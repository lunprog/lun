//! CLIF generation from SCIR

use std::collections::HashMap;

use cranelift_codegen::ir::{AbiParam, Function, InstBuilder, UserFuncName, types};
use cranelift_codegen::isa::{self, OwnedTargetIsa};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::{self as codegen};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule, ObjectProduct};

use lunc_scir::{ScItem, ScModule};
use lunc_utils::{BuildOptions, mangle, opt_unreachable, symbol};

use crate::textual::TextualClif;
use crate::translator::FunDefTranslator;

pub use cranelift_codegen::settings::OptLevel;

pub mod textual;
pub mod translator;

/// [Cranelift IR] generator from [SCIR].
///
/// [Cranelift IR]: cranelift_codegen
/// [SCIR]: lunc_scir
pub struct ClifGen {
    /// same as funbuilder_ctx but for data
    data_desc: DataDescription,
    /// the module where we are building to
    module: ObjectModule,
    /// the isa
    isa: OwnedTargetIsa,
    /// build options
    opts: BuildOptions,
    /// textual format of Clif
    textual: TextualClif,
}

/// Cranelift generator context.
pub struct ClifGenContext {
    /// used to translate multiple functions into CLIF
    fb: FunctionBuilderContext,
    /// general context of cranelift
    cg: codegen::Context,
}

impl Default for ClifGenContext {
    fn default() -> Self {
        ClifGenContext {
            fb: FunctionBuilderContext::new(),
            cg: codegen::Context::new(),
        }
    }
}

impl ClifGen {
    /// Create a new CLIF generator
    pub fn new(opts: BuildOptions, textrepr: bool, opt_level: OptLevel) -> ClifGen {
        // 1. configure the ISA-independent settings
        let mut shared_builder = settings::builder();
        // TODO: make those parameters configurable
        shared_builder.enable("is_pic").unwrap();
        let opt_level_str = format!("{opt_level}");
        shared_builder.set("opt_level", &opt_level_str).unwrap();

        let shared_flags = settings::Flags::new(shared_builder);
        debug_assert_eq!(shared_flags.opt_level(), opt_level);

        // 2. create our ISA ≃ target, and maybe configure ISA-dependant settings
        let isa_builder = isa::lookup(opts.target().clone()).unwrap();
        let isa = isa_builder.finish(shared_flags).unwrap();

        // 3. create our object module
        let objbuilder = ObjectBuilder::new(
            isa.clone(),
            opts.orb_name(),
            cranelift_module::default_libcall_names(),
        )
        .unwrap();
        let module = ObjectModule::new(objbuilder);

        ClifGen {
            data_desc: DataDescription::new(),
            module,
            isa,
            opts,
            textual: TextualClif::new(textrepr),
        }
    }

    /// Produces Cranelift IR from the [`ScModule`].
    pub fn produce(&mut self, ctx: &mut ClifGenContext, root: ScModule) {
        _ = self.data_desc;

        self.gen_module(ctx, &root);
    }

    /// Generate CLIF for a Module
    pub fn gen_module(&mut self, ctx: &mut ClifGenContext, module: &ScModule) {
        for item in &module.items {
            self.gen_item_in_module(ctx, item);
        }
    }

    /// Generate CLIF for an Item contained inside of a module
    pub fn gen_item_in_module(&mut self, ctx: &mut ClifGenContext, item: &ScItem) {
        match item {
            ScItem::GlobalDef { .. } => {
                todo!("generate global def")
            }
            // SAFETY: a global uninit or a fundecl can't be contained inside of a module
            ScItem::GlobalUninit { .. } | ScItem::FunDeclaration { .. } => opt_unreachable!(),
            ScItem::FunDefinition { .. } => {
                self.gen_fundef_in_mod(ctx, item);
            }
            ScItem::ExternBlock { .. } => {
                todo!("extern block")
            }
            ScItem::Module { module, .. } => {
                self.gen_module(ctx, module);
            }
        }
    }

    /// Generate a function definition defined in a module
    ///
    /// # Note
    ///
    /// `fundef` must be a `ScItem::FunDefinition`
    fn gen_fundef_in_mod(&mut self, ctx: &mut ClifGenContext, fundef: &ScItem) {
        let ScItem::FunDefinition { body, sym, .. } = fundef else {
            // SAFETY: it's up to the caller.
            opt_unreachable!()
        };
        self.realname(sym);

        let (arg_types, ret_type) = sym
            .typ()
            .as_fun_ptr()
            .expect("function pointer type for fundef item");

        // set the signature of the function
        let mut sig = self.module.make_signature();
        sig.call_conv = self.isa.default_call_conv();

        // maps the `which` of the arg symbol to the index of the param in the
        // Clif function
        let mut arg_map: Vec<Option<u32>> = Vec::with_capacity(arg_types.len());

        for argtyp in arg_types {
            let arg = self.type_to_fundef_arg(&argtyp);

            match arg {
                FundefArg::Zst => {
                    arg_map.push(None);
                }
                FundefArg::Param(param) => {
                    arg_map.push(Some(sig.params.len() as u32));
                    sig.params.push(param);
                }
            }
        }

        let ret_arg = self.type_to_fundef_arg(&ret_type);
        match ret_arg {
            FundefArg::Zst => {}
            FundefArg::Param(param) => sig.returns.push(param),
        }

        // create the function
        let func_id = self
            .module
            .declare_function(sym.realname().unwrap().as_str(), Linkage::Export, &sig)
            .unwrap();

        ctx.cg.func = Function::with_name_signature(UserFuncName::user(0, func_id.as_u32()), sig);

        // create the helping struct to build the function
        let mut fb = FunctionBuilder::new(&mut ctx.cg.func, &mut ctx.fb);

        // create the entry block to start emitting code in with the function's
        // params as block params
        let entry_block = fb.create_block();
        fb.append_block_params_for_function_params(entry_block);
        fb.switch_to_block(entry_block);
        fb.seal_block(entry_block);

        let mut args = vec![None; arg_map.len()];

        for (i, arg) in arg_map.iter().enumerate() {
            if let Some(arg) = *arg {
                let val = fb.block_params(entry_block)[arg as usize];
                let var = fb.declare_var(fb.func.signature.params[arg as usize].value_type);

                fb.def_var(var, val);
                args[i] = Some(var);
            }
        }

        // now translate the body
        let mut fundef_t = FunDefTranslator {
            fb,
            slots: HashMap::new(),
            args,
            cgen: self,
        };

        let ret_value = fundef_t.translate_block(body);

        // generate the implicit return of the function
        fundef_t.fb.ins().return_(ret_value.as_slice());

        // finalize the fundef
        fundef_t.fb.seal_all_blocks();
        fundef_t.fb.finalize();

        // write the fundef to the textrepr
        self.textual.write_fundef(&ctx.cg.func, sym);

        self.module.define_function(func_id, &mut ctx.cg).unwrap();

        self.module.clear_context(&mut ctx.cg);
    }

    /// Converts a SCIR type to an Abi Param
    pub fn type_to_param(&self, typ: &symbol::Type) -> AbiParam {
        use symbol::Type as SType;

        match typ {
            SType::Unknown | SType::Type | SType::Void | SType::Noreturn => unreachable!(),
            SType::I8 => AbiParam::new(types::I8).sext(),
            SType::I16 => AbiParam::new(types::I16).sext(),
            SType::I32 => AbiParam::new(types::I32).sext(),
            SType::I64 => AbiParam::new(types::I64).sext(),
            SType::I128 => AbiParam::new(types::I128).sext(),
            SType::Isz => AbiParam::new(self.isa.pointer_type()).sext(),
            SType::U8 => AbiParam::new(types::I8).uext(),
            SType::U16 => AbiParam::new(types::I16).uext(),
            SType::U32 => AbiParam::new(types::I32).uext(),
            SType::U64 => AbiParam::new(types::I64).uext(),
            SType::U128 => AbiParam::new(types::I128).uext(),
            SType::Usz => AbiParam::new(self.isa.pointer_type()).uext(),
            SType::F16 => AbiParam::new(types::F16),
            SType::F32 => AbiParam::new(types::F32),
            SType::F64 => AbiParam::new(types::F64),
            SType::F128 => AbiParam::new(types::F128),
            // NOTE: i8 is a placeholder type for noreturn and void, it is never lowered in practice
            SType::Bool => AbiParam::new(types::I8),
            SType::FunPtr { .. } | SType::Ptr { .. } => AbiParam::new(self.isa.pointer_type()),
            SType::Str => todo!("fat-pointers"),
            SType::Char => AbiParam::new(types::I32),
        }
    }

    fn type_to_fundef_arg(&self, typ: &symbol::Type) -> FundefArg {
        use symbol::Type as SType;

        match typ {
            SType::Unknown | SType::Type => unreachable!(),
            SType::Void | SType::Noreturn => FundefArg::Zst,
            _ => FundefArg::Param(self.type_to_param(typ)),
        }
    }

    /// Converts a SCIR type to a Clif type
    pub fn lower_type(&self, typ: &symbol::Type) -> types::Type {
        self.type_to_param(typ).value_type
    }

    /// Computes the realname of a symbol, and replaces `orb` with the given orb
    /// name in the build options
    pub fn realname(&self, sym: &symbol::Symbol) {
        let mut path = sym.path();

        if let Some("orb") = path.first().map(|s| s.as_str()) {
            *path.first_mut().unwrap() = String::from(self.opts.orb_name());
        }

        sym.inspect_mut(|this| this.realname = Some(mangle(&path)));
    }

    /// Returns the textual representation of the Cranelift IR
    pub fn textrepr(&self) -> String {
        self.textual.res.clone()
    }

    /// Finish the compilation to an object file
    pub fn finish_obj(self) -> ObjectProduct {
        self.module.finish()
    }
}

/// Fundef arg.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FundefArg {
    /// Zero sized type
    Zst,
    /// Regular fundef abi param
    Param(AbiParam),
}
