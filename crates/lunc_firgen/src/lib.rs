//! FIR generation from SCIR.

use std::mem;

use lunc_fir::{
    ConstValue, FcType, FirUnit, FunDecl, FunDef, Glob,
    builder::{FundefBuilder, InstBuilder},
};
use lunc_scir::{Abi, ScBlock, ScItem, ScModule};
use lunc_utils::{
    BuildOptions, opt_unreachable,
    symbol::{EffectivePath, Symbol, Type, ValueExpr},
    target::PtrWidth,
};

/// Mangles an effective path into a realname.
///
/// An effective path `std.mem.transmute` is mangled like so:
///
/// ## 1. The prefix `_L`
///
/// We append a prefix to the result, it's always `_L` and the `L` is for `Lun`.
///
/// result = `_L`
///
/// ## 2. For each member
///
/// We append the length of a member in decimal form is taking and the member
/// like so
///
/// ### For `std`
///
/// result = `_L3std`
///
/// ### For `mem`
///
/// result = `_L3std3mem`
///
/// ### For `transmute`
///
/// result = `_L3std3mem9transmute`
///
/// ### If we had another long member, like `hello_world_im_so_long`
///
/// we just append `22hello_world_im_so_long` to the result.
///
/// ## 3. Finished
///
/// This is super simple mangling.
pub fn mangle(path: &EffectivePath) -> String {
    let mut result = String::from("_L");

    for member in path.members() {
        let mangled = format!("{}{member}", member.len());

        result.push_str(&mangled);
    }

    result
}

/// The [FIR] Generator from [SCIR].
///
/// [FIR]: lunc_fir
/// [SCIR]: lunc_scir
#[derive(Debug, Clone)]
pub struct FirGen {
    unit: FirUnit,
    opts: BuildOptions,
}

impl FirGen {
    /// Create a new Fir Generator
    pub fn new(opts: BuildOptions) -> FirGen {
        FirGen {
            unit: FirUnit::new(),
            opts,
        }
    }

    /// Produces a [`FirUnit`] from the [`ScModule`].
    pub fn produce(&mut self, root: ScModule) -> FirUnit {
        _ = root;

        self.gen_module(&root);

        mem::replace(&mut self.unit, FirUnit::new())
    }

    pub fn gen_module(&mut self, module: &ScModule) {
        for item in &module.items {
            self.gen_item(item);
        }
    }

    /// Generate FIR for an Item contained inside of a module
    pub fn gen_item(&mut self, item: &ScItem) {
        match item {
            ScItem::GlobalDef { mutable, sym, .. } => {
                self.realname(sym);

                self.unit.append_glob(Glob::new_def(
                    sym.realname().unwrap(),
                    self.lower_type(&sym.typ()),
                    !mutable,
                    self.lower_value_expr(sym.value().expect("should be computed in SCIR")),
                ));
            }
            // SAFETY: a global uninit or a fundecl can't be contained inside of a module
            ScItem::GlobalUninit { .. } | ScItem::FunDeclaration { .. } => opt_unreachable!(),
            ScItem::FunDefinition { body, sym, .. } => {
                self.realname(sym);
                let mut fundef = FunDef::new(sym.realname().unwrap());

                let (args, ret) = sym
                    .typ()
                    .as_fun_ptr()
                    .expect("function pointer type for item function declaration");

                fundef.append_args(args.iter().map(|arg| self.lower_type(arg)));
                fundef.set_ret(self.lower_type(&ret));
                fundef.finish_sig();

                let mut builder = FundefBuilder::new(fundef.clone());

                builder.create_entry();

                if !body.is_empty() {
                    self.gen_block(body, builder);
                } else {
                    let mut inst = builder.inst();
                    inst.ret(FcType::Void, None);
                }

                self.unit.append_fundef(fundef);
            }
            ScItem::ExternBlock { .. } => self.gen_extern_blk(item),
            ScItem::Module { module, .. } => {
                self.gen_module(module);
            }
        }
    }

    /// Generate FIR for an Extern Block
    ///
    /// # Safety
    ///
    /// `blk` **MUST** be a [`ScItem::ExternBlock`]
    pub fn gen_extern_blk(&mut self, blk: &ScItem) {
        let ScItem::ExternBlock { abi, items, loc: _ } = blk else {
            // SAFETY: bruh the caller said it was an extern block
            opt_unreachable!()
        };

        if *abi != Abi::C {
            todo!("unsupported abi {abi:?}");
        }

        for item in items {
            match item {
                ScItem::FunDeclaration {
                    name: _,
                    name_loc: _,
                    typexpr: _,
                    args: _,
                    rettypexpr: _,
                    defined_mut: _,
                    loc: _,
                    sym,
                } => {
                    let (args, ret) = sym
                        .typ()
                        .as_fun_ptr()
                        .expect("function pointer type for item function declaration");

                    let args: Vec<_> = args.iter().map(|arg| self.lower_type(arg)).collect();
                    let ret = self.lower_type(&ret);

                    self.unit
                        .append_fundecl(FunDecl::new(sym.name(), args, ret));
                }
                ScItem::GlobalUninit {
                    name: _,
                    name_loc: _,
                    typexpr: _,
                    loc: _,
                    sym,
                } => {
                    self.unit.append_glob(Glob::new_decl(
                        sym.name(),
                        self.lower_type(&sym.typ()),
                        false,
                    ));
                }
                // SAFETY: extern block is guaranteed after scir checking to
                // only contain fundecl and global uninit.
                _ => opt_unreachable!(),
            }
        }
    }

    /// Generate FIR for a block, inside of a function
    ///
    /// ## Note
    ///
    /// This function does not create a bb.
    pub fn gen_block(&self, block: &ScBlock, builder: FundefBuilder) {
        _ = builder;

        for stmt in &block.stmts {
            _ = stmt;
            // gen stmt.
        }

        if let Some(last_expr) = &block.last_expr {
            _ = last_expr;
            // gen expr.
        }
    }

    /// Computes the realname of a symbol, and replaces `orb` with the given orb name in the build options
    pub fn realname(&self, sym: &Symbol) {
        let mut path = sym.path();

        if let Some("orb") = path.first().map(|s| s.as_str()) {
            *path.first_mut().unwrap() = String::from(self.opts.orb_name());
        }

        sym.inspect_mut(|this| this.realname = Some(mangle(&path)));
    }

    pub fn lower_type(&self, typ: &Type) -> FcType {
        match typ {
            Type::Unknown => unreachable!(),
            Type::I8 => FcType::S8,
            Type::I16 => FcType::S16,
            Type::I32 => FcType::S32,
            Type::I64 => FcType::S64,
            Type::I128 => FcType::S128,
            Type::Isz => match self.opts.target().ptr_width() {
                PtrWidth::Ptr16 => FcType::S16,
                PtrWidth::Ptr32 => FcType::S32,
                PtrWidth::Ptr64 => FcType::S64,
            },
            Type::U8 => FcType::U8,
            Type::U16 => FcType::U16,
            Type::U32 => FcType::U32,
            Type::U64 => FcType::U64,
            Type::U128 => FcType::U128,
            Type::Usz => match self.opts.target().ptr_width() {
                PtrWidth::Ptr16 => FcType::U16,
                PtrWidth::Ptr32 => FcType::U32,
                PtrWidth::Ptr64 => FcType::U64,
            },
            Type::F32 => FcType::F32,
            Type::F64 => FcType::F64,
            Type::F16 | Type::F128 => todo!("f16 and f128 lowering to fir"),
            Type::Bool => FcType::Bool,
            Type::Void => FcType::Void,
            Type::FunPtr { args, ret } => FcType::FunPtr {
                args: args.iter().map(|arg| self.lower_type(arg)).collect(),
                ret: Box::new(self.lower_type(ret)),
            },
            Type::Ptr { mutable: _, typ } => FcType::Ptr {
                ty: Box::new(self.lower_type(typ)),
            },
            Type::Noreturn => FcType::Void,
            Type::Str => todo!("fat-pointers"),
            Type::Char => FcType::U32,
            Type::Type => unreachable!(),
        }
    }

    pub fn lower_value_expr(&self, value: ValueExpr) -> ConstValue {
        match value {
            ValueExpr::Boolean(val) => ConstValue::Bool(val),
            ValueExpr::I8(val) => ConstValue::S8(val),
            ValueExpr::I16(val) => ConstValue::S16(val),
            ValueExpr::I32(val) => ConstValue::S32(val),
            ValueExpr::I64(val) => ConstValue::S64(val),
            ValueExpr::I128(val) => ConstValue::S128(val),
            ValueExpr::U8(val) => ConstValue::U8(val),
            ValueExpr::U16(val) => ConstValue::U16(val),
            ValueExpr::U32(val) => ConstValue::U32(val),
            ValueExpr::U64(val) => ConstValue::U64(val),
            ValueExpr::U128(val) => ConstValue::U128(val),
            ValueExpr::Str(val) => ConstValue::String(Box::from(val.as_bytes())),
            ValueExpr::Char(val) => ConstValue::U32(val as u32),
            ValueExpr::F32(val) => ConstValue::F32(val),
            ValueExpr::F64(val) => ConstValue::F64(val),
            ValueExpr::Void => unreachable!(),
            ValueExpr::Type(_) => unreachable!(),
        }
    }
}
