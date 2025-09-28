//! Generates the `main` function for binary orb types.

use super::*;

/// generate a main function
pub fn generate_main(cgen: &mut ClifGen, ctx: &mut ClifGenContext) {
    // create the signature for int main(int argc, char *argv[], char *envp[]);
    let ptr_t = cgen.isa.pointer_type();

    let mut sig = cgen.module.make_signature();

    // push argc
    sig.params.push(AbiParam::new(types::I32));

    // push argv
    sig.params.push(AbiParam::new(ptr_t));

    // push envp
    sig.params.push(AbiParam::new(ptr_t));

    // set return type
    sig.returns.push(AbiParam::new(types::I32));

    // declare the function
    let func_id = cgen
        .module
        .declare_function("main", Linkage::Export, &sig)
        .expect("failed to create main function");

    ctx.cg.func = Function::with_name_signature(UserFuncName::user(0, func_id.as_u32()), sig);

    // create the helping struct to build the function
    let mut fb = FunctionBuilder::new(&mut ctx.cg.func, &mut ctx.fb);

    // create the entry block to start emitting code in with the function's
    // params as block params
    let entry_block = fb.create_block();
    fb.append_block_params_for_function_params(entry_block);
    fb.switch_to_block(entry_block);
    fb.seal_block(entry_block);

    let main_fun = cgen.orbtree.def("main").unwrap();
    let Some(ClifId::Func { id: main_id, .. }) = cgen.defs.get(&main_fun) else {
        // SAFETY: it's guaranteed by the semachecker.
        opt_unreachable!()
    };

    let main_fn = cgen.module.declare_func_in_func(*main_id, fb.func);
    fb.ins().call(main_fn, &[]);

    let zero = fb.ins().iconst(types::I32, 0);
    fb.ins().return_(&[zero]);

    // finalize the fundef
    fb.seal_all_blocks();
    fb.finalize();

    // write the fundef to the textrepr
    cgen.textual.write_function_no_sym(&ctx.cg.func, "main");

    cgen.module.define_function(func_id, &mut ctx.cg).unwrap();

    cgen.module.clear_context(&mut ctx.cg);
}
