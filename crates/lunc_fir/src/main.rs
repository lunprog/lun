// NOTE: THIS IS TEMPORARY, JUST FOR THE TIME OF THE DEVELOPMENT OF LUNC_FIR.

use lunc_fir::{
    Arg, ConstValue, FcType, FirUnit, FunDecl, FunDef, Glob, IntCC, Reg,
    builder::{FundefBuilder, InstBuilder},
};
use lunc_utils::pretty::PrettyDump;

fn main() {
    let mut unit = FirUnit::new();

    let mut main_fun = FunDef::new("main");
    main_fun.append_arg(FcType::I32);
    main_fun.append_arg(FcType::ptr(FcType::ptr(FcType::I8)));
    main_fun.set_ret(FcType::I32);
    main_fun.finish_sig();

    let fun = unit.append_fundef(main_fun);

    // function declarations
    let getchar = unit.append_fundecl(FunDecl::new("getchar", [], FcType::I32));
    let puts = unit.append_fundecl(FunDecl::new("puts", [FcType::ptr(FcType::I8)], FcType::I32));

    let printf_c = unit.append_fundecl(FunDecl::new(
        "printf",
        [FcType::ptr(FcType::I8), FcType::I8],
        FcType::I32,
    ));

    // globals
    let yes_string = unit.append_glob(Glob::string_const("yes_string", "You said 'y'!\n\0"));
    let else_string = unit.append_glob(Glob::string_const(
        "else_string",
        "Instead you said '%c'.\n\0",
    ));

    let mut builder = FundefBuilder::new(fun.clone());

    // create the entry point
    let entry = builder.create_entry().label();
    let then = builder.create_bb([]).label();
    let r#else = builder.create_bb([FcType::I32]).label();

    // build entry bb
    builder.switch_bb(entry);
    let mut inst = builder.inst();
    inst.call(Reg::new(3), FcType::I32, Arg::fun(getchar), []);

    inst.br_icmp(
        IntCC::Eq,
        Arg::Constant(ConstValue::I8(121)),
        Arg::Reg(Reg::new(3)),
        then,
        [],
        r#else,
        [Arg::Reg(Reg::new(3))],
    );

    builder.bblock().finish();

    // build then bb
    builder.switch_bb(then);
    inst = builder.inst();
    inst.call(
        Reg::new(1),
        FcType::I32,
        Arg::fun(puts),
        [Arg::Glob(yes_string)],
    );
    inst.ret(FcType::I32, Arg::Constant(ConstValue::I32(0)));
    builder.bblock().finish();

    // build else bb
    builder.switch_bb(r#else);
    inst = builder.inst();
    inst.call(
        Reg::new(2),
        FcType::I32,
        Arg::fun(printf_c),
        [Arg::Glob(else_string), Arg::Reg(Reg::new(1))],
    );
    inst.ret(FcType::I32, Arg::Constant(ConstValue::I32(1)));
    builder.bblock().finish();

    unit.dump();
}
