// NOTE: THIS IS TEMPORARY, JUST FOR THE TIME OF THE DEVELOPMENT OF LUNC_FIR.

use std::num::NonZeroU32;

use lunc_fir::{
    Arg, BasicBlock, BbLabel, ConstValue, FcType, FirUnit, FunDef, Glob, Inst, Reg, Terminator,
    builder::FundefBuilder,
};
use lunc_utils::pretty::PrettyDump;

pub fn old(unit: &mut FirUnit) {
    unit.append_glob(Glob::new(
        "MyGlobal".to_string(),
        FcType::I8,
        0,
        false,
        ConstValue::I8(69),
    ));

    unit.append_glob(Glob::new(
        "hello_world".to_string(),
        FcType::I8,
        0,
        false,
        ConstValue::string(b"Hello, world!"),
    ));

    let mut entry = BasicBlock::new(BbLabel::new(0));

    entry.append_inst(Inst::Call {
        res: Reg::new(3),
        ty: FcType::I8,
        fnptr: Arg::Symbol(Box::from(b"something" as &[u8])),
        args: vec![
            Arg::Constant(ConstValue::Bool(true)),
            Arg::Symbol(Box::from(b"MyGlobal" as &[u8])),
        ],
    });
    entry.append_inst(Inst::Add {
        res: Reg::new(4),
        ty: FcType::I8,
        lhs: Arg::Constant(ConstValue::I8(34)),
        rhs: Arg::Constant(ConstValue::I8(35)),
    });

    entry.append_inst(Inst::Salloc {
        res: Reg::new(69),
        ty: FcType::U8,
        num_elems: Some(12),
        alignment: NonZeroU32::new(1).unwrap(),
    });

    entry.append_inst(Inst::Store {
        ty: FcType::U8,
        val: Arg::Constant(ConstValue::U8(69)),
        pointer: Arg::Reg(Reg::new(69)),
    });

    entry.set_terminator(Terminator::Ret {
        ty: FcType::I32,
        val: Some(Arg::Constant(ConstValue::I32(0))),
    });

    entry.finish();

    unit.append_fun(FunDef::with_args_ret_bbs(
        "main".to_string(),
        vec![FcType::I32, FcType::ptr(FcType::ptr(FcType::I8))],
        FcType::I32,
        vec![entry],
    ));
}

fn main() {
    let mut unit = FirUnit::new();

    let mut main_fun = FunDef::new("main");
    main_fun.append_arg(FcType::I32);
    main_fun.append_arg(FcType::ptr(FcType::ptr(FcType::I8)));
    main_fun.set_ret(FcType::I32);
    main_fun.finish_sig();

    let fun = unit.append_fun(main_fun);

    let mut builder = FundefBuilder::new(fun);
    builder.create_bb();
    // builder.create_bb(); // FIXME: doesn't work because of lifetimes, SO, use `idtype`s.

    unit.dump();
}
