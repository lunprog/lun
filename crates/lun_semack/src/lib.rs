use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::iter::zip;

use ckast::{
    CkArg, CkBlock, CkElse, CkExpr, CkExpression, CkIfExpression, CkProgram, CkStatement, CkStmt,
    FromAst, MaybeUnresolved,
};
use diags::{
    ExpectedTypeFoundExpr, MismatchedTypes, NeverUsedSymbol, NotFoundInScope,
    TypeAnnotationsNeeded, UnderscoreInExpression, UnderscoreReservedIdent,
};
use lun_diag::{Diagnostic, DiagnosticSink, StageResult, ToDiagnostic, feature_todo};
use lun_parser::definition::Program;
use lun_parser::expr::UnaryOp;
use lun_utils::Span;

pub mod ckast;
pub mod diags;
pub use lun_parser::definition::Vis;

/// Semantic checker, ensure all of the lun's semantic is correct, it also
/// include type checking.
#[derive(Debug, Clone)]
pub struct SemanticCk {
    /// program to check
    program: Program,
    /// diagnostic sink, used to emit diagnostics
    sink: DiagnosticSink,
    /// symbol table of the program
    table: SymbolTable,
    /// the return type of the current function
    fun_retaty: AtomicType,
    /// location of the return type (if defined) of the current function
    fun_retaty_loc: Option<Span>,
}

impl SemanticCk {
    pub fn new(ast: Program, sink: DiagnosticSink) -> SemanticCk {
        SemanticCk {
            program: ast,
            sink,
            table: SymbolTable::new(),
            fun_retaty: AtomicType::Unknown,
            fun_retaty_loc: None,
        }
    }

    pub fn produce(&mut self) -> StageResult<CkProgram> {
        // 1. create the checked program from the unchecked program.
        let mut ckprogram = CkProgram::from_ast(self.program.clone());

        // 2. check all the defs and everything following will be checked
        match self.check_program(&mut ckprogram) {
            Ok(()) => {}
            Err(e) => {
                self.sink.push(e);
                return StageResult::Part(ckprogram, self.sink.clone());
            }
        }

        if self.sink.failed() {
            StageResult::Fail(self.sink.clone())
        } else if !self.sink.is_empty() {
            StageResult::Part(ckprogram, self.sink.clone())
        } else {
            StageResult::Good(ckprogram)
        }
    }

    pub fn check_program(&mut self, ckprogram: &mut CkProgram) -> Result<(), Diagnostic> {
        // 1. pre bind definitions

        self.table.scope_enter(); // program scope

        for def in &mut ckprogram.defs {
            let CkExpr::FunDefinition {
                args,
                rettype,
                body: _,
            } = &mut def.value.expr
            else {
                self.sink.push(feature_todo! {
                    feature: "global variables",
                    label: "global aren't yet supported, only functions in definitions",
                    loc: def.loc.clone()
                });
                continue;
            };

            let mut args_atomtype = Vec::new();
            for CkArg { typ, .. } in args {
                self.check_expr(typ)?;

                if typ.atomtyp != AtomicType::Type {
                    self.sink.push(ExpectedTypeFoundExpr {
                        loc: typ.loc.clone(),
                    });
                }

                args_atomtype.push(AtomicType::from_expr(typ.clone()));
            }

            let ret_aty = if let Some(typ) = rettype {
                self.check_expr(typ)?;
                Box::new(AtomicType::from_expr((**typ).clone()))
            } else {
                Box::new(AtomicType::Nil)
            };

            let mut ckname = def.name.clone();
            if ckname == "_" {
                self.sink.push(UnderscoreReservedIdent {
                    loc: def.name_loc.clone(),
                });
                ckname = String::from("\0");
            }

            let symbol = Symbol::global(
                AtomicType::Fun {
                    args: args_atomtype,
                    ret: ret_aty,
                },
                ckname.clone(),
                self.table.global_count(),
                // TODO: add a new loc that points to the signature
                def.loc.clone(),
            );
            def.sym = MaybeUnresolved::Resolved(symbol.clone());

            self.table.bind(ckname, symbol);
        }

        // 2. now, check the rest of the program

        for def in &mut ckprogram.defs {
            let CkExpr::FunDefinition {
                args: _,
                rettype,
                body,
            } = &mut def.value.expr
            else {
                self.sink.push(feature_todo! {
                    feature: "global variables",
                    label: "global aren't yet supported, only functions in definitions",
                    loc: def.loc.clone()
                });
                continue;
            };

            let fun_ret_atyp = def.sym.clone().unwrap().atomtyp.as_fun_ret();

            self.fun_retaty = fun_ret_atyp.clone();
            self.fun_retaty_loc = rettype.as_ref().map(|e| e.loc.clone());

            self.table.scope_enter(); // function scope

            self.check_block(body)?;

            if body.atomtyp != fun_ret_atyp {
                return Err(MismatchedTypes {
                    expected: fun_ret_atyp,
                    found: body.atomtyp.clone(),
                    due_to: rettype.as_ref().map(|e| e.loc.clone()),
                    loc: body.loc.clone(),
                }
                .into_diag());
            }

            self.table.scope_exit(&mut self.sink); // function scope
        }

        self.table.scope_exit(&mut self.sink); // program scope

        Ok(())
    }

    pub fn check_block(&mut self, block: &mut CkBlock) -> Result<(), Diagnostic> {
        // 1. check all the stmts
        for stmt in &mut block.stmts {
            match self.check_stmt(stmt) {
                Ok(()) => {}
                Err(d) => self.sink.push(d),
            }
        }

        // 2. check the last_expr if any
        if let Some(expr) = &mut block.last_expr {
            self.check_expr(expr)?;
            block.atomtyp = expr.atomtyp.clone();
        } else {
            block.atomtyp = AtomicType::Nil;
        }

        Ok(())
    }

    pub fn check_stmt(&mut self, stmt: &mut CkStatement) -> Result<(), Diagnostic> {
        match &mut stmt.stmt {
            CkStmt::VariableDef {
                name,
                name_loc,
                typ,
                value,
                sym,
            } => {
                // check the type
                if let Some(ty) = typ {
                    self.check_expr(ty)?;

                    if ty.atomtyp != AtomicType::Type {
                        self.sink.push(
                            ExpectedTypeFoundExpr {
                                loc: ty.loc.clone(),
                            }
                            .into_diag(),
                        );
                    }
                }

                let type_as_atomic = if let Some(ty) = typ {
                    Some(AtomicType::from_expr(ty.clone()))
                } else {
                    None
                };

                if let Some(value) = value {
                    // check the value
                    self.check_expr(value)?;

                    if let Some(ref typ_as_aty) = type_as_atomic {
                        if &value.atomtyp != typ_as_aty {
                            self.sink.push(MismatchedTypes {
                                expected: typ_as_aty.clone(),
                                found: value.atomtyp.clone(),
                                due_to: typ.as_ref().map(|e| e.loc.clone()),
                                loc: value.loc.clone(),
                            })
                        }
                    }
                } else {
                    // TODO: implement variable initialization checking
                    self.sink.push(
                        feature_todo!{
                            feature: "variable initialization",
                            label: "for now every variable must be initialized because the check for uninitialized variable is not implemented",
                            loc: stmt.loc.clone()
                        }
                    )
                }

                let atomtyp = if let Some(ref typ_as_aty) = type_as_atomic {
                    typ_as_aty.clone()
                } else if let Some(value) = value {
                    value.atomtyp.clone()
                } else {
                    AtomicType::Unknown
                };

                // define the symbol because we didn't do it before
                let mut ckname = name.clone();
                if name == "_" {
                    self.sink.push(UnderscoreReservedIdent {
                        loc: name_loc.clone(),
                    });
                    ckname = String::from("\0");
                }

                let symbol = Symbol::var(
                    atomtyp,
                    ckname.clone(),
                    self.table.var_count(),
                    stmt.loc.clone(),
                );

                *sym = MaybeUnresolved::Resolved(symbol.clone());
                self.table.bind(ckname, symbol)
            }
            CkStmt::Expression(expr) => {
                self.check_expr(expr)?;
            }
        }
        Ok(())
    }

    pub fn check_expr(&mut self, expr: &mut CkExpression) -> Result<(), Diagnostic> {
        match &mut expr.expr {
            CkExpr::IntLit(_) => {
                // TODO(URGENT): create a `comptime_int` that can coerce to
                // any integer type both iNN and uNN, and one for floats also
                // `comptime_float`, and `comptime_number` who is a superset of
                // both comptime_int and comptime_float, but a literal can't
                // have this type.
                expr.atomtyp = AtomicType::I64;
            }
            CkExpr::BoolLit(_) => {
                expr.atomtyp = AtomicType::Bool;
            }
            CkExpr::StringLit(_) => {
                expr.atomtyp = AtomicType::Str;
            }
            CkExpr::Grouping(e) => {
                self.check_expr(e)?;
                expr.atomtyp = e.atomtyp.clone();
            }
            CkExpr::Ident(MaybeUnresolved::Unresolved(name)) => {
                let Some(sym) = self.table.lookup(&*name, true) else {
                    return Err(NotFoundInScope {
                        name: name.clone(),
                        loc: expr.loc.clone(),
                    }
                    .into_diag());
                };

                if sym.name == "_" {
                    return Err(UnderscoreInExpression {
                        loc: expr.loc.clone(),
                    }
                    .into_diag());
                }
                if sym.atomtyp == AtomicType::Unknown {
                    self.sink.push(TypeAnnotationsNeeded {
                        loc: sym.loc.clone(),
                    })
                }
                expr.atomtyp = sym.atomtyp.clone();
                expr.expr = CkExpr::Ident(MaybeUnresolved::Resolved(sym.clone()));
            }
            CkExpr::Ident(MaybeUnresolved::Resolved(_)) => {
                unreachable!("i think it's a bug not sure tho")
            }
            CkExpr::Binary { lhs, op, rhs } => {
                self.check_expr(lhs)?;
                self.check_expr(rhs)?;

                if lhs.atomtyp != rhs.atomtyp {
                    self.sink.push(MismatchedTypes {
                        expected: lhs.atomtyp.clone(),
                        found: rhs.atomtyp.clone(),
                        due_to: None,
                        loc: rhs.loc.clone(),
                    });
                }

                expr.atomtyp = if op.is_relational() | op.is_logical() {
                    AtomicType::Bool
                } else {
                    lhs.atomtyp.clone()
                };
            }
            CkExpr::Unary { op, expr: exp } => match op {
                UnaryOp::Negation => {
                    if !exp.atomtyp.is_integer() || !exp.atomtyp.is_float() {
                        self.sink.push(MismatchedTypes {
                            // TODO(URGENT): FIXME, tell somehow that we
                            // expected an integer or float here, tell
                            // with `comptime_int`, `comptime_float`,
                            // `comptime_number`
                            expected: AtomicType::Unknown,
                            found: exp.atomtyp.clone(),
                            due_to: None,
                            loc: exp.loc.clone(),
                        })
                    }
                    expr.atomtyp = exp.atomtyp.clone();
                }
                UnaryOp::Not => {
                    if exp.atomtyp != AtomicType::Bool {
                        self.sink.push(MismatchedTypes {
                            expected: AtomicType::Bool,
                            found: exp.atomtyp.clone(),
                            due_to: None,
                            loc: exp.loc.clone(),
                        });
                    }
                    expr.atomtyp = AtomicType::Bool;
                }
            },
            CkExpr::FunCall { called, args } => {
                self.check_expr(called)?;

                let AtomicType::Fun {
                    args: args_aty,
                    ret: ret_ty,
                } = &called.atomtyp
                else {
                    return Err(ExpectedTypeFoundExpr {
                        loc: called.loc.clone(),
                    }
                    .into_diag());
                };

                assert!(called.atomtyp.is_func());

                for (val, aty) in zip(args, args_aty) {
                    self.check_expr(val)?;

                    if &val.atomtyp != aty {
                        self.sink.push(MismatchedTypes {
                            expected: aty.clone(),
                            found: val.atomtyp.clone(),
                            due_to: None,
                            loc: val.loc.clone(),
                        })
                    }
                }

                expr.atomtyp = *ret_ty.clone();
            }
            CkExpr::FunDefinition { .. } => {
                return Err(feature_todo! {
                    feature: "function closure",
                    label: "closures are not yet supported, you can only define functions",
                    loc: expr.loc.clone()
                }
                .into_diag());
            }
            CkExpr::If(ifexpr) => {
                self.check_ifexpr(ifexpr)?;
                expr.atomtyp = ifexpr.atomtyp.clone();
            }
            CkExpr::IfThenElse {
                cond,
                true_val,
                false_val,
            } => {
                // 1. condition
                self.check_expr(cond)?;

                if cond.atomtyp != AtomicType::Bool {
                    self.sink.push(MismatchedTypes {
                        expected: AtomicType::Bool,
                        found: cond.atomtyp.clone(),
                        due_to: None,
                        loc: cond.loc.clone(),
                    });
                }

                // 2. true value
                self.check_expr(true_val)?;

                // 3. set the atomtyp to the type of true_val
                expr.atomtyp = true_val.atomtyp.clone();

                // 4. false value
                self.check_expr(false_val)?;

                if false_val.atomtyp != expr.atomtyp {
                    self.sink.push(MismatchedTypes {
                        expected: expr.atomtyp.clone(),
                        found: false_val.atomtyp.clone(),
                        due_to: None,
                        loc: false_val.loc.clone(),
                    });
                }
            }
            CkExpr::Block(block) => {
                self.check_block(block)?;
                expr.atomtyp = block.atomtyp.clone();
            }
            CkExpr::While { cond, body } => {
                // 1. condition
                self.check_expr(cond)?;

                if cond.atomtyp != AtomicType::Bool {
                    self.sink.push(MismatchedTypes {
                        expected: AtomicType::Bool,
                        found: cond.atomtyp.clone(),
                        due_to: None,
                        loc: cond.loc.clone(),
                    });
                }

                // 2. body
                self.check_block(body)?;
                expr.atomtyp = body.atomtyp.clone();
            }
            CkExpr::For { .. } => {
                // TODO: implement for loops

                self.sink.push(feature_todo! {
                    feature: "for loop",
                    label: "iterators are not implemented so..",
                    loc: expr.loc.clone(),
                });

                expr.atomtyp = AtomicType::Nil;
            }
            CkExpr::Return { val } => {
                expr.atomtyp = AtomicType::Noreturn;

                if let Some(val) = val {
                    self.check_expr(val)?;

                    if val.atomtyp != self.fun_retaty {
                        self.sink.push(MismatchedTypes {
                            expected: self.fun_retaty.clone(),
                            found: val.atomtyp.clone(),
                            due_to: self.fun_retaty_loc.clone(),
                            loc: val.loc.clone(),
                        });
                    }
                }
            }
            CkExpr::Break { val } => {
                // TODO: check that the val has the same type as its loop / block
                expr.atomtyp = AtomicType::Noreturn;

                if let Some(val) = val {
                    self.check_expr(val)?;
                }
            }
            CkExpr::Continue => {
                expr.atomtyp = AtomicType::Noreturn;
            }
            CkExpr::Nil => {
                expr.atomtyp = AtomicType::Nil;
            }
        }

        debug_assert_ne!(expr.atomtyp, AtomicType::Unknown);
        Ok(())
    }

    pub fn check_ifexpr(&mut self, ifexpr: &mut CkIfExpression) -> Result<(), Diagnostic> {
        // 1. condition
        self.check_expr(&mut ifexpr.cond)?;

        if ifexpr.cond.atomtyp != AtomicType::Bool {
            self.sink.push(MismatchedTypes {
                expected: AtomicType::Bool,
                found: ifexpr.cond.atomtyp.clone(),
                due_to: None,
                loc: ifexpr.cond.loc.clone(),
            });
        }

        // 2. body

        self.table.scope_enter(); // body scope

        self.check_block(&mut ifexpr.body)?;
        ifexpr.atomtyp = ifexpr.body.atomtyp.clone();

        self.table.scope_exit(&mut self.sink); // body scope

        // 3. else

        if let Some(r#else) = &mut ifexpr.else_branch {
            self.check_else(r#else)?;

            if r#else.atomic_type() != &ifexpr.atomtyp {
                self.sink.push(MismatchedTypes {
                    expected: ifexpr.atomtyp.clone(),
                    found: r#else.atomic_type().clone(),
                    due_to: None,
                    loc: ifexpr.cond.loc.clone(),
                });
            }
        }

        Ok(())
    }

    pub fn check_else(&mut self, r#else: &mut CkElse) -> Result<(), Diagnostic> {
        match r#else {
            CkElse::IfExpr(ifexpr) => self.check_ifexpr(ifexpr),
            CkElse::Block(block) => self.check_block(block),
        }
    }
}

/// Symbol
#[derive(Debug, Clone)]
pub struct Symbol {
    /// local, parameter or global
    pub kind: SymKind,
    /// actual type of the
    pub atomtyp: AtomicType,
    /// the name of the symbol
    pub name: String,
    /// which scope the symbol is referring to
    pub which: usize,
    /// location of the definition of the symbol, must point to at least the
    /// identifier and can point to more: the identifier and the type ...
    pub loc: Span,
    /// count of how many times this symbol is used
    pub uses: usize,
}

impl Symbol {
    /// Create a new symbol
    pub fn new(
        kind: SymKind,
        atomtyp: AtomicType,
        name: String,
        which: usize,
        loc: Span,
    ) -> Symbol {
        Symbol {
            kind,
            atomtyp,
            name,
            which,
            loc,
            uses: 0,
        }
    }

    /// Create a new local symbol
    pub fn var(atomtyp: AtomicType, name: String, which: usize, loc: Span) -> Symbol {
        Symbol {
            kind: SymKind::Var,
            atomtyp,
            name,
            which,
            loc,
            uses: 0,
        }
    }

    /// Create a new param symbol
    pub fn arg(atomtyp: AtomicType, name: String, which: usize, loc: Span) -> Symbol {
        Symbol {
            kind: SymKind::Arg,
            atomtyp,
            name,
            which,
            loc,
            uses: 0,
        }
    }

    /// Create a new global symbol
    pub fn global(atomtyp: AtomicType, name: String, which: usize, loc: Span) -> Symbol {
        Symbol {
            kind: SymKind::Global,
            atomtyp,
            name,
            which,
            loc,
            uses: 0,
        }
    }

    pub fn kind(mut self, kind: SymKind) -> Symbol {
        self.kind = kind;
        self
    }

    pub fn atomtyp(mut self, atomtyp: AtomicType) -> Symbol {
        self.atomtyp = atomtyp;
        self
    }

    pub fn name(mut self, name: String) -> Symbol {
        self.name = name;
        self
    }

    pub fn which(mut self, which: usize) -> Symbol {
        self.which = which;
        self
    }
}

/// Symbol type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymKind {
    /// Variable
    Var,
    /// Argument
    Arg,
    /// Global
    Global,
}

impl Display for SymKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymKind::Var => f.write_str("variable"),
            SymKind::Arg => f.write_str("argument"),
            SymKind::Global => f.write_str("global"),
        }
    }
}

/// An atomic type is the real underlying type of a Checked Expression,
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum AtomicType {
    /// Unknown, at the end of type checking this type is an error.
    #[default]
    Unknown,
    /// 8 bit signed integer
    I8,
    /// 16 bit signed integer
    I16,
    /// 32 bit signed integer
    I32,
    /// 64 bit signed integer
    ///
    /// NOTE: the exprtype `int` is an alias of `i64` exprtype
    I64,
    /// Alias of `i64`
    Int,
    /// 8 bit unsigned integer
    U8,
    /// 16 bit unsigned integer
    U16,
    /// 32 bit unsigned integer
    U32,
    /// 64 bit unsigned integer
    ///
    /// NOTE: the exprtype `uint` is an alias of `u64` exprtype
    U64,
    /// Alias of `u64`
    UInt,
    /// 32 bit floating point number, compliant with IEEE 754-2008
    F32,
    /// 16 bit floating point number, compliant with IEEE 754-2008
    F16,
    /// 64 bit floating point number, compliant with IEEE 754-2008
    F64,
    /// equivalent of Rust's `bool`, always one byte long. Can only contain
    /// `true` -> 1 and `false` -> 0
    Bool,
    // TODO: implement strings
    /// a string, nothing for now, we can't use them
    Str,
    /// a nil value, just the `nil` literal or nothing, its the base return
    /// type of a function that returns nothing
    Nil,
    /// a function type, can only be constructed from a function definition.
    Fun {
        /// types of the arguments
        args: Vec<AtomicType>,
        /// the return type
        ret: Box<AtomicType>,
    },
    /// Type, in the Type System.
    ///
    /// Because lun have types that are expression, types get typed checked as
    /// well. So (for example) the identifier `int` will be evaluated in EVERY
    /// expression to be of type `type`.
    Type,
    /// Noreturn, the type that return, break and continue expressions evaluate
    /// to.
    ///
    /// It indicates that the control flow will halts after evaluating the
    /// expression.
    Noreturn,
}

impl AtomicType {
    // TODO: add more atomic types, u8, u16, u32, u64, u128, i8, i16,
    // i32, i64, i128, f16, f32, f64, f128
    pub const ATOMIC_TYPES: [&str; 4] = ["int", "float", "bool", "string"];

    pub const PRIMARY_ATOMTYPE_PAIRS: &[(&str, AtomicType)] = &[
        ("int", AtomicType::Int),
        ("i64", AtomicType::I64),
        ("i32", AtomicType::I32),
        ("i16", AtomicType::I16),
        ("i8", AtomicType::I8),
        ("uint", AtomicType::UInt),
        ("u64", AtomicType::U64),
        ("u32", AtomicType::U32),
        ("u16", AtomicType::U16),
        ("u8", AtomicType::U8),
        ("f16", AtomicType::F16),
        ("f32", AtomicType::F32),
        ("f64", AtomicType::F64),
        ("bool", AtomicType::Bool),
        ("str", AtomicType::Str),
        ("noreturn", AtomicType::Noreturn),
    ];

    /// returns true if the type is a function
    pub const fn is_func(&self) -> bool {
        matches!(self, AtomicType::Fun { .. })
    }

    /// Converts a type expression to a type.
    pub fn from_expr(expr: CkExpression) -> AtomicType {
        // TODO(URGENT): make this function return diagnostics instead of panicking
        let CkExpr::Ident(MaybeUnresolved::Resolved(Symbol { name, .. })) = expr.expr else {
            unreachable!("the type should just be a symbol")
        };

        for (tyname, ty) in AtomicType::PRIMARY_ATOMTYPE_PAIRS {
            if *tyname == name {
                return ty.clone();
            }
        }

        unreachable!(
            "the type was in the SymbolTable but couldn't be converted to a\
            real type"
        )
    }

    /// Interpret the type as a Fun and return the return type
    #[track_caller]
    pub fn as_fun_ret(&self) -> AtomicType {
        match self {
            Self::Fun { ret, .. } => (**ret).clone(),
            _ => panic!("{self:?} is not a function type"),
        }
    }

    /// Interpret the type as a Fun and return the arguments types
    #[track_caller]
    pub fn as_fun_args(&self) -> Vec<AtomicType> {
        match self {
            Self::Fun { args, .. } => args.clone(),
            _ => panic!("{self:?} is not a function type"),
        }
    }

    /// Returns true if self is an integer type, so `iNN` or `uNN`
    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            Self::I8
                | Self::I16
                | Self::I32
                | Self::I64
                | Self::U8
                | Self::U16
                | Self::U32
                | Self::U64
        )
    }

    /// Returns true if self is a float type, so `f16`, `f32` or `f64`
    pub fn is_float(&self) -> bool {
        matches!(self, Self::F16 | Self::F32 | Self::F64)
    }
}

impl Display for AtomicType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicType::Unknown => f.write_str("unknown"),
            AtomicType::I64 => f.write_str("i64"),
            AtomicType::I32 => f.write_str("i32"),
            AtomicType::I16 => f.write_str("i16"),
            AtomicType::I8 => f.write_str("i8"),
            AtomicType::Int => f.write_str("int"),
            AtomicType::U64 => f.write_str("u64"),
            AtomicType::U32 => f.write_str("u32"),
            AtomicType::U16 => f.write_str("u16"),
            AtomicType::U8 => f.write_str("u8"),
            AtomicType::UInt => f.write_str("uint"),
            AtomicType::F16 => f.write_str("f16"),
            AtomicType::F32 => f.write_str("f32"),
            AtomicType::F64 => f.write_str("f64"),
            AtomicType::Bool => f.write_str("bool"),
            AtomicType::Str => f.write_str("string"),
            AtomicType::Nil => f.write_str("nil"),
            // TODO: implement a proper display for function type, like `fun(int, f16) -> bool`
            AtomicType::Fun { .. } => f.write_str("fun"),
            AtomicType::Type => f.write_str("type"),
            AtomicType::Noreturn => f.write_str("noreturn"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SymbolMap {
    map: HashMap<String, Symbol>,
    global_count: usize,
    var_count: usize,
    arg_count: usize,
}

impl SymbolMap {
    pub fn new() -> SymbolMap {
        SymbolMap {
            map: HashMap::new(),
            global_count: 0,
            var_count: 0,
            arg_count: 0,
        }
    }

    pub fn first_scope() -> SymbolMap {
        SymbolMap {
            map: HashMap::from([
                (
                    "int".to_string(),
                    Symbol::global(AtomicType::Type, "int".to_string(), 0, Span::ZERO),
                ),
                (
                    "i64".to_string(),
                    Symbol::global(AtomicType::Type, "i64".to_string(), 0, Span::ZERO),
                ),
                (
                    "i32".to_string(),
                    Symbol::global(AtomicType::Type, "i32".to_string(), 0, Span::ZERO),
                ),
                (
                    "i16".to_string(),
                    Symbol::global(AtomicType::Type, "i16".to_string(), 0, Span::ZERO),
                ),
                (
                    "i8".to_string(),
                    Symbol::global(AtomicType::Type, "i8".to_string(), 0, Span::ZERO),
                ),
                (
                    "uint".to_string(),
                    Symbol::global(AtomicType::Type, "uint".to_string(), 0, Span::ZERO),
                ),
                (
                    "u64".to_string(),
                    Symbol::global(AtomicType::Type, "u64".to_string(), 0, Span::ZERO),
                ),
                (
                    "u32".to_string(),
                    Symbol::global(AtomicType::Type, "u32".to_string(), 0, Span::ZERO),
                ),
                (
                    "u16".to_string(),
                    Symbol::global(AtomicType::Type, "u16".to_string(), 0, Span::ZERO),
                ),
                (
                    "u8".to_string(),
                    Symbol::global(AtomicType::Type, "u8".to_string(), 0, Span::ZERO),
                ),
                (
                    "f16".to_string(),
                    Symbol::global(AtomicType::Type, "f16".to_string(), 0, Span::ZERO),
                ),
                (
                    "f32".to_string(),
                    Symbol::global(AtomicType::Type, "f32".to_string(), 0, Span::ZERO),
                ),
                (
                    "f64".to_string(),
                    Symbol::global(AtomicType::Type, "f64".to_string(), 0, Span::ZERO),
                ),
                (
                    "bool".to_string(),
                    Symbol::global(AtomicType::Type, "bool".to_string(), 0, Span::ZERO),
                ),
                (
                    "str".to_string(),
                    Symbol::global(AtomicType::Type, "str".to_string(), 0, Span::ZERO),
                ),
                (
                    "noreturn".to_string(),
                    Symbol::global(AtomicType::Type, "noreturn".to_string(), 0, Span::ZERO),
                ),
                (
                    "_".to_string(),
                    Symbol::global(AtomicType::Unknown, "_".to_string(), 0, Span::ZERO),
                ),
            ]),
            global_count: 5,
            var_count: 0,
            arg_count: 0,
        }
    }
}

/// Symbol table.
///
/// The symbol table is a stack of hash maps. Each hashmap maps a name to a
/// symbol, the global scope is at level 0 and each scope we go deeper the
/// level increases by one.
#[derive(Clone)]
pub struct SymbolTable {
    /// all the tables, the first table is the always the global scope and as
    /// we go deeper in scopes we push new tables
    tabs: Vec<SymbolMap>,
}

impl SymbolTable {
    /// Create a new Symbol Table, with the global scope.
    pub fn new() -> SymbolTable {
        // TODO: load with atomic types like int, float etc etc
        SymbolTable {
            tabs: vec![SymbolMap::first_scope()],
        }
    }

    fn last_map(&self) -> &SymbolMap {
        // we can unwrap because we know there is at least the global scope.
        self.tabs.last().unwrap()
    }

    fn last_map_mut(&mut self) -> &mut SymbolMap {
        // we can unwrap because we know there is at least the global scope.
        self.tabs.last_mut().unwrap()
    }

    /// Enter a new scope
    pub fn scope_enter(&mut self) {
        self.tabs.push(SymbolMap::new())
    }

    /// Enter a new scope
    pub fn scope_exit(&mut self, sink: &mut DiagnosticSink) {
        assert_ne!(self.tabs.len(), 1, "can't exit out of the global scope");

        for sym in self.last_map().map.values() {
            // type annotation needed the type is unknown
            if sym.atomtyp == AtomicType::Unknown {
                sink.push(TypeAnnotationsNeeded {
                    loc: sym.loc.clone(),
                })
            }

            // unused symbol check
            if sym.kind != SymKind::Global && sym.uses == 0 {
                // the symbol isn't global and isn't used so we push a warning
                sink.push(NeverUsedSymbol {
                    kind: sym.kind.clone(),
                    name: sym.name.clone(),
                    loc: sym.loc.clone(),
                })
            }
        }

        self.tabs.pop();
    }

    /// Bind a name to a symbol in the current scope, will panick if name == `_`
    pub fn bind(&mut self, name: String, sym: Symbol) {
        assert_ne!(name.as_str(), "_", "`_` is a reserved identifier");
        match sym.kind {
            SymKind::Var => {
                self.last_map_mut().var_count += 1;
            }
            SymKind::Arg => {
                self.last_map_mut().arg_count += 1;
            }
            SymKind::Global => {
                self.last_map_mut().global_count += 1;
            }
        }
        self.last_map_mut().map.insert(name, sym);
    }

    /// Return the current scope level
    pub fn level(&self) -> usize {
        self.tabs.len() - 1
    }

    /// Lookup for the symbol in the current scope, returns None if there is no
    /// symbol with this name in the current scope
    pub fn lookup_current(&self, name: impl AsRef<str>) -> Option<&Symbol> {
        self.last_map().map.get(name.as_ref())
    }

    /// Lookup for a symbol with the given name, starting at the current scope
    /// ending at the global scope, returns None if there is no symbol in any
    /// scopes
    pub fn lookup(&mut self, name: impl AsRef<str>, used: bool) -> Option<&Symbol> {
        let name = name.as_ref();
        for i in (0..=self.level()).rev() {
            if let res @ Some(_) = self.tabs[i].map.get_mut(name) {
                if used {
                    if let Some(val) = res {
                        val.uses += 1;
                    }
                }
                return self.tabs[i].map.get(name);
            }
        }
        None
    }

    /// Edit a symbol in the scope `which` with the name `name`, will panick if
    /// the scope or the symbol doesn't exist
    pub fn edit(&mut self, which: usize, name: impl AsRef<str>, new_symbol: Symbol) {
        *self.tabs[which].map.get_mut(name.as_ref()).unwrap() = new_symbol;
    }

    /// Returns the Var count of the last symbol map
    pub fn var_count(&self) -> usize {
        self.last_map().var_count
    }

    /// Returns the Arg count of the last symbol map
    pub fn arg_count(&self) -> usize {
        self.last_map().arg_count
    }

    /// Returns the Global count of the last symbol map
    pub fn global_count(&self) -> usize {
        self.last_map().global_count
    }
}

impl Debug for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.tabs.iter().enumerate()).finish()
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        SymbolTable::new()
    }
}
