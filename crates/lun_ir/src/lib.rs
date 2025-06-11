use lun_semack::{
    Symbol, Type, Vis,
    ckast::{
        BinOp, CkChunk, CkElseIf, CkExpr, CkExpression, CkStatement, CkStmt, MaybeUnresolved,
        UnaryOp,
    },
};

/// Convert Checked AST to a simpler Intermidiate Representation
pub trait IntoIr: Sized {
    type Ir;

    fn into_ir(self) -> Self::Ir;
}

impl<T: IntoIr> IntoIr for Vec<T> {
    type Ir = Vec<T::Ir>;

    fn into_ir(self) -> Self::Ir {
        let mut vec = vec![];

        for item in self {
            vec.push(item.into_ir());
        }

        vec
    }
}

impl<T: IntoIr> IntoIr for Option<T> {
    type Ir = Option<T::Ir>;

    fn into_ir(self) -> Self::Ir {
        self.map(IntoIr::into_ir)
    }
}

/// A lun module is a translation unit of Lun.
#[derive(Debug, Clone)]
pub struct IrModule {
    pub defs: Vec<IrDefinition>,
}

impl IrModule {
    pub fn from_ck_chunk(ckast: CkChunk) -> IrModule {
        let mut module = IrModule { defs: Vec::new() };
        let mut start_fn_body = IrChunk { stmts: Vec::new() };

        for stmt in ckast.stmts {
            match stmt.stmt {
                CkStmt::FunDef {
                    vis,
                    name,
                    name_loc: _,
                    args: _,
                    rettype: _,
                    body,
                    sym: MaybeUnresolved::Resolved(sym),
                } => module.defs.push(IrDefinition::FunDef {
                    vis,
                    name,
                    args: sym.typ.as_fun_args(),
                    rettype: sym.typ.as_fun_ret(),
                    body: body.into_ir(),
                }),
                CkStmt::FunDef {
                    sym: MaybeUnresolved::Unresolved(_),
                    ..
                } => unreachable!(),
                _ => {
                    start_fn_body.stmts.push(stmt.into_ir());
                }
            }
        }

        module.defs.push(IrDefinition::FunDef {
            vis: Vis::Private,
            name: "$start".to_string(),
            args: Vec::new(),
            rettype: Type::Nil,
            body: start_fn_body,
        });

        module
    }
}

#[derive(Debug, Clone)]
pub enum IrDefinition {
    FunDef {
        vis: Vis,
        name: String,
        args: Vec<Type>,
        rettype: Type,
        body: IrChunk,
    },
}

#[derive(Debug, Clone)]
pub struct IrChunk {
    pub stmts: Vec<IrStatement>,
}

impl IntoIr for CkChunk {
    type Ir = IrChunk;

    fn into_ir(self) -> Self::Ir {
        IrChunk {
            stmts: self.stmts.into_ir(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum IrStatement {
    Assignement {
        variable: Symbol,
        value: IrExpression,
    },
    VariableDef {
        name: String,
        typ: Type,
        value: Option<IrExpression>,
    },
    IfThenElse {
        cond: IrExpression,
        body: IrChunk,
        else_ifs: Vec<IrElseIf>,
        else_body: Option<IrChunk>,
    },
    DoBlock {
        body: IrChunk,
    },
    FunCall {
        name: Symbol,
        args: Vec<IrExpression>,
    },
    Return {
        val: Option<IrExpression>,
    },
    Break {
        val: Option<IrExpression>,
    },
}

impl IntoIr for CkStatement {
    type Ir = IrStatement;

    fn into_ir(self) -> Self::Ir {
        match self.stmt {
            CkStmt::Assignement { variable, value } => IrStatement::Assignement {
                variable: variable.unwrap(),
                value: value.into_ir(),
            },
            CkStmt::VariableDef {
                vis: _,
                name,
                name_loc: _,
                typ: _,
                value,
                sym,
            } => IrStatement::VariableDef {
                name,
                typ: sym.unwrap().typ,
                value: value.into_ir(),
            },
            CkStmt::IfThenElse {
                cond,
                body,
                else_ifs,
                else_body,
            } => IrStatement::IfThenElse {
                cond: cond.into_ir(),
                body: body.into_ir(),
                else_ifs: else_ifs.into_ir(),
                else_body: else_body.into_ir(),
            },
            CkStmt::DoBlock { body } => IrStatement::DoBlock {
                body: body.into_ir(),
            },
            CkStmt::FunCall { name, args } => IrStatement::FunCall {
                name: name.unwrap(),
                args: args.into_ir(),
            },
            // TODO: implement loops
            CkStmt::While { .. } | CkStmt::For { .. } => todo!("IMPLEMENT LOOPS"),
            CkStmt::Return { val } => IrStatement::Return { val: val.into_ir() },
            CkStmt::Break { val } => IrStatement::Break { val: val.into_ir() },
            CkStmt::FunDef { .. } => todo!("NESTED FUNCTIONS AREN'T YET ALLOWED"), // TODO: support nested functions
        }
    }
}

#[derive(Debug, Clone)]
pub struct IrElseIf {
    pub cond: IrExpression,
    pub body: IrChunk,
}

impl IntoIr for CkElseIf {
    type Ir = IrElseIf;

    fn into_ir(self) -> Self::Ir {
        IrElseIf {
            cond: self.cond.into_ir(),
            body: self.body.into_ir(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum IrExpression {
    /// see [`IntLit`]
    ///
    /// [`IntLit`]: lun_parser::expr::Expr::IntLit
    IntLit(u64),
    /// see [`BoolLit`]
    ///
    /// [`BoolLit`]: lun_parser::expr::Expr::BoolLit
    BoolLit(bool),
    /// see [`StringLit`]
    ///
    /// [`StringLit`]: lun_parser::expr::Expr::StringLit
    StringLit(String),
    /// see [`Grouping`]
    ///
    /// [`Grouping`]: lun_parser::expr::Expr::Grouping
    Grouping(Box<IrExpression>),
    /// see [`Ident`]
    ///
    /// [`Ident`]: lun_parser::expr::Expr::Ident
    Ident(Symbol),
    /// see [`Binary`]
    ///
    /// [`Binary`]: lun_parser::expr::Expr::Binary
    Binary {
        lhs: Box<IrExpression>,
        op: BinOp,
        rhs: Box<IrExpression>,
    },
    /// see [`Unary`]
    ///
    /// [`Unary`]: lun_parser::expr::Expr::Unary
    Unary {
        op: UnaryOp,
        expr: Box<IrExpression>,
    },
    /// see [`FunCall`]
    ///
    /// [`FunCall`]: lun_parser::expr::Expr::FunCall
    FunCall {
        called: Box<IrExpression>,
        args: Vec<IrExpression>,
    },
}

impl IntoIr for CkExpression {
    type Ir = IrExpression;

    fn into_ir(self) -> Self::Ir {
        match self.expr {
            CkExpr::IntLit(i) => IrExpression::IntLit(i),
            CkExpr::BoolLit(b) => IrExpression::BoolLit(b),
            CkExpr::StringLit(s) => IrExpression::StringLit(s),
            CkExpr::Grouping(e) => e.into_ir(),
            CkExpr::Ident(sym) => IrExpression::Ident(sym.unwrap()),
            CkExpr::Binary { lhs, op, rhs } => IrExpression::Binary {
                lhs: Box::new(lhs.into_ir()),
                op,
                rhs: Box::new(rhs.into_ir()),
            },
            CkExpr::Unary { op, expr } => IrExpression::Unary {
                op,
                expr: Box::new(expr.into_ir()),
            },
            CkExpr::FunCall { called, args } => IrExpression::FunCall {
                called: Box::new(called.into_ir()),
                args: args.into_ir(),
            },
        }
    }
}
