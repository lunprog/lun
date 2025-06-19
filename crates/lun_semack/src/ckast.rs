//! Checked AST.

use lun_parser::{
    definition::Definition,
    expr::{Arg, Else, Expr, Expression, IfExpression},
    stmt::{Block, Statement, Stmt},
};

use super::*;

pub use lun_parser::expr::{BinOp, UnaryOp};

/// Convert AST to a checked AST, but not yet checked
pub trait FromAst: Sized {
    type Unchecked;

    fn from_ast(ast: Self::Unchecked) -> Self;
}

impl<T> FromAst for Option<T>
where
    T: FromAst,
{
    type Unchecked = Option<T::Unchecked>;

    fn from_ast(ast: Self::Unchecked) -> Self {
        ast.map(from_ast)
    }
}

impl<T> FromAst for Vec<T>
where
    T: FromAst,
{
    type Unchecked = Vec<T::Unchecked>;

    fn from_ast(ast: Self::Unchecked) -> Self {
        let mut list = Vec::new();

        for item in ast {
            list.push(T::from_ast(item));
        }

        list
    }
}

impl<T> FromAst for Box<T>
where
    T: FromAst,
{
    type Unchecked = T::Unchecked;

    fn from_ast(ast: Self::Unchecked) -> Self {
        Box::new(from_ast(ast))
    }
}

pub fn from_ast<T: FromAst>(ast: T::Unchecked) -> T {
    T::from_ast(ast)
}

/// Checked Lun Program see [`Program`]
///
/// [`Program`]: lun_parser::definition::Program
#[derive(Debug, Clone)]
pub struct CkProgram {
    pub defs: Vec<CkDefinition>,
}

impl FromAst for CkProgram {
    type Unchecked = Program;

    fn from_ast(ast: Self::Unchecked) -> Self {
        CkProgram {
            defs: from_ast(ast.defs),
        }
    }
}

/// Checked Lun Definition see [`Definition`]
///
/// [`Definition`]: lun_parser::definition::Definition
#[derive(Debug, Clone)]
pub struct CkDefinition {
    pub vis: Vis,
    pub name: String,
    pub name_loc: Span,
    pub typ: Option<CkExpression>,
    pub value: CkExpression,
    pub loc: Span,
    /// the symbol representing this definition
    pub sym: MaybeUnresolved,
}

impl FromAst for CkDefinition {
    type Unchecked = Definition;

    fn from_ast(ast: Self::Unchecked) -> Self {
        CkDefinition {
            vis: ast.vis,
            name: ast.name.clone(),
            name_loc: ast.name_loc,
            typ: from_ast(ast.typ),
            value: from_ast(ast.value),
            loc: ast.loc,
            sym: MaybeUnresolved::Unresolved(ast.name),
        }
    }
}

/// Checked block see [`Block`].
///
/// [`Block`]: lun_parser::stmt::Block
#[derive(Debug, Clone)]
pub struct CkBlock {
    pub stmts: Vec<CkStatement>,
    pub last_expr: Option<Box<CkExpression>>,
    pub loc: Span,
    pub atomtyp: AtomicType,
}

impl FromAst for CkBlock {
    type Unchecked = Block;

    fn from_ast(ast: Self::Unchecked) -> Self {
        CkBlock {
            stmts: from_ast(ast.stmts),
            last_expr: from_ast(ast.last_expr.map(|a| *a)),
            loc: ast.loc,
            atomtyp: AtomicType::Unknown,
        }
    }
}

/// Checked statement see [`Statement`].
///
/// [`Statement`]: lun_parser::stmt::Statement
#[derive(Debug, Clone)]
pub struct CkStatement {
    pub stmt: CkStmt,
    pub loc: Span,
}

impl FromAst for CkStatement {
    type Unchecked = Statement;

    fn from_ast(ast: Self::Unchecked) -> Self {
        let stmt = match ast.stmt {
            Stmt::VariableDef {
                name,
                name_loc,
                typ,
                value,
            } => CkStmt::VariableDef {
                name: name.clone(),
                name_loc,
                typ: from_ast(typ),
                value: from_ast(value),
                sym: MaybeUnresolved::Unresolved(name),
            },
            Stmt::Expression(expr) => CkStmt::Expression(from_ast(expr)),
        };

        CkStatement { stmt, loc: ast.loc }
    }
}

/// see [`Stmt`].
///
/// [`Stmt`]: lun_parser::stmt::Stmt
#[derive(Debug, Clone)]
pub enum CkStmt {
    /// see [`VariableDef`]
    ///
    /// [`VariableDef`]: lun_parser::stmt::Stmt::VariableDef
    VariableDef {
        name: String,
        name_loc: Span,
        typ: Option<CkExpression>,
        value: Option<CkExpression>,
        /// the symbol representing this function
        sym: MaybeUnresolved,
    },
    /// see [`Expression`]
    ///
    /// [`Expression`]: lun_parser::stmt::Stmt::Expression
    Expression(CkExpression),
}

/// see [`Arg`]
///
/// [`Arg`]: lun_parser::expr::Arg
#[derive(Debug, Clone)]
pub struct CkArg {
    pub name: String,
    pub name_loc: Span,
    pub typ: CkExpression,
    pub loc: Span,
}

impl FromAst for CkArg {
    type Unchecked = Arg;

    fn from_ast(ast: Self::Unchecked) -> Self {
        CkArg {
            name: ast.name,
            name_loc: ast.name_loc,
            typ: from_ast(ast.typ),
            loc: ast.loc,
        }
    }
}

/// Checked expression, see [`Expression`] to understand.
///
/// [`Expression`]: lun_parser::expr::Expression
#[derive(Debug, Clone)]
pub struct CkExpression {
    /// the checked expression
    pub expr: CkExpr,
    /// the actual type of the expression
    pub atomtyp: AtomicType,
    /// the location of the expression
    pub loc: Span,
}

impl FromAst for CkExpression {
    type Unchecked = Expression;

    fn from_ast(ast: Self::Unchecked) -> Self {
        let expr = match ast.expr {
            Expr::IntLit(i) => CkExpr::IntLit(i),
            Expr::BoolLit(b) => CkExpr::BoolLit(b),
            Expr::StringLit(s) => CkExpr::StringLit(s),
            Expr::Grouping(expr) => CkExpr::Grouping(from_ast(*expr)),
            Expr::Ident(id) => CkExpr::Ident(MaybeUnresolved::Unresolved(id)),
            Expr::Binary { lhs, op, rhs } => CkExpr::Binary {
                lhs: from_ast(*lhs),
                op,
                rhs: from_ast(*rhs),
            },
            Expr::Unary { op, expr } => CkExpr::Unary {
                op,
                expr: from_ast(*expr),
            },
            Expr::FunCall { called, args } => CkExpr::FunCall {
                called: from_ast(*called),
                args: from_ast(args),
            },
            Expr::FunDefinition {
                args,
                rettype,
                body,
            } => CkExpr::FunDefinition {
                args: from_ast(args),
                rettype: from_ast(rettype.map(|a| *a)),
                body: from_ast(body),
            },
            Expr::If(ifexpr) => CkExpr::If(from_ast(ifexpr)),
            Expr::IfThenElse {
                cond,
                true_val,
                false_val,
            } => CkExpr::IfThenElse {
                cond: from_ast(*cond),
                true_val: from_ast(*true_val),
                false_val: from_ast(*false_val),
            },
            Expr::Block(block) => CkExpr::Block(from_ast(block)),
            Expr::While { cond, body } => CkExpr::While {
                cond: from_ast(*cond),
                body: from_ast(body),
            },
            Expr::For {
                variable,
                iterator,
                body,
            } => CkExpr::For {
                variable,
                iterator: from_ast(*iterator),
                body: from_ast(body),
            },
            Expr::Return { val } => CkExpr::Return {
                val: from_ast(val.map(|a| *a)),
            },
            Expr::Break { val } => CkExpr::Break {
                val: from_ast(val.map(|a| *a)),
            },
            Expr::Continue => CkExpr::Continue,
            Expr::Nil => CkExpr::Nil,
        };

        CkExpression {
            expr,
            atomtyp: AtomicType::Unknown,
            loc: ast.loc,
        }
    }
}

#[derive(Debug, Clone)]
pub enum CkExpr {
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
    Grouping(Box<CkExpression>),
    /// see [`Ident`]
    ///
    /// [`Ident`]: lun_parser::expr::Expr::Ident
    Ident(MaybeUnresolved),
    /// see [`Binary`]
    ///
    /// [`Binary`]: lun_parser::expr::Expr::Binary
    Binary {
        lhs: Box<CkExpression>,
        op: BinOp,
        rhs: Box<CkExpression>,
    },
    /// see [`Unary`]
    ///
    /// [`Unary`]: lun_parser::expr::Expr::Unary
    Unary {
        op: UnaryOp,
        expr: Box<CkExpression>,
    },
    /// see [`FunCall`]
    ///
    /// [`FunCall`]: lun_parser::expr::Expr::FunCall
    FunCall {
        called: Box<CkExpression>,
        args: Vec<CkExpression>,
    },
    /// see [`FunDefinition`]
    ///
    /// [`FunDefinition`]: lun_parser::expr::Expr::FunDefinition
    FunDefinition {
        args: Vec<CkArg>,
        rettype: Option<Box<CkExpression>>,
        body: CkBlock,
    },
    /// see [`If`]
    ///
    /// [`If`]: lun_parser::expr::Expr::If
    If(CkIfExpression),
    /// see [`IfThenElse`]
    ///
    /// [`IfThenElse`]: lun_parser::expr::Expr::IfThenElse
    IfThenElse {
        cond: Box<CkExpression>,
        true_val: Box<CkExpression>,
        false_val: Box<CkExpression>,
    },
    /// see [`Block`]
    ///
    /// [`Block`]: lun_parser::expr::Expr::Block
    Block(CkBlock),
    /// see [`While`]
    ///
    /// [`While`]: lun_parser::expr::Expr::While
    While {
        cond: Box<CkExpression>,
        body: CkBlock,
    },
    /// see [`For`]
    ///
    /// [`For`]: lun_parser::expr::Expr::For
    For {
        /// the variable that holds the value of the iterator
        variable: String,
        iterator: Box<CkExpression>,
        body: CkBlock,
    },
    /// see [`Return`]
    ///
    /// [`Return`]: lun_parser::expr::Expr::Return
    Return { val: Option<Box<CkExpression>> },
    /// see [`Break`]
    ///
    /// [`Break`]: lun_parser::expr::Expr::Break
    Break { val: Option<Box<CkExpression>> },
    /// see [`Continue`]
    ///
    /// [`Continue`]: lun_parser::expr::Expr::Continue
    Continue,
    /// see [`Nil`]
    ///
    /// [`Nil`]: lun_parser::expr::Expr::Nil
    Nil,
}

#[derive(Debug, Clone)]
pub struct CkIfExpression {
    pub cond: Box<CkExpression>,
    pub body: Box<CkBlock>,
    pub else_branch: Option<Box<CkElse>>,
    pub loc: Span,
    pub atomtyp: AtomicType,
}

impl FromAst for CkIfExpression {
    type Unchecked = IfExpression;

    fn from_ast(ast: Self::Unchecked) -> Self {
        CkIfExpression {
            cond: from_ast(*ast.cond),
            body: from_ast(*ast.body),
            else_branch: from_ast(ast.else_branch.map(|a| *a)),
            loc: ast.loc,
            atomtyp: AtomicType::Unknown,
        }
    }
}

#[derive(Debug, Clone)]
pub enum CkElse {
    IfExpr(CkIfExpression),
    Block(CkBlock),
}

impl CkElse {
    pub fn atomic_type(&self) -> &AtomicType {
        match self {
            Self::IfExpr(ifexpr) => &ifexpr.atomtyp,
            Self::Block(block) => &block.atomtyp,
        }
    }

    pub fn loc(&self) -> &Span {
        match self {
            Self::IfExpr(ifexpr) => &ifexpr.loc,
            Self::Block(block) => &block.loc,
        }
    }
}

impl FromAst for CkElse {
    type Unchecked = Else;

    fn from_ast(ast: Self::Unchecked) -> Self {
        match ast {
            Else::IfExpr(ifexpr) => CkElse::IfExpr(from_ast(ifexpr)),
            Else::Block(block) => CkElse::Block(from_ast(block)),
        }
    }
}

/// a symbol that may be resolved or not yet
#[derive(Debug, Clone)]
pub enum MaybeUnresolved {
    Unresolved(String),
    Resolved(Symbol),
}

impl MaybeUnresolved {
    pub fn unwrap(self) -> Symbol {
        match self {
            MaybeUnresolved::Unresolved(_) => panic!("Called `unwrap` on an Unresolved."),
            MaybeUnresolved::Resolved(s) => s,
        }
    }
}
