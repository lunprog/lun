//! Checked AST.

use lun_parser::{
    expr::{Arg, Expr, Expression},
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

/// Checked chunk
/// see [`Chunk`].
///
/// [`Chunk`]: lun_parser::stmt::Chunk
#[derive(Debug, Clone)]
pub struct CkBlock {
    pub stmts: Vec<CkStatement>,
    pub loc: Span,
}

impl FromAst for CkBlock {
    type Unchecked = Block;

    fn from_ast(chunk: Self::Unchecked) -> Self {
        CkBlock {
            stmts: from_ast(chunk.stmts),
            loc: chunk.loc,
        }
    }
}

/// Checked statement
/// see [`Statement`].
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
/// [`Arg`]: lun_parser::stmt::Arg
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
    pub typ: Type,
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
            Expr::FunDefinition { .. }
            | Expr::If(..)
            | Expr::IfThenElse { .. }
            | Expr::Block(_)
            | Expr::While { .. } => {
                todo!("TODO(URGENT): implement me")
            }
        };

        CkExpression {
            expr,
            typ: Type::Unknown,
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
