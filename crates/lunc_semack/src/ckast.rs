//! Checked AST.

use std::fmt;

pub use lunc_parser::expr::{BinOp, UnaryOp};
use lunc_parser::{
    expr::{Arg, Else, Expr, Expression, IfExpression},
    item::Item,
    stmt::{Block, Statement, Stmt},
};

use super::*;

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
/// [`Program`]: lunc_parser::definition::Program
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
/// [`Definition`]: lunc_parser::definition::Definition
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
    type Unchecked = Item;

    fn from_ast(ast: Self::Unchecked) -> Self {
        match ast {
            Item::GlobalConst {
                name,
                name_loc,
                typ,
                value,
                loc,
            } => CkDefinition {
                vis: Vis::Public,
                name: name.clone(),
                name_loc,
                typ: from_ast(typ),
                value: from_ast(value),
                loc,
                sym: MaybeUnresolved::Unresolved(name),
            },
            _ => todo!(),
        }
    }
}

/// Checked block see [`Block`].
///
/// [`Block`]: lunc_parser::stmt::Block
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
/// [`Statement`]: lunc_parser::stmt::Statement
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
                mutable,
                typ,
                value,
            } => CkStmt::VariableDef {
                name: name.clone(),
                name_loc,
                mutable,
                typ: from_ast(typ),
                value: from_ast(*value),
                sym: MaybeUnresolved::Unresolved(name),
            },
            Stmt::Expression(expr) => CkStmt::Expression(from_ast(expr)),
            _ => todo!(),
        };

        CkStatement { stmt, loc: ast.loc }
    }
}

/// see [`Stmt`].
///
/// [`Stmt`]: lunc_parser::stmt::Stmt
#[derive(Debug, Clone)]
pub enum CkStmt {
    /// see [`VariableDef`]
    ///
    /// [`VariableDef`]: lunc_parser::stmt::Stmt::VariableDef
    VariableDef {
        name: String,
        name_loc: Span,
        mutable: bool,
        typ: Option<CkExpression>,
        value: Box<CkExpression>,
        /// the symbol representing this function
        sym: MaybeUnresolved,
    },
    /// see [`Expression`]
    ///
    /// [`Expression`]: lunc_parser::stmt::Stmt::Expression
    Expression(CkExpression),
}

/// see [`Arg`]
///
/// [`Arg`]: lunc_parser::expr::Arg
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
/// [`Expression`]: lunc_parser::expr::Expression
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
                val: from_ast(*expr),
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
            Expr::If(ifexpr) => ckexpr_from_if_expr(ifexpr),
            Expr::IfThenElse {
                cond,
                true_val,
                false_val,
            } => CkExpr::If {
                cond: from_ast(*cond),
                then_branch: from_ast(*true_val),
                else_branch: Some(from_ast(*false_val)),
            },
            Expr::Block(block) => CkExpr::Block(from_ast(block)),
            Expr::PredicateLoop { cond, body } => CkExpr::While {
                cond: from_ast(*cond),
                body: from_ast(body),
                index: None,
            },
            Expr::IteratorLoop {
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
                index: None,
            },
            Expr::Continue => CkExpr::Continue { index: None },
            Expr::Null => CkExpr::Null,
            Expr::PointerType { mutable, typ } => CkExpr::PointerType {
                mutable,
                typ: from_ast(*typ),
            },
            Expr::AddressOf { mutable, val } => CkExpr::Deref {
                mutable,
                val: from_ast(*val),
            },
            _ => todo!(),
        };

        CkExpression {
            expr,
            atomtyp: AtomicType::Unknown,
            loc: ast.loc,
        }
    }
}

impl Display for CkExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.expr, f)
    }
}

pub fn ckexpr_from_if_expr(ifexpr: IfExpression) -> CkExpr {
    CkExpr::If {
        cond: from_ast(*ifexpr.cond),
        then_branch: Box::new(CkExpression {
            loc: ifexpr.loc.clone(),
            expr: CkExpr::Block(from_ast(*ifexpr.body)),
            atomtyp: AtomicType::Unknown,
        }),
        else_branch: {
            match ifexpr.else_branch.map(|e| *e) {
                Some(Else::IfExpr(ifexpr)) => Some(Box::new(CkExpression {
                    loc: ifexpr.loc.clone(),
                    expr: ckexpr_from_if_expr(ifexpr),
                    atomtyp: AtomicType::Unknown,
                })),
                Some(Else::Block(block)) => Some(Box::new(CkExpression {
                    loc: block.loc.clone(),
                    expr: CkExpr::Block(from_ast(block)),
                    atomtyp: AtomicType::Unknown,
                })),
                None => None,
            }
        },
    }
}

impl Display for CkExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CkExpr::IntLit(i) => write!(f, "{i}")?,
            CkExpr::BoolLit(bool) => write!(f, "{bool}")?,
            CkExpr::StringLit(str) => write!(f, "{str:?}")?,
            CkExpr::Grouping(expr) => write!(f, "({expr})")?,
            CkExpr::Ident(MaybeUnresolved::Unresolved(name)) => write!(f, "{name}")?,
            CkExpr::Ident(MaybeUnresolved::Resolved(symref)) => {
                let sym = symref.read().unwrap();

                write!(f, "{}", sym.name)?;
            }
            CkExpr::Binary { lhs, op, rhs } => write!(f, "{lhs} {op} {rhs}")?,
            CkExpr::Unary { op, val } => write!(f, "{op}{val}")?,
            CkExpr::FunCall { called, args } => {
                write!(f, "{called}(")?;
                if !args.is_empty() {
                    for arg in &args[..args.len() - 1] {
                        write!(f, "{arg}, ")?;
                    }
                    write!(f, "{})", args.last().unwrap())?;
                }
            }
            CkExpr::PointerType { mutable, typ } => {
                write!(f, "*")?;
                if *mutable {
                    write!(f, "mut ")?;
                }
                write!(f, "{typ}")?;
            }
            exp => write!(f, "<{exp:?}>")?,
        };
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum CkExpr {
    /// see [`IntLit`]
    ///
    /// [`IntLit`]: lunc_parser::expr::Expr::IntLit
    IntLit(u128),
    /// see [`BoolLit`]
    ///
    /// [`BoolLit`]: lunc_parser::expr::Expr::BoolLit
    BoolLit(bool),
    /// see [`StringLit`]
    ///
    /// [`StringLit`]: lunc_parser::expr::Expr::StringLit
    StringLit(String),
    /// see [`Grouping`]
    ///
    /// [`Grouping`]: lunc_parser::expr::Expr::Grouping
    Grouping(Box<CkExpression>),
    /// see [`Ident`]
    ///
    /// [`Ident`]: lunc_parser::expr::Expr::Ident
    Ident(MaybeUnresolved),
    /// see [`Binary`]
    ///
    /// [`Binary`]: lunc_parser::expr::Expr::Binary
    Binary {
        lhs: Box<CkExpression>,
        op: BinOp,
        rhs: Box<CkExpression>,
    },
    /// see [`Unary`]
    ///
    /// [`Unary`]: lunc_parser::expr::Expr::Unary
    Unary { op: UnaryOp, val: Box<CkExpression> },
    /// see [`FunCall`]
    ///
    /// [`FunCall`]: lunc_parser::expr::Expr::FunCall
    FunCall {
        called: Box<CkExpression>,
        args: Vec<CkExpression>,
    },
    /// see [`FunDefinition`]
    ///
    /// [`FunDefinition`]: lunc_parser::expr::Expr::FunDefinition
    FunDefinition {
        args: Vec<CkArg>,
        rettype: Option<Box<CkExpression>>,
        body: CkBlock,
    },
    /// see [`If`] and [`IfThenElse`]
    ///
    /// [`If`]: lunc_parser::expr::Expr::If
    /// [`IfThenElse`]: lunc_parser::expr::Expr::IfThenElse
    If {
        cond: Box<CkExpression>,
        then_branch: Box<CkExpression>,
        else_branch: Option<Box<CkExpression>>,
    },
    /// see [`Block`]
    ///
    /// [`Block`]: lunc_parser::expr::Expr::Block
    Block(CkBlock),
    /// see [`While`]
    ///
    /// [`While`]: lunc_parser::expr::Expr::While
    While {
        cond: Box<CkExpression>,
        body: CkBlock,
        /// index of the loop after checking
        index: Option<usize>,
    },
    /// see [`For`]
    ///
    /// [`For`]: lunc_parser::expr::Expr::For
    For {
        /// the variable that holds the value of the iterator
        variable: String,
        iterator: Box<CkExpression>,
        body: CkBlock,
    },
    /// see [`Return`]
    ///
    /// [`Return`]: lunc_parser::expr::Expr::Return
    Return { val: Option<Box<CkExpression>> },
    /// see [`Break`]
    ///
    /// [`Break`]: lunc_parser::expr::Expr::Break
    Break {
        val: Option<Box<CkExpression>>,
        /// loop index
        index: Option<usize>,
    },
    /// see [`Continue`]
    ///
    /// [`Continue`]: lunc_parser::expr::Expr::Continue
    Continue {
        /// loop index
        index: Option<usize>,
    },
    /// see [`Null`]
    ///
    /// [`Null`]: lunc_parser::expr::Expr::Null
    Null,
    /// see [`PointerType`]
    ///
    /// [`PointerType`]: lunc_parser::expr::Expr::PointerType
    PointerType {
        mutable: bool,
        typ: Box<CkExpression>,
    },
    /// see [`Deref`]
    ///
    /// [`Deref`]: lunc_parser::expr::Expr::Deref
    Deref {
        mutable: bool,
        val: Box<CkExpression>,
    },
}

/// a symbol that may be resolved or not yet
#[derive(Debug, Clone)]
pub enum MaybeUnresolved {
    Unresolved(String),
    Resolved(SymbolRef),
}

impl MaybeUnresolved {
    pub fn unwrap(&self) -> SymbolRef {
        match self {
            MaybeUnresolved::Unresolved(_) => panic!("Called `unwrap` on an Unresolved."),
            MaybeUnresolved::Resolved(s) => s.clone(),
        }
    }
}
