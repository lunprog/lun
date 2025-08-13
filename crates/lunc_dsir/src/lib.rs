//! Desugared Intermediate Representation of Lun.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/logo/logo_no_bg_black.png"
)]

use std::{collections::HashMap, fmt::Debug, fs, path::PathBuf};

use diags::{
    ModuleFileDoesnotExist, NameDefinedMultipleTimes, NotFoundInScope, UnderscoreInExpression,
    UnderscoreReservedIdent,
};
use lunc_diag::{Diagnostic, DiagnosticSink, FileId, ToDiagnostic};
use lunc_lexer::Lexer;
use lunc_parser::{
    Parser,
    directive::Directive,
    expr::{Arg, Else, Expr, Expression, IfExpression},
    item::{Item, Module},
    stmt::{Block, Statement, Stmt},
};
use lunc_utils::{
    FromHigher, Span, lower, opt_unrecheable,
    symbol::{EffectivePath, LazySymbol, SymKind, Symbol, Type, Typeness},
};

pub use lunc_parser::{
    directive::QualifiedPath,
    expr::{BinOp, UnaryOp},
    item::Abi,
};

pub mod diags;
pub mod pretty;

/// Optional span, used because when we desugar we are creating new nodes, so
/// there is no location for them.
///
/// # Note:
///
/// It's fine to unwrap because if we need to get the loc of a node it's to emit
/// a diagnostic and the desugaring should never make errors.
pub type OSpan = Option<lunc_utils::Span>;

/// A desugared module, see the sweet version [`Module`]
///
/// [`Module`]: lunc_parser::item::Module
#[derive(Debug, Clone)]
pub struct DsModule {
    pub items: Vec<DsItem>,
    pub fid: FileId,
}

impl FromHigher for DsModule {
    type Higher = Module;

    fn lower(node: Self::Higher) -> Self {
        let Module { items, fid } = node;

        DsModule {
            items: lower(items),
            fid,
        }
    }
}

/// A desugared item, see the sweet version [`Item`]
///
/// [`Item`]: lunc_parser::item::Item
#[derive(Debug, Clone)]
pub enum DsItem {
    /// Both [`GlobalConst`] and [`GlobalVar`]
    ///
    /// [`GlobalVar`]: lunc_parser::item::Item::GlobalVar
    /// [`GlobalConst`]: lunc_parser::item::Item::GlobalConst
    GlobalDef {
        name: String,
        name_loc: OSpan,
        mutable: bool,
        typexpr: Option<DsExpression>,
        value: Box<DsExpression>,
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: LazySymbol,
    },
    /// A [`Mod`], with its items inlined inside this member, constructed from
    /// the dsir directive `Mod` by the Desugarrer
    ///
    /// [`Mod`]: lunc_parser::directive::Directive::Mod
    Module {
        /// the name of the module when declared
        name: String,
        /// the items of the module
        module: DsModule,
        /// location of the directive that defined this module.
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: LazySymbol,
    },
    /// See [`Item::ExternBlock`]
    ///
    /// [`Item::ExternBlock`]: lunc_parser::item::Item::ExternBlock
    ExternBlock {
        abi: Abi,
        items: Vec<DsItem>,
        loc: OSpan,
    },
    /// See [`Item::Directive`]
    ///
    /// [`Item::Directive`]: lunc_parser::item::Item::Directive
    Directive(DsDirective),
}

/// See [`ItemDirective`]
///
/// [`ItemDirective`]: lunc_parser::directive::Directive
#[derive(Debug, Clone)]
pub enum DsDirective {
    Import {
        path: QualifiedPath,
        alias: Option<String>,
        loc: OSpan,
    },
    /// NOTE: This directive will not be here after we pass the lowered DSIR to the desugarrer
    Mod { name: String, loc: OSpan },
}

impl FromHigher for DsDirective {
    type Higher = Directive;

    fn lower(node: Self::Higher) -> Self {
        match node {
            Directive::Mod { name, loc } => DsDirective::Mod {
                name,
                loc: Some(loc),
            },
            Directive::Import { path, alias, loc } => Self::Import {
                path,
                alias,
                loc: Some(loc),
            },
        }
    }
}

impl FromHigher for DsItem {
    type Higher = Item;

    fn lower(node: Self::Higher) -> Self {
        match node {
            Item::GlobalConst {
                name,
                name_loc,
                typexpr,
                value,
                loc,
            } => DsItem::GlobalDef {
                sym: LazySymbol::Name(name.clone()),
                name,
                name_loc: Some(name_loc),
                mutable: false,
                typexpr: lower(typexpr),
                value: Box::new(lower(value)),
                loc: Some(loc),
            },
            Item::GlobalVar {
                name,
                name_loc,
                typexpr,
                value,
                loc,
            } => DsItem::GlobalDef {
                sym: LazySymbol::Name(name.clone()),
                name,
                name_loc: Some(name_loc),
                mutable: true,
                typexpr: lower(typexpr),
                value: Box::new(lower(value)),
                loc: Some(loc),
            },
            Item::ExternBlock { abi, items, loc } => DsItem::ExternBlock {
                abi,
                items: lower(items),
                loc: Some(loc),
            },
            Item::Directive(directive) => DsItem::Directive(lower(directive)),
        }
    }
}

/// A desugared expression, see the sweet version [`Expression`]
///
/// [`Expression`]: lunc_parser::expr::Expression
#[derive(Debug, Clone)]
pub struct DsExpression {
    pub expr: DsExpr,
    pub loc: OSpan,
}

impl FromHigher for DsExpression {
    type Higher = Expression;

    fn lower(node: Self::Higher) -> Self {
        let expr = match node.expr {
            Expr::IntLit(i) => DsExpr::IntLit(i),
            Expr::BoolLit(b) => DsExpr::BoolLit(b),
            Expr::StringLit(str) => DsExpr::StringLit(str),
            Expr::CharLit(c) => DsExpr::CharLit(c),
            Expr::FloatLit(f) => DsExpr::FloatLit(f),
            // we remove the parenthesis we don't need them anymore
            Expr::Grouping(e) => return lower(*e),
            Expr::Ident(id) => DsExpr::Ident(LazySymbol::Name(id)),
            Expr::Binary { lhs, op, rhs } => DsExpr::Binary {
                lhs: lower(lhs),
                op,
                rhs: lower(rhs),
            },
            Expr::Unary { op, expr } => DsExpr::Unary {
                op,
                expr: lower(expr),
            },
            Expr::Borrow { mutable, expr } => DsExpr::Borrow {
                mutable,
                expr: lower(expr),
            },
            Expr::FunCall {
                callee: called,
                args,
            } => DsExpr::FunCall {
                callee: lower(called),
                args: lower(args),
            },
            Expr::If(ifexpr) => lower_if_expression(ifexpr),
            Expr::IfThenElse {
                cond,
                true_val,
                false_val,
            } => DsExpr::If {
                cond: lower(cond),
                then_br: lower(true_val),
                else_br: Some(lower(false_val)),
            },
            Expr::Block(block) => DsExpr::Block {
                label: None,
                block: lower(block),
            },
            Expr::BlockWithLabel { label, block } => DsExpr::Block {
                label: Some(label),
                block: lower(block),
            },

            // NOTE: here we make the following conversion eg:
            //
            // ```
            // label: while condition {
            //     // body
            // }
            // ```
            //
            // gets lowered down to
            //
            // ```
            // label: loop {
            //     if !condition { // <- without this block
            //         break :label;
            //     }
            //
            //     {
            //         // body
            //     };
            // }
            // ```
            //
            // NOTE: if you modify the desugaring of while expression, this
            // might break the detection of while expression in the SCIR in
            // file `lunc_scir/src/checking.rs` in the function `ck_expr`
            Expr::PredicateLoop { label, cond, body } => DsExpr::Loop {
                label: label.clone(),
                body: block(
                    body.loc.clone(),
                    vec![
                        stmt_expr(expr_if(
                            expr_unary(UnaryOp::Not, lower(*cond)),
                            expr_break(label.map(|(name, _)| name), None),
                            None,
                        )),
                        stmt_expr(expr_block(lower(body))),
                    ],
                    None,
                ),
            },
            Expr::IteratorLoop { .. } => todo!("iterator loop"),
            Expr::InfiniteLoop { label, body } => DsExpr::Loop {
                label,
                body: lower(body),
            },
            Expr::Return { expr: val } => DsExpr::Return { expr: lower(val) },
            Expr::Break { label, expr: val } => DsExpr::Break {
                label,
                expr: lower(val),
            },
            Expr::Continue { label } => DsExpr::Continue { label },
            Expr::Null => DsExpr::Null,
            Expr::MemberAccess { expr, member } => DsExpr::MemberAccess {
                expr: lower(expr),
                member,
            },
            Expr::Orb => DsExpr::Ident(LazySymbol::Name("orb".to_string())),
            Expr::FunDefinition {
                args,
                rettypexpr,
                body,
            } => DsExpr::FunDefinition {
                args: lower(args),
                rettypexpr: lower(rettypexpr),
                body: lower(body),
            },
            Expr::FunDeclaration { args, rettypexpr } => DsExpr::FunDeclaration {
                args: lower(args),
                rettypexpr: lower(rettypexpr),
            },
            Expr::PointerType { mutable, typexpr } => DsExpr::PointerType {
                mutable,
                typexpr: lower(typexpr),
            },
            Expr::FunPtrType { args, ret } => DsExpr::FunPtrType {
                args: lower(args),
                ret: lower(ret),
            },
        };

        DsExpression {
            expr,
            loc: Some(node.loc),
        }
    }
}

pub fn lower_if_expression(ifexpr: IfExpression) -> DsExpr {
    DsExpr::If {
        cond: lower(ifexpr.cond),
        then_br: Box::new(DsExpression {
            expr: expr_block(lower(*ifexpr.body)).expr,
            loc: Some(ifexpr.loc.clone()),
        }),
        else_br: match ifexpr.else_br.map(|e| *e) {
            Some(Else::IfExpr(ifexp)) => Some(Box::new(DsExpression {
                loc: Some(ifexp.loc.clone()),
                expr: lower_if_expression(ifexp),
            })),
            Some(Else::Block(block)) => Some(Box::new(DsExpression {
                loc: Some(block.loc.clone()),
                expr: expr_block(lower(block)).expr,
            })),
            None => None,
        },
    }
}

/// A desugared expression internal, see the sweet version [`Expr`]
///
/// [`Expr`]: lunc_parser::expr::Expr
#[derive(Debug, Clone)]
pub enum DsExpr {
    /// See [`Expr::IntLit`]
    ///
    /// [`Expr::IntLit`]: lunc_parser::expr::Expr::IntLit
    IntLit(u128),
    /// See [`Expr::BoolLit`]
    ///
    /// [`Expr::BoolLit`]: lunc_parser::expr::Expr::BoolLit
    BoolLit(bool),
    /// See [`Expr::StringLit`]
    ///
    /// [`Expr::StringLit`]: lunc_parser::expr::Expr::StringLit
    StringLit(String),
    /// See [`Expr::CharLit`]
    ///
    /// [`Expr::CharLit`]: lunc_parser::expr::Expr::CharLit
    CharLit(char),
    /// See [`Expr::FloatLit`]
    ///
    /// [`Expr::FloatLit`]: lunc_parser::expr::Expr::FloatLit
    FloatLit(f64),
    /// See [`Expr::Ident`]
    ///
    /// [`Expr::Ident`]: lunc_parser::expr::Expr::Ident
    Ident(LazySymbol),
    /// See [`Expr::Binary`]
    ///
    /// [`Expr::Binary`]: lunc_parser::expr::Expr::Binary
    Binary {
        lhs: Box<DsExpression>,
        op: BinOp,
        rhs: Box<DsExpression>,
    },
    /// See [`Expr::Unary`]
    ///
    /// [`Expr::Unary`]: lunc_parser::expr::Expr::Unary
    Unary {
        op: UnaryOp,
        expr: Box<DsExpression>,
    },
    /// See [`Expr::Borrow`]
    ///
    /// [`Expr::Borrow`]: lunc_parser::expr::Expr::Borrow
    Borrow {
        mutable: bool,
        expr: Box<DsExpression>,
    },
    /// See [`Expr::FunCall`]
    ///
    /// [`Expr::FunCall`]: lunc_parser::expr::Expr::FunCall
    FunCall {
        callee: Box<DsExpression>,
        args: Vec<DsExpression>,
    },
    /// See [`Expr::If`] and [`Expr::IfThenElse`]
    ///
    /// [`Expr::If`]: lunc_parser::expr::Expr::If
    /// [`Expr::IfThenElse`]: lunc_parser::expr::Expr::IfThenElse
    If {
        cond: Box<DsExpression>,
        then_br: Box<DsExpression>,
        else_br: Option<Box<DsExpression>>,
    },
    /// See [`Expr::Block`]
    ///
    /// [`Expr::Block`]: lunc_parser::expr::Expr::Block
    Block {
        label: Option<(String, Span)>,
        block: DsBlock,
    },
    /// See [`Expr::InfiniteLoop`], [`Expr::IteratorLoop`] and [`Expr::PredicateLoop`].
    ///
    /// [`Expr::InfiniteLoop`]: lunc_parser::expr::Expr::InfiniteLoop
    /// [`Expr::IteratorLoop`]: lunc_parser::expr::Expr::IteratorLoop
    /// [`Expr::PredicateLoop`]: lunc_parser::expr::Expr::PredicateLoop
    Loop {
        label: Option<(String, Span)>,
        body: DsBlock,
    },
    /// See [`Expr::Return`]
    ///
    /// [`Expr::Return`]: lunc_parser::expr::Expr::Return
    Return { expr: Option<Box<DsExpression>> },
    /// See [`Expr::Break`]
    ///
    /// [`Expr::Break`]: lunc_parser::expr::Expr::Break
    Break {
        label: Option<String>,
        expr: Option<Box<DsExpression>>,
    },
    /// See [`Expr::Continue`]
    ///
    /// [`Expr::Continue`]: lunc_parser::expr::Expr::Continue
    Continue { label: Option<String> },
    /// See [`Expr::Null`]
    ///
    /// [`Expr::Null`]: lunc_parser::expr::Expr::Null
    Null,
    /// See [`Expr::MemberAccess`]
    ///
    /// After the name resolution, member access of modules are converted to [`EffectivePath`]
    /// [`Expr::MemberAccess`]: lunc_parser::expr::Expr::MemberAccess
    MemberAccess {
        expr: Box<DsExpression>,
        member: String,
    },
    /// Constructed from member access, eg:
    ///
    /// `orb.driver.run` are member accesses and it refers to a function "run",
    /// so this expression is lowered down to an EffectivePath
    QualifiedPath {
        /// path to the symbol
        path: QualifiedPath,
        /// the symbol we are referring to
        sym: LazySymbol,
    },
    /// Constructed from the lazy ident `_`, but only in certain cases, like
    /// when it's part of an assignment like so: `_ = expr`
    Underscore,
    /// See [`Expr::FunDefinition`]
    ///
    /// [`Expr::FunDefinition`]: lunc_parser::expr::Expr::FunDefinition
    FunDefinition {
        args: Vec<DsArg>,
        rettypexpr: Option<Box<DsExpression>>,
        body: DsBlock,
    },
    /// See [`Expr::FunDeclaration`]
    ///
    /// [`Expr::FunDeclaration`]: lunc_parser::expr::Expr::FunDeclaration
    FunDeclaration {
        args: Vec<DsExpression>,
        rettypexpr: Option<Box<DsExpression>>,
    },
    /// See [`Expr::PointerType`]
    ///
    /// [`Expr::PointerType`]: lunc_parser::expr::Expr::PointerType
    PointerType {
        mutable: bool,
        typexpr: Box<DsExpression>,
    },
    /// See [`Expr::FunPtrType`]
    ///
    /// [`Expr::FunPtrType`]: lunc_parser::expr::Expr::FunPtrType
    FunPtrType {
        args: Vec<DsExpression>,
        ret: Option<Box<DsExpression>>,
    },
}

impl DsExpr {
    pub fn is_fundef(&self) -> bool {
        matches!(self, Self::FunDefinition { .. })
    }

    pub fn is_fundecl(&self) -> bool {
        matches!(self, Self::FunDeclaration { .. })
    }
}

/// Creates an integer expression without location.
pub fn expr_int(i: impl Into<u128>) -> DsExpression {
    DsExpression {
        expr: DsExpr::IntLit(i.into()),
        loc: None,
    }
}

/// Creates an boolean expression without location.
pub fn expr_bool(b: bool) -> DsExpression {
    DsExpression {
        expr: DsExpr::BoolLit(b),
        loc: None,
    }
}

/// Creates an string expression without location.
pub fn expr_string(str: impl ToString) -> DsExpression {
    DsExpression {
        expr: DsExpr::StringLit(str.to_string()),
        loc: None,
    }
}

/// Creates an character expression without location.
pub fn expr_char(c: impl Into<char>) -> DsExpression {
    DsExpression {
        expr: DsExpr::CharLit(c.into()),
        loc: None,
    }
}

/// Creates an character expression without location.
pub fn expr_float(f: f64) -> DsExpression {
    DsExpression {
        expr: DsExpr::FloatLit(f),
        loc: None,
    }
}

/// Creates an ident expression without location.
pub fn expr_ident(id: impl Into<LazySymbol>) -> DsExpression {
    DsExpression {
        expr: DsExpr::Ident(id.into()),
        loc: None,
    }
}

/// Creates a binary expression without location.
pub fn expr_binary(lhs: DsExpression, op: BinOp, rhs: DsExpression) -> DsExpression {
    DsExpression {
        expr: DsExpr::Binary {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        },
        loc: None,
    }
}

/// Creates a unary expression without location.
pub fn expr_unary(op: UnaryOp, expr: DsExpression) -> DsExpression {
    DsExpression {
        expr: DsExpr::Unary {
            op,
            expr: Box::new(expr),
        },
        loc: None,
    }
}

/// Creates an address of expression without location.
pub fn expr_borrow(mutable: bool, val: DsExpression) -> DsExpression {
    DsExpression {
        expr: DsExpr::Borrow {
            mutable,
            expr: Box::new(val),
        },
        loc: None,
    }
}

/// Creates a function call expression without location.
pub fn expr_funcall(
    called: DsExpression,
    args: impl Iterator<Item = DsExpression>,
) -> DsExpression {
    DsExpression {
        expr: DsExpr::FunCall {
            callee: Box::new(called),
            args: args.collect(),
        },
        loc: None,
    }
}

/// Creates an if expression without location.
pub fn expr_if(
    cond: DsExpression,
    then_br: DsExpression,
    else_br: impl Into<Option<DsExpression>>,
) -> DsExpression {
    DsExpression {
        expr: DsExpr::If {
            cond: Box::new(cond),
            then_br: Box::new(then_br),
            else_br: else_br.into().map(Box::new),
        },
        loc: None,
    }
}

/// Creates a block expression without location.
pub fn expr_block(block: DsBlock) -> DsExpression {
    DsExpression {
        expr: DsExpr::Block { label: None, block },
        loc: None,
    }
}

/// Creates a loop expression without location.
pub fn expr_loop(label: Option<(String, Span)>, body: DsBlock) -> DsExpression {
    DsExpression {
        expr: DsExpr::Loop { label, body },
        loc: None,
    }
}

/// Creates a return expression without location.
pub fn expr_return(val: impl Into<Option<DsExpression>>) -> DsExpression {
    DsExpression {
        expr: DsExpr::Return {
            expr: val.into().map(Box::new),
        },
        loc: None,
    }
}

/// Creates a break expression without location.
pub fn expr_break(label: Option<String>, val: impl Into<Option<DsExpression>>) -> DsExpression {
    DsExpression {
        expr: DsExpr::Break {
            label,
            expr: val.into().map(Box::new),
        },
        loc: None,
    }
}

/// Creates a continue expression without location.
pub fn expr_continue(label: Option<String>) -> DsExpression {
    DsExpression {
        expr: DsExpr::Continue { label },
        loc: None,
    }
}

/// Creates a null expression without location.
pub fn expr_null() -> DsExpression {
    DsExpression {
        expr: DsExpr::Null,
        loc: None,
    }
}

/// Creates a member access expression without location.
pub fn expr_member_access(expr: DsExpression, member: impl ToString) -> DsExpression {
    DsExpression {
        expr: DsExpr::MemberAccess {
            expr: Box::new(expr),
            member: member.to_string(),
        },
        loc: None,
    }
}

/// Creates a function definition expression without location.
pub fn expr_fundef(
    args: Vec<DsArg>,
    rettypexpr: impl Into<Option<DsExpression>>,
    body: DsBlock,
) -> DsExpression {
    DsExpression {
        expr: DsExpr::FunDefinition {
            args,
            rettypexpr: rettypexpr.into().map(Box::new),
            body,
        },
        loc: None,
    }
}

/// Creates a pointer type expression without location.
pub fn expr_ptr_type(mutable: bool, typexpr: DsExpression) -> DsExpression {
    DsExpression {
        expr: DsExpr::PointerType {
            mutable,
            typexpr: Box::new(typexpr),
        },
        loc: None,
    }
}

/// Creates a function pointer type expression without location.
pub fn expr_fun_ptr_type(
    args: Vec<DsExpression>,
    ret: impl Into<Option<DsExpression>>,
) -> DsExpression {
    DsExpression {
        expr: DsExpr::FunPtrType {
            args,
            ret: ret.into().map(Box::new),
        },
        loc: None,
    }
}

/// A desugared block, see the sweet version [`Block`]
///
/// [`Block`]: lunc_parser::stmt::Block
#[derive(Debug, Clone)]
pub struct DsBlock {
    pub stmts: Vec<DsStatement>,
    pub last_expr: Option<Box<DsExpression>>,
    pub loc: OSpan,
}

/// Creates a new block without a location
pub fn block(
    loc: impl Into<OSpan>,
    stmts: Vec<DsStatement>,
    last_expr: Option<Box<DsExpression>>,
) -> DsBlock {
    DsBlock {
        stmts,
        last_expr,
        loc: loc.into(),
    }
}

impl FromHigher for DsBlock {
    type Higher = Block;

    fn lower(node: Self::Higher) -> Self {
        let Block {
            stmts,
            last_expr,
            loc,
        } = node;

        DsBlock {
            stmts: lower(stmts),
            last_expr: lower(last_expr),
            loc: Some(loc),
        }
    }
}

/// A desugared statement, see the sweet version [`Statement`]
///
/// [`Statement`]: lunc_parser::stmt::Statement
#[derive(Debug, Clone)]
pub struct DsStatement {
    pub stmt: DsStmt,
    pub loc: OSpan,
}

impl FromHigher for DsStatement {
    type Higher = Statement;

    fn lower(node: Self::Higher) -> Self {
        let stmt = match node.stmt {
            Stmt::VariableDef {
                name,
                name_loc,
                mutable,
                typexpr,
                value,
            } => DsStmt::VariableDef {
                sym: LazySymbol::Name(name.clone()),
                name,
                name_loc: Some(name_loc),
                mutable,
                typexpr: lower(typexpr),
                value: lower(value),
            },
            Stmt::Defer { expr } => DsStmt::Defer { expr: lower(expr) },
            Stmt::Expression(expr) => DsStmt::Expression(lower(expr)),
        };

        DsStatement {
            stmt,
            loc: Some(node.loc),
        }
    }
}

#[derive(Debug, Clone)]
pub enum DsStmt {
    /// See [`Stmt::VariableDef`]
    ///
    /// [`Stmt::VariableDef`]: lunc_parser::stmt::Stmt::VariableDef
    VariableDef {
        name: String,
        name_loc: OSpan,
        mutable: bool,
        typexpr: Option<DsExpression>,
        value: Box<DsExpression>,
        sym: LazySymbol,
    },
    /// See [`Stmt::Defer`]
    ///
    /// [`Stmt::Defer`]: lunc_parser::stmt::Stmt::Defer
    Defer { expr: DsExpression },
    /// See [`Stmt::Expression`]
    ///
    /// [`Stmt::Expression`]: lunc_parser::stmt::Stmt::Expression
    Expression(DsExpression),
}

/// Creates an expression statement without location.
pub fn stmt_expr(expr: DsExpression) -> DsStatement {
    DsStatement {
        stmt: DsStmt::Expression(expr),
        loc: None,
    }
}

/// A desugared argument, see the sweet version [`Arg`]
///
/// [`Arg`]: lunc_parser::expr::Arg
#[derive(Debug, Clone)]
pub struct DsArg {
    pub name: String,
    pub name_loc: OSpan,
    pub typexpr: DsExpression,
    pub loc: OSpan,
    pub sym: LazySymbol,
}

impl FromHigher for DsArg {
    type Higher = Arg;

    fn lower(node: Self::Higher) -> Self {
        let Arg {
            name,
            name_loc,
            typexpr,
            loc,
        } = node;

        DsArg {
            sym: LazySymbol::Name(name.clone()),
            name,
            name_loc: Some(name_loc),
            typexpr: lower(typexpr),
            loc: Some(loc),
        }
    }
}

/// Helping struct to convert AST to DSIR
#[derive(Debug, Clone)]
pub struct Desugarrer {
    /// the sink of diagnostics
    sink: DiagnosticSink,
    /// symbol table, maps a name to a symbol in the current scope
    table: SymbolTable,
    /// root module of the orb we are building
    orb: ModuleTree,
    /// current path of the module we are desugarring
    current_path: EffectivePath,
}

impl Desugarrer {
    /// Create a new desugarrer.
    pub fn new(sink: DiagnosticSink, orb_name: String) -> Desugarrer {
        Desugarrer {
            sink,
            table: SymbolTable::new(),
            orb: ModuleTree::new(Some(orb_name), LazySymbol::Name("orb".to_string())),
            current_path: EffectivePath::with_root_member("orb"),
        }
    }

    /// Get the orb name
    pub fn orb_name(&self) -> &str {
        self.orb.root_name.as_deref().unwrap()
    }

    /// Try to produce a desugarred module.
    pub fn produce(&mut self, ast: Module) -> Option<DsModule> {
        let mut module = lower(ast);

        self.inline_modules(&mut module);

        if !module.fid.is_root() {
            // we return early if this is not the root module to not messed up
            // the recursion
            return Some(module);
        }

        self.orb.sym = LazySymbol::Sym(self.table.lookup("orb").unwrap());

        // resolve the root module, then it will recurse
        self.resolve_module(&mut module, self.current_path.clone());

        if self.sink.failed() {
            return None;
        }

        Some(module)
    }

    /// Takes a module and converts (recursively) the Mod directive to Item Mod.
    ///
    /// So in this function, we:
    /// 1. look for the file that corresponds to the module name
    /// 2. lex this file
    /// 3. parse this token stream
    /// 4. desugar this ast
    /// 5. put the items of the module inside the parent module, in a `DsItem::Module`
    pub fn inline_modules(&mut self, parent: &mut DsModule) {
        let parent_path = PathBuf::from(self.sink.name(parent.fid).unwrap());

        for item in &mut parent.items {
            if let DsItem::Directive(DsDirective::Mod { name, loc }) = item {
                // 1. compute the path of the submodule
                let submodule_path = if parent.fid.is_root() {
                    // root module's path
                    parent_path
                        .with_file_name(name.clone())
                        .with_extension("lun")
                } else {
                    // submodule module's path
                    parent_path
                        .with_extension("")
                        .join(name.clone())
                        .with_extension("lun")
                };

                if !submodule_path.exists() {
                    self.sink.emit(ModuleFileDoesnotExist {
                        name: name.clone(),
                        expected_path: submodule_path,
                        loc: loc.clone().unwrap(),
                    });
                    continue;
                }

                // 2. retrieve the source code of the submodule
                let source_code = fs::read_to_string(&submodule_path).unwrap();

                // 3. add it to the sink
                let submodule_fid = self.sink.register_file(
                    submodule_path.to_string_lossy().to_string(),
                    source_code.clone(),
                );

                // 4. lex the submodule
                let mut lexer = Lexer::new(self.sink.clone(), source_code.clone(), submodule_fid);
                let tokenstream = match lexer.produce() {
                    Some(toks) => toks,
                    None => continue,
                };

                // 5. parse the submodule
                let mut parser = Parser::new(tokenstream, self.sink.clone(), submodule_fid);
                let ast = match parser.produce() {
                    Some(ast) => ast,
                    None => continue,
                };

                // 6. desugar it.
                let submodule_dsir = match self.produce(ast) {
                    Some(dsir) => dsir,
                    None => continue,
                };

                *item = DsItem::Module {
                    name: name.clone(),
                    module: submodule_dsir,
                    loc: loc.clone(),
                    sym: LazySymbol::Name(name.clone()),
                };
            }
        }

        // we successfully inlined all modules :)
    }

    /// Resolve names in module
    ///
    /// # Resolve path
    ///
    /// it is the path of the module we are currently resolving, it is not
    /// changed when we bind global defs recursively to be able to know when
    /// we need to something in bind global def but for the current scope, like
    /// the use directive that needs to bind names to symbols only if we are
    /// resolving the module this use directive was written in.
    ///
    /// *(kinda incomprensible garbage but you know..)*
    pub fn resolve_module(&mut self, module: &mut DsModule, resolve_path: EffectivePath) {
        self.table.scope_enter(); // module scope

        self.bind_global_defs(&mut module.items, resolve_path);

        for item in &mut module.items {
            match self.resolve_item(item) {
                Ok(()) => {}
                Err(d) => self.sink.emit(d),
            }
        }

        self.table.scope_exit(); // module scope

        self.current_path.push(String::new());

        // recuresivelly resolve submodules
        for item in &mut module.items {
            if let DsItem::Module {
                name,
                module: submod,
                ..
            } = item
            {
                *self.current_path.last_mut().unwrap() = name.clone();

                self.resolve_module(submod, self.current_path.clone());
            }
        }
    }

    /// Resolve names of an item
    pub fn resolve_item(&mut self, item: &mut DsItem) -> Result<(), Diagnostic> {
        match item {
            DsItem::GlobalDef { typexpr, value, .. } => {
                if let Some(typexpr) = typexpr {
                    self.resolve_expr(typexpr)?;
                }

                self.resolve_expr(value)?;

                Ok(())
            }
            DsItem::ExternBlock {
                abi: _,
                items,
                loc: _,
            } => {
                for item in items {
                    match self.resolve_item(item) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                Ok(())
            }
            DsItem::Module { .. } | DsItem::Directive(_) => Ok(()),
        }
    }

    /// Resolve names in block
    pub fn resolve_block(&mut self, block: &mut DsBlock) {
        self.table.scope_enter(); // block scope

        for stmt in &mut block.stmts {
            match self.resolve_stmt(stmt) {
                Ok(()) => {}
                Err(d) => self.sink.emit(d),
            }
        }

        if let Some(expr) = &mut block.last_expr {
            match self.resolve_expr(expr) {
                Ok(()) => {}
                Err(d) => self.sink.emit(d),
            }
        }

        self.table.scope_exit(); // block scope
    }

    /// Resolve statement
    pub fn resolve_stmt(&mut self, stmt: &mut DsStatement) -> Result<(), Diagnostic> {
        match &mut stmt.stmt {
            DsStmt::VariableDef {
                name,
                name_loc,
                mutable,
                typexpr,
                value,
                sym,
            } => {
                match (|| -> Result<(), Diagnostic> {
                    if let Some(typexpr) = typexpr {
                        self.resolve_expr(typexpr)?;
                    }
                    self.resolve_expr(value)?;

                    Ok(())
                })() {
                    Ok(()) => {}
                    Err(d) => self.sink.emit(d),
                }

                let symref = Symbol::local(
                    *mutable,
                    name.clone(),
                    self.table.local_count(),
                    if typexpr.is_some() {
                        Typeness::Explicit
                    } else {
                        Typeness::Implicit
                    },
                    name_loc.clone(),
                );

                *sym = LazySymbol::Sym(symref.clone());

                self.table.bind(name.clone(), symref)?;

                Ok(())
            }
            DsStmt::Defer { expr } | DsStmt::Expression(expr) => self.resolve_expr(expr),
        }
    }

    /// Resolve expression
    pub fn resolve_expr(&mut self, expr: &mut DsExpression) -> Result<(), Diagnostic> {
        match &mut expr.expr {
            DsExpr::IntLit(_)
            | DsExpr::BoolLit(_)
            | DsExpr::StringLit(_)
            | DsExpr::CharLit(_)
            | DsExpr::FloatLit(_) => Ok(()),
            DsExpr::Binary {
                lhs,
                op: BinOp::Assignment,
                rhs,
            } if matches!(&lhs.expr, DsExpr::Ident(LazySymbol::Name(id)) if id.as_str() == "_") => {
                // we allow _ in lhs of assignment
                lhs.expr = DsExpr::Underscore;
                self.resolve_expr(rhs)
            }
            DsExpr::Binary { lhs, op: _, rhs } => {
                self.resolve_expr(lhs)?;
                self.resolve_expr(rhs)
            }
            DsExpr::Unary { op: _, expr } | DsExpr::Borrow { mutable: _, expr } => {
                self.resolve_expr(expr)
            }
            DsExpr::FunCall { callee, args } => {
                self.resolve_expr(callee)?;

                for arg in args {
                    self.resolve_expr(arg)?;
                }

                Ok(())
            }
            DsExpr::If {
                cond,
                then_br,
                else_br,
            } => {
                self.resolve_expr(cond)?;

                self.resolve_expr(then_br)?;

                if let Some(else_br) = else_br {
                    self.resolve_expr(else_br)?;
                }

                Ok(())
            }
            DsExpr::Block { label, block } | DsExpr::Loop { label, body: block } => {
                _ = label;

                self.resolve_block(block);

                Ok(())
            }
            DsExpr::Return { expr } | DsExpr::Break { label: _, expr } => {
                if let Some(expr) = expr {
                    self.resolve_expr(expr)?;
                }

                Ok(())
            }
            DsExpr::Continue { label: _ } | DsExpr::Null => Ok(()),
            DsExpr::PointerType {
                mutable: _,
                typexpr,
            } => self.resolve_expr(typexpr),
            DsExpr::FunPtrType { args, ret } => {
                for arg in args {
                    self.resolve_expr(arg)?;
                }

                if let Some(ret) = ret {
                    self.resolve_expr(ret)?;
                }

                Ok(())
            }
            DsExpr::Ident(LazySymbol::Name(name)) => {
                let Some(symref) = self.table.lookup(&*name) else {
                    return Err(NotFoundInScope {
                        name: name.clone(),
                        loc: expr.loc.clone().unwrap(),
                    }
                    .into_diag());
                };

                symref.inspect(|sym| {
                    if sym.name == "_" {
                        return Err(UnderscoreInExpression {
                            loc: expr.loc.clone().unwrap(),
                        }
                        .into_diag());
                    }

                    Ok(())
                })?;

                expr.expr = DsExpr::Ident(LazySymbol::Sym(symref.clone()));

                Ok(())
            }
            // NOTE: they cannot be reached because they are constructed in this
            // method, its an internal error if it is reached, so we panic.
            DsExpr::Ident(LazySymbol::Sym(_))
            | DsExpr::Underscore
            | DsExpr::QualifiedPath {
                path: _,
                sym: LazySymbol::Sym(_),
            } => unreachable!(),
            DsExpr::QualifiedPath { path, sym } => {
                let LazySymbol::Name(sym_name) = sym else {
                    // SAFETY: we already matched just above, it can only be that
                    opt_unrecheable!()
                };
                let mut mod_path = path.path.clone();

                mod_path.pop();

                let mut search_path = self.current_path.clone();
                search_path.append(mod_path.clone());

                if let Some(module) = self.orb.goto(&mod_path)
                    && let Some(symref) = module.def_or_mod(&sym_name)
                {
                    // looked up in orb tree for absolute paths (in general)
                    *sym = LazySymbol::Sym(symref);

                    Ok(())
                } else if let Some(module) = self.orb.goto(&search_path)
                    && let Some(symref) = module.def_or_mod(&sym_name)
                {
                    // looked up in orb tree for relative paths (in general)
                    *sym = LazySymbol::Sym(symref);

                    Ok(())
                } else if let Some(symref) = self.table.lookup(&sym_name) {
                    // looked up in scope for local module or imports (in general)
                    *sym = LazySymbol::Sym(symref);

                    Ok(())
                } else if let Some(search_path) = self
                    .table
                    .lookup(mod_path.first().unwrap())
                    .map(|sym| sym.path())
                    && let Some(module) = self.orb.goto(&search_path)
                    && let Some(symref) = module.def_or_mod(&sym_name)
                {
                    // looked up in orb tree for relative paths
                    //
                    // a relative path is a path that does not start with `orb`,
                    // and the first member is a refers to a module

                    *sym = LazySymbol::Sym(symref);
                    Ok(())
                } else {
                    Err(NotFoundInScope {
                        name: path.path.to_string(),
                        loc: path.loc.clone(),
                    }
                    .into_diag())
                }
            }
            DsExpr::MemberAccess { .. } => {
                if let Some(path) = self.flatten_member_access(expr) {
                    *expr = DsExpression {
                        expr: DsExpr::QualifiedPath {
                            sym: LazySymbol::Name(path.last().unwrap().clone()),
                            path: QualifiedPath {
                                path,
                                loc: expr.loc.clone().unwrap(),
                            },
                        },
                        loc: expr.loc.clone(),
                    };

                    self.resolve_expr(expr)
                } else {
                    let DsExpr::MemberAccess {
                        expr: exp,
                        member: _,
                    } = &mut expr.expr
                    else {
                        // SAFETY: we already matched this expression we know
                        // it is a member access for sure
                        opt_unrecheable!()
                    };

                    self.resolve_expr(&mut *exp)?;

                    Ok(())
                }
            }
            DsExpr::FunDefinition {
                args,
                rettypexpr,
                body,
            } => {
                for DsArg {
                    name,
                    name_loc,
                    typexpr,
                    loc: _,
                    sym,
                } in args
                {
                    match self.resolve_expr(typexpr) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }

                    let symref =
                        Symbol::arg(name.clone(), self.table.local_count(), name_loc.clone());

                    *sym = LazySymbol::Sym(symref.clone());

                    self.table.bind(name.clone(), symref)?;
                }

                if let Some(retty) = rettypexpr {
                    self.resolve_expr(retty)?;
                }

                self.resolve_block(body);

                Ok(())
            }
            DsExpr::FunDeclaration { args, rettypexpr } => {
                for arg in args {
                    match self.resolve_expr(arg) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                if let Some(retty) = rettypexpr {
                    self.resolve_expr(retty)?;
                }

                Ok(())
            }
        }
    }

    /// Returns an effective path if the root of the effective path is a module,
    /// and converts the nested member accesses to an effective path.
    pub fn flatten_member_access(&mut self, expr: &DsExpression) -> Option<EffectivePath> {
        let mut path = Vec::new();
        let mut current = expr;

        while let DsExpr::MemberAccess { expr, member } = &current.expr {
            path.push(member.as_str());
            current = &**expr;
        }

        match &current.expr {
            DsExpr::Ident(LazySymbol::Name(member)) => {
                path.push(member);
            }
            _ => return None,
        }

        path.reverse();

        if let Some(sym) = self.table.lookup(path.first().unwrap())
            && sym.kind() == SymKind::Module
        {
            Some(EffectivePath::from_iter(path.iter()))
        } else {
            None
        }
    }

    /// Bind all the global definitions before resolving recursively the dsir
    pub fn bind_global_defs(&mut self, items: &mut [DsItem], resolve_path: EffectivePath) {
        for item in items {
            match self.bind_global_def(item, resolve_path.clone()) {
                Ok(()) => {}
                Err(d) => {
                    self.sink.emit(d);
                }
            }
        }
    }

    /// bind symbols in the module tree and in the symbol table if we resolve in
    /// the current path
    fn bind_global_def(
        &mut self,
        item: &mut DsItem,
        resolve_path: EffectivePath,
    ) -> Result<(), Diagnostic> {
        match item {
            DsItem::GlobalDef {
                name,
                name_loc,
                mutable: _,
                typexpr: _,
                value,
                loc: _,
                sym,
            } if value.expr.is_fundef() || value.expr.is_fundecl() => {
                let mut path = self.current_path.clone();
                path.push(name.clone());

                let symref =
                    sym.symbol()
                        .unwrap_or(Symbol::function(name.clone(), path, name_loc.clone()));

                self.orb
                    .goto_mut(&self.current_path)
                    .unwrap()
                    .define(name.clone(), symref.clone());

                *sym = LazySymbol::Sym(symref.clone());

                if self.current_path == resolve_path {
                    match self.table.bind(name.clone(), symref) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                Ok(())
            }
            DsItem::GlobalDef {
                name,
                name_loc,
                mutable,
                typexpr,
                value: _,
                loc: _,
                sym,
            } => {
                let mut path = self.current_path.clone();
                path.push(name.clone());

                let symref = sym.symbol().unwrap_or(Symbol::global(
                    *mutable,
                    name.clone(),
                    path,
                    if typexpr.is_some() {
                        Typeness::Explicit
                    } else {
                        Typeness::Implicit
                    },
                    name_loc.clone(),
                ));

                self.orb
                    .goto_mut(&self.current_path)
                    .unwrap()
                    .define(name.clone(), symref.clone());

                *sym = LazySymbol::Sym(symref.clone());

                match self.table.bind(name.clone(), symref) {
                    Ok(()) => {}
                    Err(d) => self.sink.emit(d),
                }

                Ok(())
            }
            DsItem::Module {
                name,
                module,
                loc,
                sym,
            } => {
                let mut path = self.current_path.clone();
                path.push(name.clone());

                let symref =
                    sym.symbol()
                        .unwrap_or(Symbol::module(name.clone(), path, loc.clone()));

                *sym = LazySymbol::Sym(symref.clone());

                self.orb
                    .goto_mut(&self.current_path)
                    .unwrap()
                    .define_mod(name.clone(), symref.clone());

                if self.current_path == resolve_path {
                    match self.table.bind(name.clone(), symref) {
                        Ok(()) => {}
                        Err(d) => self.sink.emit(d),
                    }
                }

                // change current path for the recursion to work
                self.current_path.push(name.clone());

                // start binding global defs of submodule
                self.bind_global_defs(&mut module.items, resolve_path);

                // pop the current path to recover the path we had before
                self.current_path.pop();

                Ok(())
            }
            DsItem::ExternBlock {
                abi: _,
                items,
                loc: _,
            } => {
                // NOTE: we check, its optional in theory but it should speed up
                // a little bit
                if self.current_path == resolve_path {
                    self.bind_global_defs(items, resolve_path);
                }

                Ok(())
            }
            DsItem::Directive(DsDirective::Import {
                path,
                alias,
                loc: _,
            }) => {
                if self.current_path != resolve_path {
                    return Ok(());
                }
                let mut mod_path = path.path.clone();

                let name = mod_path.pop().unwrap();

                if let Some(module) = self.orb.goto(&mod_path)
                    && let Some(symref) = module.def_or_mod(&name)
                {
                    self.table.bind(alias.clone().unwrap_or(name), symref)
                } else {
                    Err(NotFoundInScope {
                        name: path.path.to_string(),
                        loc: path.loc.clone(),
                    }
                    .into_diag())
                }
            }
            DsItem::Directive(DsDirective::Mod { .. }) => Ok(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SymbolMap {
    map: HashMap<String, Symbol>,
    fun_count: usize,
    global_count: usize,
    local_count: usize,
    arg_count: usize,
    mod_count: usize,
}

impl SymbolMap {
    pub fn new() -> SymbolMap {
        SymbolMap {
            map: HashMap::new(),
            fun_count: 0,
            global_count: 0,
            local_count: 0,
            arg_count: 0,
            mod_count: 0,
        }
    }

    pub fn first_scope() -> SymbolMap {
        SymbolMap {
            map: HashMap::from([
                ("isz".to_string(), Symbol::new_typ("isz", Type::Isz)),
                ("i128".to_string(), Symbol::new_typ("i128", Type::I128)),
                ("i64".to_string(), Symbol::new_typ("i64", Type::I64)),
                ("i32".to_string(), Symbol::new_typ("i32", Type::I32)),
                ("i16".to_string(), Symbol::new_typ("i16", Type::I16)),
                ("i8".to_string(), Symbol::new_typ("i8", Type::I8)),
                ("usz".to_string(), Symbol::new_typ("usz", Type::Usz)),
                ("u128".to_string(), Symbol::new_typ("u128", Type::U128)),
                ("u64".to_string(), Symbol::new_typ("u64", Type::U64)),
                ("u32".to_string(), Symbol::new_typ("u32", Type::U32)),
                ("u16".to_string(), Symbol::new_typ("u16", Type::U16)),
                ("u8".to_string(), Symbol::new_typ("u8", Type::U8)),
                ("f16".to_string(), Symbol::new_typ("f16", Type::F16)),
                ("f32".to_string(), Symbol::new_typ("f32", Type::F32)),
                ("f64".to_string(), Symbol::new_typ("f64", Type::F64)),
                ("f128".to_string(), Symbol::new_typ("f128", Type::F128)),
                ("bool".to_string(), Symbol::new_typ("bool", Type::Bool)),
                ("str".to_string(), Symbol::new_typ("str", Type::Str)),
                ("char".to_string(), Symbol::new_typ("char", Type::Char)),
                (
                    "noreturn".to_string(),
                    Symbol::new_typ("usz", Type::Noreturn),
                ),
                ("void".to_string(), Symbol::new_typ("usz", Type::Void)),
                (
                    "orb".to_string(),
                    // NOTE: here we can set the loc to be 0..0 into the root
                    // file, its fine ig, a span from the first character to eof
                    // would be better but this works
                    Symbol::module(
                        "orb".to_string(),
                        EffectivePath::with_root_member("orb"),
                        Some(lunc_utils::Span::ZERO),
                    ),
                ),
            ]),
            fun_count: 0,
            global_count: 0,
            local_count: 0,
            arg_count: 0,
            mod_count: 0,
        }
    }
}

impl Default for SymbolMap {
    fn default() -> Self {
        Self::new()
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
    pub fn scope_exit(&mut self) {
        assert_ne!(self.tabs.len(), 1, "can't exit out of the global scope");

        self.tabs.pop();
    }

    /// Bind a name to a symbol in the current scope, returns a diagnostic if name == `_`
    pub fn bind(&mut self, name: String, sym: Symbol) -> Result<(), Diagnostic> {
        let sym_kind = sym.kind();

        if let Some(previous_sym) = self.lookup(&name)
            && !previous_sym.kind().can_shadow()
        {
            return Err(NameDefinedMultipleTimes {
                name: &name,
                loc_previous: previous_sym.loc().unwrap(),
                loc: sym.loc().unwrap(),
            }
            .into_diag());
        }

        match sym_kind {
            SymKind::Local { .. } => {
                self.last_map_mut().local_count += 1;
            }
            SymKind::Arg => {
                self.last_map_mut().arg_count += 1;
            }
            SymKind::Global { .. } => {
                self.last_map_mut().global_count += 1;
            }
            SymKind::Function => {
                self.last_map_mut().fun_count += 1;
            }
            SymKind::Module => {
                self.last_map_mut().mod_count += 1;
            }
        }

        if name.as_str() == "_" {
            return Err(UnderscoreReservedIdent {
                loc: sym.loc().unwrap(),
            }
            .into_diag());
        }

        self.last_map_mut().map.insert(name, sym.clone());

        Ok(())
    }

    /// Return the current scope level
    pub fn level(&self) -> usize {
        self.tabs.len() - 1
    }

    /// Lookup for the symbol in the current scope, returns None if there is no
    /// symbol with this name in the current scope
    pub fn lookup_current(&self, name: impl AsRef<str>) -> Option<Symbol> {
        self.last_map().map.get(name.as_ref()).cloned()
    }

    /// Lookup for a symbol with the given name, starting at the current scope
    /// ending at the global scope, returns None if there is no symbol in any
    /// scopes
    pub fn lookup(&mut self, name: impl AsRef<str>) -> Option<Symbol> {
        let name = name.as_ref();

        for tab in self.tabs.iter().rev() {
            if let Some(symref) = tab.map.get(name) {
                return Some(symref.clone());
            }
        }

        None
    }

    /// Returns the Var count of the last symbol map
    pub fn local_count(&self) -> usize {
        self.last_map().local_count
    }

    /// Returns the Arg count of the last symbol map
    pub fn arg_count(&self) -> usize {
        self.last_map().arg_count
    }

    /// Returns the Global count of the last symbol map
    pub fn global_count(&self) -> usize {
        self.last_map().global_count
    }

    /// Returns the Function count of the last symbol map
    pub fn fun_count(&self) -> usize {
        self.last_map().fun_count
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

/// A tree representing the orb definitions as a tree
#[derive(Debug, Clone)]
pub struct ModuleTree {
    /// submodules of this module
    submodules: HashMap<String, ModuleTree>,
    /// definitions in this module tree, a definition can only be one of:
    /// - global
    /// - function
    defs: HashMap<String, Symbol>,
    /// is this module tree the root module?
    root_name: Option<String>,
    /// symbol of the module
    pub sym: LazySymbol,
}

impl ModuleTree {
    /// Creates a new ModuleTree, set `root_name` arg to None if the ModuleTree
    /// you want to create is not the root module of the orb.
    pub fn new(root_name: Option<String>, sym: LazySymbol) -> ModuleTree {
        ModuleTree {
            submodules: HashMap::default(),
            defs: HashMap::new(),
            root_name,
            sym,
        }
    }

    /// Get the submodule of the current module with `name`.
    pub fn submod(&self, name: impl AsRef<str>) -> Option<&ModuleTree> {
        self.submodules.get(name.as_ref())
    }

    /// Mutable get the submodule of the current module with `name`.
    pub fn submod_mut(&mut self, name: impl AsRef<str>) -> Option<&mut ModuleTree> {
        self.submodules.get_mut(name.as_ref())
    }

    /// Define a new symbol inside the current module tree
    pub fn define(&mut self, name: String, sym: Symbol) {
        assert!(matches!(
            sym.kind(),
            SymKind::Global { .. } | SymKind::Function
        ));

        self.defs.insert(name, sym.clone());
    }

    /// Define a new module in the current module tree
    pub fn define_mod(&mut self, name: String, symref: Symbol) {
        self.submodules
            .insert(name.clone(), ModuleTree::new(None, LazySymbol::Sym(symref)));
    }

    /// Is this module the root module of the orb?
    #[inline]
    pub fn is_root(&self) -> bool {
        self.root_name.is_some()
    }

    /// If self is root module, get the submodule at the `path` and returns it,
    /// or returns None if the path does not lead to anything
    pub fn goto(&self, path: &EffectivePath) -> Option<&ModuleTree> {
        assert!(self.is_root());

        let mut iterator = path.as_slice().iter();

        let Some("orb") = iterator.next().map(|s| s.as_str()) else {
            return None;
        };

        let mut current_module = self;

        for member in iterator {
            current_module = current_module.submod(member)?;
        }

        Some(current_module)
    }

    /// If self is root module, get the submodule at the `path` and returns it,
    /// or returns None if the path does not lead to anything
    pub fn goto_mut(&mut self, path: &EffectivePath) -> Option<&mut ModuleTree> {
        assert!(self.is_root());

        let mut iterator = path.as_slice().iter();

        let Some("orb") = iterator.next().map(|s| s.as_str()) else {
            return None;
        };

        let mut current_module = self;

        for member in iterator {
            current_module = current_module.submod_mut(member)?;
        }

        Some(current_module)
    }

    /// Get a definition in the current module tree
    pub fn def(&self, name: impl AsRef<str>) -> Option<Symbol> {
        self.defs.get(name.as_ref()).cloned()
    }

    /// Returns the symbol of the definition or the module with this name
    pub fn def_or_mod(&self, name: impl AsRef<str>) -> Option<Symbol> {
        self.def(&name)
            .or(self.submod(&name).map(|submod| submod.sym.unwrap_sym()))
    }
}
