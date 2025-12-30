//! Desugared Intermediate Representation of Lun.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::{collections::HashMap, fmt::Debug, fs, mem, path::PathBuf};

use diags::{
    ModuleFileDoesnotExist, NameDefinedMultipleTimes, NotFoundInScope, UnderscoreInExpression,
    UnderscoreReservedIdent,
};

use lunc_ast::{Abi, BinOp, ItemKind, Mutability, Path, PathSegment, Spanned, UnOp};
use lunc_diag::{Diagnostic, DiagnosticSink, FileId, ToDiagnostic, feature_todo};
use lunc_entity::{AnyId, Entity, EntityDb};
use lunc_lexer::Lexer;
use lunc_parser::{
    Parser,
    directive::Directive,
    expr::{Else, ExprKind, Expression, IfExpression, Param},
    item::{Item, Module},
    stmt::{Block, Statement, StmtKind},
};
use lunc_token::Lit;
use lunc_utils::{FromHigher, Span, lower, opt_unreachable};

pub use lunc_parser::directive::SpannedPath;

use crate::symbol::{EntityDbExt, LazySymbol, Symbol, SymbolKind};

pub mod diags;
pub mod pretty;
pub mod symbol;

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
    /// See [`GlobalDef`].
    ///
    /// [`GlobalDef`]: lunc_parser::item::Item::GlobalDef
    GlobalDef {
        name: Spanned<String>,
        mutability: Mutability,
        typeexpr: Option<DsExpression>,
        value: Box<DsExpression>,
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: LazySymbol,
    },
    /// See [`Item::GlobalUninit`]
    ///
    /// [`Item::GlobalUninit`]: lunc_parser::item::Item::GlobalUninit
    GlobalUninit {
        name: Spanned<String>,
        typeexpr: DsExpression,
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
        /// it will hold the ItemId of the UTIR later, we use this because
        /// ExternBlock doesn't have an item id.
        id: Option<AnyId>,
    },
    /// See [`Item::Directive`]
    ///
    /// [`Item::Directive`]: lunc_parser::item::Item::Directive
    Directive(DsDirective),
}

impl DsItem {
    /// Unwarps the location of the item
    pub fn loc(&self) -> Span {
        match self {
            DsItem::GlobalDef { loc, .. }
            | DsItem::GlobalUninit { loc, .. }
            | DsItem::Module { loc, .. }
            | DsItem::ExternBlock { loc, .. } => (*loc).unwrap(),
            DsItem::Directive(directive) => directive.loc(),
        }
    }

    pub fn kind(&self) -> ItemKind {
        match self {
            DsItem::GlobalDef { value, .. } if value.is_fundef() => ItemKind::Fundef,
            DsItem::GlobalDef { value, .. } if value.is_fundecl() => ItemKind::Fundecl,
            DsItem::GlobalDef { .. } => ItemKind::GlobalDef,
            DsItem::GlobalUninit { .. } => ItemKind::GlobalUninit,
            DsItem::Module { .. } => ItemKind::Module,
            DsItem::ExternBlock { .. } => ItemKind::ExternBlock,
            DsItem::Directive(_) => ItemKind::Directive,
        }
    }
}

/// See [`ItemDirective`]
///
/// [`ItemDirective`]: lunc_parser::directive::Directive
#[derive(Debug, Clone)]
pub enum DsDirective {
    Import {
        path: SpannedPath,
        alias: Option<String>,
        loc: OSpan,
    },
    /// NOTE: This directive will not be here after we pass the lowered DSIR to the desugarrer
    Mod { name: String, loc: OSpan },
}

impl DsDirective {
    pub fn loc(&self) -> Span {
        match self {
            DsDirective::Import { loc, .. } | DsDirective::Mod { loc, .. } => (*loc).unwrap(),
        }
    }
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
            Item::GlobalDef {
                name,
                mutability,
                typeexpr,
                value,
                loc,
            } => DsItem::GlobalDef {
                sym: LazySymbol::Path(Path::with_root(name.node.clone())),
                name,
                mutability,
                typeexpr: lower(typeexpr),
                value: Box::new(lower(value)),
                loc: Some(loc),
            },
            Item::GlobalUninit {
                name,
                typeexpr,
                loc,
            } => DsItem::GlobalUninit {
                sym: LazySymbol::Path(Path::with_root(name.node.clone())),
                name,
                typeexpr: lower(typeexpr),
                loc: Some(loc),
            },
            Item::ExternBlock { abi, items, loc } => DsItem::ExternBlock {
                abi,
                items: lower(items),
                loc: Some(loc),
                id: None,
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
    pub expr: DsExprKind,
    pub loc: OSpan,
}

impl DsExpression {
    /// Is the expression a function definition?
    pub fn is_fundef(&self) -> bool {
        matches!(self.expr, DsExprKind::FunDefinition { .. })
    }

    /// Is the expression a function declaration?
    pub fn is_fundecl(&self) -> bool {
        matches!(self.expr, DsExprKind::FunDeclaration { .. })
    }

    pub fn is_underscore(&self) -> bool {
        matches!(self.expr, DsExprKind::Underscore)
    }
}

impl FromHigher for DsExpression {
    type Higher = Expression;

    fn lower(node: Self::Higher) -> Self {
        let expr = match node.kind {
            ExprKind::Lit(lit) => DsExprKind::Lit(lit),
            ExprKind::BoolLit(b) => DsExprKind::BoolLit(b),
            // we remove the parenthesis we don't need them anymore
            ExprKind::Paren(e) => return lower(*e),
            ExprKind::Path(p) => DsExprKind::Path(LazySymbol::Path(p)),
            ExprKind::Binary { lhs, op, rhs } => DsExprKind::Binary {
                lhs: lower(lhs),
                op,
                rhs: lower(rhs),
            },
            ExprKind::Unary { op, expr } => DsExprKind::Unary {
                op,
                expr: lower(expr),
            },
            ExprKind::Borrow(mutability, expr) => DsExprKind::Borrow(mutability, lower(expr)),
            ExprKind::Call {
                callee: called,
                args,
            } => DsExprKind::Call {
                callee: lower(called),
                args: lower(args),
            },
            ExprKind::If(ifexpr) => lower_if_expression(ifexpr),
            ExprKind::IfThenElse {
                cond,
                true_val,
                false_val,
            } => DsExprKind::If {
                cond: lower(cond),
                then_br: lower(true_val),
                else_br: Some(lower(false_val)),
            },
            ExprKind::Block(block) => DsExprKind::Block {
                label: None,
                block: lower(block),
            },
            ExprKind::BlockWithLabel { label, block } => DsExprKind::Block {
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
            //     // body
            // }
            // ```
            //
            // NOTE: if you modify the desugaring of while expression, this
            // might break the detection of while expression in the SCIR in
            // file `lunc_untyped/src/lib.rs` in the function `gen_expr`
            ExprKind::PredicateLoop { label, cond, body } => {
                let mut stmts = Vec::with_capacity(body.stmts.len() + 1);

                stmts.push(stmt_expr(expr_if(
                    expr_unary(UnOp::Not, lower(*cond)),
                    expr_break(
                        label.clone().map(|Spanned { node: name, loc: _ }| name),
                        None,
                    ),
                    None,
                )));

                for stmt in body.stmts {
                    stmts.push(lower(stmt));
                }

                DsExprKind::Loop {
                    label: label.clone(),
                    body: block(body.loc, stmts, lower(body.last_expr)),
                }
            }
            ExprKind::IteratorLoop { loc, .. } => DsExprKind::Poisoned {
                diag: Some(feature_todo! {
                    feature: "iterator loop",
                    label: "traits and iterators aren't yet implemented",
                    loc: loc,
                }),
            },
            ExprKind::InfiniteLoop { label, body } => DsExprKind::Loop {
                label,
                body: lower(body),
            },
            ExprKind::Return { expr: val } => DsExprKind::Return { expr: lower(val) },
            ExprKind::Break { label, expr: val } => DsExprKind::Break {
                label,
                expr: lower(val),
            },
            ExprKind::Continue { label } => DsExprKind::Continue { label },
            ExprKind::Null => DsExprKind::Null,
            ExprKind::Field { expr, member } => DsExprKind::Field {
                expr: lower(expr),
                field: member,
            },
            ExprKind::FunDefinition {
                params,
                rettypeexpr,
                body,
            } => DsExprKind::FunDefinition {
                params: lower(params),
                rettypeexpr: lower(rettypeexpr),
                body: lower(body),
            },
            ExprKind::FunDeclaration {
                params: args,
                rettypeexpr,
            } => DsExprKind::FunDeclaration {
                args: lower(args),
                rettypeexpr: lower(rettypeexpr),
            },
            ExprKind::PointerType(mutability, typeexpr) => {
                DsExprKind::PointerType(mutability, lower(typeexpr))
            }
            ExprKind::FunPtrType { args, ret } => DsExprKind::FunPtrType {
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

pub fn lower_if_expression(ifexpr: IfExpression) -> DsExprKind {
    let then_b: DsBlock = lower(*ifexpr.body);

    DsExprKind::If {
        cond: lower(ifexpr.cond),
        then_br: Box::new(DsExpression {
            loc: then_b.loc,
            expr: expr_block(then_b.loc, then_b).expr,
        }),
        else_br: match ifexpr.else_br.map(|e| *e) {
            Some(Else::IfExpr(ifexp)) => Some(Box::new(DsExpression {
                loc: Some(ifexp.loc),
                expr: lower_if_expression(ifexp),
            })),
            Some(Else::Block(block)) => Some(Box::new(DsExpression {
                loc: Some(block.loc),
                expr: expr_block(block.loc, lower(block)).expr,
            })),
            None => None,
        },
    }
}

/// A desugared expression internal, see the sweet version [`ExprKind`]
///
/// [`ExprKind`]: lunc_parser::expr::ExprKind
#[derive(Debug, Clone)]
pub enum DsExprKind {
    /// See [`ExprKind::Lit`]
    ///
    /// [`ExprKind::Lit`]: lunc_parser::expr::ExprKind::Lit
    Lit(Lit),
    /// See [`ExprKind::BoolLit`]
    ///
    /// [`ExprKind::BoolLit`]: lunc_parser::expr::ExprKind::BoolLit
    BoolLit(bool),
    /// See [`ExprKind::Path`]
    ///
    /// [`ExprKind::Path`]: lunc_parser::expr::ExprKind::Path
    Path(LazySymbol),
    /// See [`ExprKind::Binary`]
    ///
    /// [`ExprKind::Binary`]: lunc_parser::expr::ExprKind::Binary
    Binary {
        lhs: Box<DsExpression>,
        op: BinOp,
        rhs: Box<DsExpression>,
    },
    /// See [`ExprKind::Unary`]
    ///
    /// [`ExprKind::Unary`]: lunc_parser::expr::ExprKind::Unary
    Unary { op: UnOp, expr: Box<DsExpression> },
    /// See [`ExprKind::Borrow`]
    ///
    /// [`ExprKind::Borrow`]: lunc_parser::expr::ExprKind::Borrow
    Borrow(Mutability, Box<DsExpression>),
    /// See [`ExprKind::Call`]
    ///
    /// [`ExprKind::Call`]: lunc_parser::expr::ExprKind::Call
    Call {
        callee: Box<DsExpression>,
        args: Vec<DsExpression>,
    },
    /// See [`ExprKind::If`] and [`ExprKind::IfThenElse`]
    ///
    /// [`ExprKind::If`]: lunc_parser::expr::ExprKind::If
    /// [`ExprKind::IfThenElse`]: lunc_parser::expr::ExprKind::IfThenElse
    If {
        cond: Box<DsExpression>,
        then_br: Box<DsExpression>,
        else_br: Option<Box<DsExpression>>,
    },
    /// See [`ExprKind::Block`]
    ///
    /// [`ExprKind::Block`]: lunc_parser::expr::ExprKind::Block
    Block {
        label: Option<Spanned<String>>,
        block: DsBlock,
    },
    /// See [`ExprKind::InfiniteLoop`], [`ExprKind::IteratorLoop`] and [`ExprKind::PredicateLoop`].
    ///
    /// [`ExprKind::InfiniteLoop`]: lunc_parser::expr::ExprKind::InfiniteLoop
    /// [`ExprKind::IteratorLoop`]: lunc_parser::expr::ExprKind::IteratorLoop
    /// [`ExprKind::PredicateLoop`]: lunc_parser::expr::ExprKind::PredicateLoop
    Loop {
        label: Option<Spanned<String>>,
        body: DsBlock,
    },
    /// See [`ExprKind::Return`]
    ///
    /// [`ExprKind::Return`]: lunc_parser::expr::ExprKind::Return
    Return { expr: Option<Box<DsExpression>> },
    /// See [`ExprKind::Break`]
    ///
    /// [`ExprKind::Break`]: lunc_parser::expr::ExprKind::Break
    Break {
        label: Option<String>,
        expr: Option<Box<DsExpression>>,
    },
    /// See [`ExprKind::Continue`]
    ///
    /// [`ExprKind::Continue`]: lunc_parser::expr::ExprKind::Continue
    Continue { label: Option<String> },
    /// See [`ExprKind::Null`]
    ///
    /// [`ExprKind::Null`]: lunc_parser::expr::ExprKind::Null
    Null,
    /// See [`ExprKind::Field`]
    ///
    /// [`ExprKind::Field`]: lunc_parser::expr::ExprKind::Field
    Field {
        expr: Box<DsExpression>,
        field: String,
    },
    /// Constructed from the lazy path `_`, but only in certain cases, like when
    /// it's part of an assignment like so: `_ = expr`
    Underscore,
    /// See [`ExprKind::FunDefinition`]
    ///
    /// [`ExprKind::FunDefinition`]: lunc_parser::expr::ExprKind::FunDefinition
    FunDefinition {
        params: Vec<DsParam>,
        rettypeexpr: Option<Box<DsExpression>>,
        body: DsBlock,
    },
    /// See [`ExprKind::FunDeclaration`]
    ///
    /// [`ExprKind::FunDeclaration`]: lunc_parser::expr::ExprKind::FunDeclaration
    FunDeclaration {
        args: Vec<DsExpression>,
        rettypeexpr: Option<Box<DsExpression>>,
    },
    /// See [`ExprKind::PointerType`]
    ///
    /// [`ExprKind::PointerType`]: lunc_parser::expr::ExprKind::PointerType
    PointerType(Mutability, Box<DsExpression>),
    /// See [`ExprKind::FunPtrType`]
    ///
    /// [`ExprKind::FunPtrType`]: lunc_parser::expr::ExprKind::FunPtrType
    FunPtrType {
        args: Vec<DsExpression>,
        ret: Option<Box<DsExpression>>,
    },
    /// This is a special node, it holds a diagnostic and is emitted in lowering
    /// (ast -> dsir) to emit error instead of panic.
    ///
    /// # Note
    ///
    /// The field `diag` must be set to `Some(..)` when you emit this node and
    /// when we perform checking the diagnostic must be emitted asap.
    Poisoned { diag: Option<Diagnostic> },
}

impl DsExprKind {
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
        expr: DsExprKind::Lit(Lit::int(i.into())),
        loc: None,
    }
}

/// Creates an boolean expression without location.
pub fn expr_bool(b: bool) -> DsExpression {
    DsExpression {
        expr: DsExprKind::BoolLit(b),
        loc: None,
    }
}

/// Creates an string expression without location.
pub fn expr_string(str: impl ToString) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Lit(Lit::string(str.to_string())),
        loc: None,
    }
}

/// Creates an character expression without location.
pub fn expr_char(c: impl Into<char>) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Lit(Lit::char(c.into())),
        loc: None,
    }
}

/// Creates an character expression without location.
pub fn expr_float(f: f64) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Lit(Lit::float(f)),
        loc: None,
    }
}

/// Creates an ident expression without location.
pub fn expr_path(path: impl IntoIterator<Item = PathSegment>) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Path(LazySymbol::Path(Path::from_iter(path))),
        loc: None,
    }
}

/// Creates a binary expression without location.
pub fn expr_binary(lhs: DsExpression, op: BinOp, rhs: DsExpression) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Binary {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        },
        loc: None,
    }
}

/// Creates a unary expression without location.
pub fn expr_unary(op: UnOp, expr: DsExpression) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Unary {
            op,
            expr: Box::new(expr),
        },
        loc: None,
    }
}

/// Creates an address of expression without location.
pub fn expr_borrow(mutability: Mutability, val: DsExpression) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Borrow(mutability, Box::new(val)),
        loc: None,
    }
}

/// Creates a function call expression without location.
pub fn expr_funcall(
    called: DsExpression,
    args: impl Iterator<Item = DsExpression>,
) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Call {
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
        expr: DsExprKind::If {
            cond: Box::new(cond),
            then_br: Box::new(then_br),
            else_br: else_br.into().map(Box::new),
        },
        loc: None,
    }
}

/// Creates a block expression without location.
pub fn expr_block(loc: impl Into<OSpan>, block: DsBlock) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Block { label: None, block },
        loc: loc.into(),
    }
}

/// Creates a loop expression without location.
pub fn expr_loop(label: Option<Spanned<String>>, body: DsBlock) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Loop { label, body },
        loc: None,
    }
}

/// Creates a return expression without location.
pub fn expr_return(val: impl Into<Option<DsExpression>>) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Return {
            expr: val.into().map(Box::new),
        },
        loc: None,
    }
}

/// Creates a break expression without location.
pub fn expr_break(label: Option<String>, val: impl Into<Option<DsExpression>>) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Break {
            label,
            expr: val.into().map(Box::new),
        },
        loc: None,
    }
}

/// Creates a continue expression without location.
pub fn expr_continue(label: Option<String>) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Continue { label },
        loc: None,
    }
}

/// Creates a null expression without location.
pub fn expr_null() -> DsExpression {
    DsExpression {
        expr: DsExprKind::Null,
        loc: None,
    }
}

/// Creates a member access expression without location.
pub fn expr_member_access(expr: DsExpression, member: impl ToString) -> DsExpression {
    DsExpression {
        expr: DsExprKind::Field {
            expr: Box::new(expr),
            field: member.to_string(),
        },
        loc: None,
    }
}

/// Creates a function definition expression without location.
pub fn expr_fundef(
    params: Vec<DsParam>,
    rettypeexpr: impl Into<Option<DsExpression>>,
    body: DsBlock,
) -> DsExpression {
    DsExpression {
        expr: DsExprKind::FunDefinition {
            params,
            rettypeexpr: rettypeexpr.into().map(Box::new),
            body,
        },
        loc: None,
    }
}

/// Creates a pointer type expression without location.
pub fn expr_ptr_type(mutability: Mutability, typeexpr: DsExpression) -> DsExpression {
    DsExpression {
        expr: DsExprKind::PointerType(mutability, Box::new(typeexpr)),
        loc: None,
    }
}

/// Creates a function pointer type expression without location.
pub fn expr_fun_ptr_type(
    args: Vec<DsExpression>,
    ret: impl Into<Option<DsExpression>>,
) -> DsExpression {
    DsExpression {
        expr: DsExprKind::FunPtrType {
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
    pub stmt: DsStmtKind,
    pub loc: OSpan,
}

impl FromHigher for DsStatement {
    type Higher = Statement;

    fn lower(node: Self::Higher) -> Self {
        let stmt = match node.stmt {
            StmtKind::BindingDef {
                name,
                mutability,
                typeexpr,
                value,
            } => DsStmtKind::BindingDef {
                sym: LazySymbol::Path(Path::with_root(name.node.clone())),
                name,
                mutability,
                typeexpr: lower(typeexpr),
                value: lower(value),
            },
            StmtKind::Defer { expr } => DsStmtKind::Defer { expr: lower(expr) },
            StmtKind::Expression(expr) => DsStmtKind::Expression(lower(expr)),
        };

        DsStatement {
            stmt,
            loc: Some(node.loc),
        }
    }
}

#[derive(Debug, Clone)]
pub enum DsStmtKind {
    /// See [`StmtKind::BindingDef`]
    ///
    /// [`StmtKind::BindingDef`]: lunc_parser::stmt::StmtKind::BindingDef
    BindingDef {
        name: Spanned<String>,
        mutability: Mutability,
        typeexpr: Option<DsExpression>,
        value: Box<DsExpression>,
        sym: LazySymbol,
    },
    /// See [`StmtKind::Defer`]
    ///
    /// [`StmtKind::Defer`]: lunc_parser::stmt::StmtKind::Defer
    Defer { expr: DsExpression },
    /// See [`StmtKind::Expression`]
    ///
    /// [`StmtKind::Expression`]: lunc_parser::stmt::StmtKind::Expression
    Expression(DsExpression),
}

/// Creates an expression statement without location.
pub fn stmt_expr(expr: DsExpression) -> DsStatement {
    DsStatement {
        stmt: DsStmtKind::Expression(expr),
        loc: None,
    }
}

/// A desugared argument, see the sweet version [`Param`]
///
/// [`Param`]: lunc_parser::expr::Param
#[derive(Debug, Clone)]
pub struct DsParam {
    pub name: Spanned<String>,
    pub typeexpr: DsExpression,
    pub loc: OSpan,
    pub sym: LazySymbol,
}

impl FromHigher for DsParam {
    type Higher = Param;

    fn lower(node: Self::Higher) -> Self {
        let Param {
            name,
            typeexpr,
            loc,
        } = node;

        DsParam {
            sym: LazySymbol::Path(Path::with_root(name.node.clone())),
            name,
            typeexpr: lower(typeexpr),
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
    current_path: Path,
    /// symbol database
    symdb: EntityDb<Symbol>,
}

impl Desugarrer {
    /// Create a new desugarrer.
    pub fn new(sink: DiagnosticSink, orb_name: impl ToString) -> Desugarrer {
        let mut ds = Desugarrer {
            sink,
            table: SymbolTable::new(),
            orb: ModuleTree::new(
                Some(orb_name.to_string()),
                LazySymbol::Path(Path::with_root("orb".to_string())),
            ),
            current_path: Path::with_root(PathSegment::Orb),
            symdb: EntityDb::new(),
        };

        let first = SymbolMap::first_scope(&mut ds);
        ds.table.tabs.push(first);

        ds
    }

    /// Get the orb name
    pub fn orb_name(&self) -> &str {
        self.orb.root_name().unwrap()
    }

    /// Bind a name to a symbol in the current scope, returns a diagnostic if name == `_`
    pub fn bind(&mut self, name: String, sym: Symbol) -> Result<(), Diagnostic> {
        let symdata = self.symdb.get(sym);
        let skind = symdata.kind.clone();

        if let Some(previous_sym) = self.table.lookup(&name).map(|s| self.symdb.get(s))
            && !skind.can_shadow(&previous_sym.kind)
        {
            return Err(NameDefinedMultipleTimes {
                name: &name,
                loc_previous: previous_sym.loc,
                loc: symdata.loc,
            }
            .into_diag());
        }

        match skind {
            SymbolKind::UserBinding { .. } => {
                self.table.last_map_mut().usr_binding_count += 1;
            }
            SymbolKind::Param => {
                self.table.last_map_mut().param_count += 1;
            }
            SymbolKind::PrimitiveType | SymbolKind::GlobalDef { .. } => {
                self.table.last_map_mut().global_count += 1;
            }
            SymbolKind::Function => {
                self.table.last_map_mut().fun_count += 1;
            }
            SymbolKind::Module => {
                self.table.last_map_mut().mod_count += 1;
            }
        }

        if name.as_str() == "_" {
            return Err(UnderscoreReservedIdent { loc: symdata.loc }.into_diag());
        }

        self.table.last_map_mut().map.insert(name, sym);

        Ok(())
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

        Some(module)
    }

    /// Returns the produce Orb-tree, it replaces the module tree with a dummy one.
    pub fn take_orb_tree(&mut self) -> ModuleTree {
        mem::replace(
            &mut self.orb,
            ModuleTree::new(None, LazySymbol::Sym(Symbol::RESERVED)),
        )
    }

    /// Returns the entity database of symbols, replaces it with a dummy one.
    pub fn take_symdb(&mut self) -> EntityDb<Symbol> {
        mem::replace(&mut self.symdb, EntityDb::new())
    }

    /// Takes a module and converts (recursively) the Mod directive to Item Mod.
    ///
    /// So in this function, we:
    /// 1. look for the file that corresponds to the module name
    /// 2. lex this file
    /// 3. parse this token stream
    /// 4. desugar this ast
    /// 5. put the items of the module inside the parent module, in a `DsItem::Module`
    ///
    /// # Note
    ///
    /// We are inlining module directives in EVERY item container even tho the
    /// only accepted item container for it is a module it self, because we get
    /// rid of the directive when we convert it to SCIR. The diagnostic about
    /// module not being in a module is emitted in the SCIR.
    pub fn inline_modules(&mut self, parent: &mut DsModule) {
        let parent_path = PathBuf::from(self.sink.name(parent.fid).unwrap());

        self.inline_modules_in_item_container(&mut parent.items, parent.fid, parent_path);
    }

    fn inline_modules_in_item_container(
        &mut self,
        items: &mut Vec<DsItem>,
        parent_fid: FileId,
        parent_path: PathBuf,
    ) {
        for item in items {
            match item {
                DsItem::Directive(DsDirective::Mod { name, loc }) => {
                    // 1. compute the path of the submodule
                    let submodule_path = if parent_fid.is_root() {
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
                            loc: (*loc).unwrap(),
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
                    let mut lexer =
                        Lexer::new(self.sink.clone(), source_code.clone(), submodule_fid);
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
                        loc: *loc,
                        sym: LazySymbol::Path(Path::with_root(name.clone())),
                    };
                }
                DsItem::ExternBlock { items, .. } => {
                    self.inline_modules_in_item_container(items, parent_fid, parent_path.clone());
                }
                _ => {}
            }
        }
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
    pub fn resolve_module(&mut self, module: &mut DsModule, resolve_path: Path) {
        self.table.scope_enter(); // module scope

        self.bind_global_defs(&mut module.items, resolve_path);

        for item in &mut module.items {
            match self.resolve_item(item) {
                Ok(()) => {}
                Err(d) => {
                    self.sink.emit(d);
                }
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
                *self.current_path.last_mut().unwrap() = PathSegment::Ident(name.clone());

                self.resolve_module(submod, self.current_path.clone());
            }
        }
    }

    /// Resolve names of an item
    pub fn resolve_item(&mut self, item: &mut DsItem) -> Result<(), Diagnostic> {
        match item {
            DsItem::GlobalDef {
                typeexpr, value, ..
            } => {
                if let Some(typeexpr) = typeexpr {
                    self.resolve_expr(typeexpr)?;
                }

                self.resolve_expr(value)?;

                Ok(())
            }
            DsItem::GlobalUninit { typeexpr, .. } => {
                self.resolve_expr(typeexpr)?;

                Ok(())
            }
            DsItem::ExternBlock {
                abi: _,
                items,
                loc: _,
                id: _,
            } => {
                for item in items {
                    match self.resolve_item(item) {
                        Ok(()) => {}
                        Err(d) => {
                            self.sink.emit(d);
                        }
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
                Err(d) => {
                    self.sink.emit(d);
                }
            }
        }

        if let Some(expr) = &mut block.last_expr {
            match self.resolve_expr(expr) {
                Ok(()) => {}
                Err(d) => {
                    self.sink.emit(d);
                }
            }
        }

        self.table.scope_exit(); // block scope
    }

    /// Resolve statement
    pub fn resolve_stmt(&mut self, stmt: &mut DsStatement) -> Result<(), Diagnostic> {
        match &mut stmt.stmt {
            DsStmtKind::BindingDef {
                name,
                mutability,
                typeexpr,
                value,
                sym,
            } => {
                match (|| -> Result<(), Diagnostic> {
                    if let Some(typeexpr) = typeexpr {
                        self.resolve_expr(typeexpr)?;
                    }
                    self.resolve_expr(value)?;

                    Ok(())
                })() {
                    Ok(()) => {}
                    Err(d) => {
                        self.sink.emit(d);
                    }
                }

                let symref = self.symdb.create_user_binding(
                    *mutability,
                    name.node.clone(),
                    self.table.usr_binding_count(),
                    name.loc,
                );

                *sym = LazySymbol::Sym(symref);

                self.bind(name.node.clone(), symref)?;

                Ok(())
            }
            DsStmtKind::Defer { expr } | DsStmtKind::Expression(expr) => self.resolve_expr(expr),
        }
    }

    /// Resolve expression
    pub fn resolve_expr(&mut self, expr: &mut DsExpression) -> Result<(), Diagnostic> {
        match &mut expr.expr {
            DsExprKind::BoolLit(_) | DsExprKind::Lit(_) => Ok(()),
            DsExprKind::Binary {
                lhs,
                op: BinOp::Assignment,
                rhs,
            } if matches!(&lhs.expr, DsExprKind::Path(LazySymbol::Path(path)) if path.is_underscore()) =>
            {
                // we allow _ in lhs of assignment
                lhs.expr = DsExprKind::Underscore;
                self.resolve_expr(rhs)
            }
            DsExprKind::Binary { lhs, op: _, rhs } => {
                self.resolve_expr(lhs)?;
                self.resolve_expr(rhs)
            }
            DsExprKind::Unary { op: _, expr } | DsExprKind::Borrow(_, expr) => {
                self.resolve_expr(expr)
            }
            DsExprKind::Call { callee, args } => {
                self.resolve_expr(callee)?;

                for arg in args {
                    self.resolve_expr(arg)?;
                }

                Ok(())
            }
            DsExprKind::If {
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
            DsExprKind::Block { label, block } | DsExprKind::Loop { label, body: block } => {
                _ = label;

                self.resolve_block(block);

                Ok(())
            }
            DsExprKind::Return { expr } | DsExprKind::Break { label: _, expr } => {
                if let Some(expr) = expr {
                    self.resolve_expr(expr)?;
                }

                Ok(())
            }
            DsExprKind::Continue { label: _ } | DsExprKind::Null => Ok(()),
            DsExprKind::PointerType(_, typeexpr) => self.resolve_expr(typeexpr),
            DsExprKind::FunPtrType { args, ret } => {
                for arg in args {
                    self.resolve_expr(arg)?;
                }

                if let Some(ret) = ret {
                    self.resolve_expr(ret)?;
                }

                Ok(())
            }
            DsExprKind::Path(LazySymbol::Path(path)) => {
                if path.is_underscore() {
                    return Err(UnderscoreInExpression {
                        loc: expr.loc.unwrap(),
                    }
                    .into_diag());
                }

                // path of the module (without the last segment)
                let mut mod_path = path.clone();
                let def_name = mod_path.pop().map(|seg| seg.to_string());

                // absolute version of the `mod_path`.
                let mut abs_mod_path = self.current_path.clone();
                abs_mod_path.append(mod_path.clone());

                if path.len() == 1
                    && let Some(PathSegment::Ident(name)) = path.get(0).cloned()
                    && let Some(symref) = self.table.lookup(&name)
                {
                    // a simple one segment path, just search in the symbol
                    // table if we find something appropriate
                    expr.expr = DsExprKind::Path(LazySymbol::Sym(symref));

                    Ok(())
                } else if let Some(module) = self.orb.goto(&mod_path)
                    && let Some(name) = &def_name
                    && let Some(symref) = module.def_or_mod(name)
                {
                    // absolute path to a definition of the orb tree.
                    expr.expr = DsExprKind::Path(LazySymbol::Sym(symref));

                    Ok(())
                } else if let Some(module) = self.orb.goto(&abs_mod_path)
                    && let Some(name) = &def_name
                    && let Some(symref) = module.def_or_mod(name)
                {
                    // relative path to a definition of the module but doesn't
                    // take in charge import aliases.
                    //
                    // In theory this is a peephole optimization to search
                    // without thinking about import aliases.
                    expr.expr = DsExprKind::Path(LazySymbol::Sym(symref));

                    Ok(())
                } else if let Some(first) = mod_path.first()
                    && let Some(search_path) = self
                        .table
                        .lookup(first.to_string())
                        .map(|sym| self.symdb.get(sym).path.clone())
                    && let Some(module) = self.orb.goto(&search_path)
                    && let Some(name) = &def_name
                    && let Some(symref) = module.def_or_mod(name)
                {
                    // relative path to a definition with the first segment that
                    // may be an import alias.
                    expr.expr = DsExprKind::Path(LazySymbol::Sym(symref));

                    Ok(())
                } else {
                    // path not found.
                    Err(NotFoundInScope {
                        name: path.to_string(),
                        loc: expr.loc.unwrap(),
                    }
                    .into_diag())
                }
            }
            DsExprKind::Path(LazySymbol::Sym(_)) | DsExprKind::Underscore => {
                // SAFETY: they cannot be reached because they are constructed
                // in this method, its an internal error if it is reached, so
                // we panic.
                opt_unreachable!()
            }
            DsExprKind::Field {
                expr: exp,
                field: _,
            } => {
                self.resolve_expr(&mut *exp)?;

                Ok(())
            }
            DsExprKind::FunDefinition {
                params,
                rettypeexpr,
                body,
            } => {
                self.table.scope_enter(); // fundef scope

                for DsParam {
                    name,
                    typeexpr,
                    loc: _,
                    sym,
                } in params
                {
                    match self.resolve_expr(typeexpr) {
                        Ok(()) => {}
                        Err(d) => {
                            self.sink.emit(d);
                        }
                    }

                    let symref = self.symdb.create_param(
                        name.node.clone(),
                        self.table.param_count(),
                        name.loc,
                    );

                    *sym = LazySymbol::Sym(symref);

                    self.bind(name.node.clone(), symref)?;
                }

                if let Some(retty) = rettypeexpr {
                    self.resolve_expr(retty)?;
                }

                self.resolve_block(body);

                self.table.scope_exit(); // fundef scope

                Ok(())
            }
            DsExprKind::FunDeclaration { args, rettypeexpr } => {
                for arg in args {
                    match self.resolve_expr(arg) {
                        Ok(()) => {}
                        Err(d) => {
                            self.sink.emit(d);
                        }
                    }
                }

                if let Some(retty) = rettypeexpr {
                    self.resolve_expr(retty)?;
                }

                Ok(())
            }
            DsExprKind::Poisoned { diag } => {
                self.sink.emit(diag.take().unwrap());

                Ok(())
            }
        }
    }

    /// Bind all the global definitions before resolving recursively the dsir
    pub fn bind_global_defs(&mut self, items: &mut [DsItem], resolve_path: Path) {
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
    fn bind_global_def(&mut self, item: &mut DsItem, resolve_path: Path) -> Result<(), Diagnostic> {
        match item {
            DsItem::GlobalDef {
                name,
                mutability: _,
                typeexpr: _,
                value,
                loc: _,
                sym,
            } if value.expr.is_fundef() || value.expr.is_fundecl() => {
                let mut path = self.current_path.clone();
                path.push(name.node.clone());

                let symref = sym.symbol().unwrap_or_else(|| {
                    self.symdb
                        .create_function(name.node.clone(), path, name.loc)
                });

                self.orb
                    .goto_mut(&self.current_path)
                    .unwrap()
                    .define(name.node.clone(), symref);

                *sym = LazySymbol::Sym(symref);

                if self.current_path == resolve_path {
                    match self.bind(name.node.clone(), symref) {
                        Ok(()) => {}
                        Err(d) => {
                            self.sink.emit(d);
                        }
                    }
                }

                Ok(())
            }
            DsItem::GlobalDef {
                name,
                mutability,
                typeexpr: _,
                value: _,
                loc: _,
                sym,
            } => {
                let mut path = self.current_path.clone();
                path.push(name.node.clone());

                let symref = sym.symbol().unwrap_or_else(|| {
                    self.symdb
                        .create_global_def(*mutability, name.node.clone(), path, name.loc)
                });

                self.orb
                    .goto_mut(&self.current_path)
                    .unwrap()
                    .define(name.node.clone(), symref);

                *sym = LazySymbol::Sym(symref);

                if self.current_path == resolve_path {
                    match self.bind(name.node.clone(), symref) {
                        Ok(()) => {}
                        Err(d) => {
                            self.sink.emit(d);
                        }
                    }
                }

                Ok(())
            }
            DsItem::GlobalUninit {
                name,
                typeexpr: _,
                loc: _,
                sym,
            } => {
                let mut path = self.current_path.clone();
                path.push(name.node.clone());

                let symref = sym.symbol().unwrap_or_else(|| {
                    self.symdb
                        .create_global_def(Mutability::Mut, name.node.clone(), path, name.loc)
                });

                self.orb
                    .goto_mut(&self.current_path)
                    .unwrap()
                    .define(name.node.clone(), symref);

                *sym = LazySymbol::Sym(symref);

                if self.current_path == resolve_path {
                    match self.bind(name.node.clone(), symref) {
                        Ok(()) => {}
                        Err(d) => {
                            self.sink.emit(d);
                        }
                    }
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

                let symref = sym.symbol().unwrap_or_else(|| {
                    self.symdb
                        .create_module(name.clone(), path, (*loc).unwrap())
                });

                *sym = LazySymbol::Sym(symref);

                self.orb
                    .goto_mut(&self.current_path)
                    .unwrap()
                    .define_mod(name.clone(), symref);

                if self.current_path == resolve_path {
                    match self.bind(name.clone(), symref) {
                        Ok(()) => {}
                        Err(d) => {
                            self.sink.emit(d);
                        }
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
                id: _,
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
                let mut mod_path = path.node.clone();

                let name = mod_path.pop().unwrap();

                if let Some(module) = self.orb.goto(&mod_path)
                    && let Some(symref) = module.def_or_mod(name.to_string())
                {
                    self.bind(alias.clone().unwrap_or(name.to_string()), symref)
                } else {
                    Err(NotFoundInScope {
                        name: path.node.to_string(),
                        loc: path.loc,
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
    usr_binding_count: usize,
    param_count: usize,
    mod_count: usize,
}

impl SymbolMap {
    pub fn new() -> SymbolMap {
        SymbolMap {
            map: HashMap::new(),
            fun_count: 0,
            global_count: 0,
            usr_binding_count: 0,
            param_count: 0,
            mod_count: 0,
        }
    }

    pub fn first_scope(ds: &mut Desugarrer) -> SymbolMap {
        SymbolMap {
            map: HashMap::from([
                ("isz".to_string(), ds.symdb.create_primitive_type("isz")),
                ("i128".to_string(), ds.symdb.create_primitive_type("i128")),
                ("i64".to_string(), ds.symdb.create_primitive_type("i64")),
                ("i32".to_string(), ds.symdb.create_primitive_type("i32")),
                ("i16".to_string(), ds.symdb.create_primitive_type("i16")),
                ("i8".to_string(), ds.symdb.create_primitive_type("i8")),
                ("usz".to_string(), ds.symdb.create_primitive_type("usz")),
                ("u128".to_string(), ds.symdb.create_primitive_type("u128")),
                ("u64".to_string(), ds.symdb.create_primitive_type("u64")),
                ("u32".to_string(), ds.symdb.create_primitive_type("u32")),
                ("u16".to_string(), ds.symdb.create_primitive_type("u16")),
                ("u8".to_string(), ds.symdb.create_primitive_type("u8")),
                ("f16".to_string(), ds.symdb.create_primitive_type("f16")),
                ("f32".to_string(), ds.symdb.create_primitive_type("f32")),
                ("f64".to_string(), ds.symdb.create_primitive_type("f64")),
                ("f128".to_string(), ds.symdb.create_primitive_type("f128")),
                ("bool".to_string(), ds.symdb.create_primitive_type("bool")),
                ("str".to_string(), ds.symdb.create_primitive_type("str")),
                ("char".to_string(), ds.symdb.create_primitive_type("char")),
                ("never".to_string(), ds.symdb.create_primitive_type("never")),
                ("void".to_string(), ds.symdb.create_primitive_type("void")),
                (
                    "orb".to_string(),
                    // NOTE: here we can set the loc to be 0..0 into the root
                    // file, its fine ig, a span from the first character to eof
                    // would be better but this works
                    ds.symdb.create_module(
                        "orb".to_string(),
                        Path::with_root(ds.orb_name()),
                        Span::ZERO,
                    ),
                ),
            ]),
            fun_count: 0,
            global_count: 0,
            usr_binding_count: 0,
            param_count: 0,
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
        SymbolTable { tabs: Vec::new() }
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
                return Some(*symref);
            }
        }

        None
    }

    /// Returns the UserBinding count of the last symbol map
    pub fn usr_binding_count(&self) -> usize {
        self.last_map().usr_binding_count
    }

    /// Returns the Param count of the last symbol map
    pub fn param_count(&self) -> usize {
        self.last_map().param_count
    }

    /// Returns the GlobalDef count of the last symbol map
    pub fn global_def_count(&self) -> usize {
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
        self.defs.insert(name, sym);
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
    pub fn goto(&self, path: &Path) -> Option<&ModuleTree> {
        assert!(self.is_root());

        let mut iterator = path.as_slice().iter();

        let Some(PathSegment::Orb) = iterator.next() else {
            return None;
        };

        let mut current_module = self;

        for member in iterator {
            current_module = current_module.submod(member.to_string())?;
        }

        Some(current_module)
    }

    /// If self is root module, get the submodule at the `path` and returns it,
    /// or returns None if the path does not lead to anything
    pub fn goto_mut(&mut self, path: &Path) -> Option<&mut ModuleTree> {
        assert!(self.is_root());

        let mut iterator = path.as_slice().iter();

        let Some(PathSegment::Orb) = iterator.next() else {
            return None;
        };

        let mut current_module = self;

        for member in iterator {
            current_module = current_module.submod_mut(member.to_string())?;
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

    /// Gets the name of the root module if any.
    pub fn root_name(&self) -> Option<&str> {
        self.root_name.as_deref()
    }
}
