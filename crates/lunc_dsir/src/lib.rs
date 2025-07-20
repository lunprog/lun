//! Desugared Intermediate Representation of Lun.

use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    fs,
    hint::unreachable_unchecked,
    ops::Deref,
    path::PathBuf,
    sync::{Arc, RwLock},
};

use diags::{
    ModuleFileDoesnotExist, NameDefinedMultipleTimes, NotFoundInScope, UnderscoreInExpression,
    UnderscoreReservedIdent,
};
use lunc_diag::{Diagnostic, DiagnosticSink, FileId, ToDiagnostic};
use lunc_lexer::Lexer;
use lunc_parser::{
    Parser,
    directive::{EffectivePath, ItemDirective, QualifiedPath},
    expr::{Arg, Else, Expr, Expression, IfExpression},
    item::{Item, Module},
    stmt::{Block, Statement, Stmt},
};
use lunc_utils::{FromHigher, lower};

pub use lunc_parser::expr::{BinOp, UnaryOp};

pub mod diags;
pub mod pretty;

/// Optional span, used because when we desugar we are creating new nodes, so
/// there is no location for them.
///
/// # Note:
///
/// It's fine to unwrap because if we need to get the loc of a node it's to emit
/// a diagnostic and the desugaring should never make errors.
pub type Span = Option<lunc_utils::Span>;

/// A maybe not yet evaluated Symbol
#[derive(Debug, Clone)]
pub enum LazySymbol {
    Name(String),
    Sym(SymbolRef),
}

impl From<String> for LazySymbol {
    fn from(value: String) -> Self {
        LazySymbol::Name(value)
    }
}

impl From<SymbolRef> for LazySymbol {
    fn from(value: SymbolRef) -> Self {
        LazySymbol::Sym(value)
    }
}

/// A reference to a symbol, used to mutate symbols during resolution,
/// everywhere both in SymbolTable and in the DSIR
///
/// # Note
///
/// This type is a wrapper of Arc so a clone of this type is very cheap.
#[repr(transparent)]
#[derive(Debug, Clone)]
pub struct SymbolRef(Arc<RwLock<Symbol>>);

impl SymbolRef {
    pub fn new(
        kind: SymKind,
        name: String,
        which: usize,
        path: EffectivePath,
        loc: Span,
    ) -> SymbolRef {
        SymbolRef(Arc::new(RwLock::new(Symbol {
            kind,
            name,
            which,
            path,
            loc,
        })))
    }

    pub fn local(mutable: bool, name: String, which: usize, loc: Span) -> SymbolRef {
        SymbolRef::new(
            SymKind::Local { mutable },
            name.clone(),
            which,
            EffectivePath::with_root_member(name),
            loc,
        )
    }

    pub fn arg(name: String, which: usize, loc: Span) -> SymbolRef {
        SymbolRef::new(
            SymKind::Arg,
            name.clone(),
            which,
            EffectivePath::with_root_member(name),
            loc,
        )
    }

    pub fn global(
        mutable: bool,
        name: String,
        which: usize,
        path: EffectivePath,
        loc: Span,
    ) -> SymbolRef {
        SymbolRef::new(SymKind::Global { mutable }, name, which, path, loc)
    }

    pub fn function(name: String, which: usize, path: EffectivePath, loc: Span) -> SymbolRef {
        SymbolRef::new(SymKind::Function, name, which, path, loc)
    }

    pub fn module(name: String, which: usize, path: EffectivePath, loc: Span) -> SymbolRef {
        SymbolRef::new(SymKind::Module, name, which, path, loc)
    }
}

impl Deref for SymbolRef {
    type Target = Arc<RwLock<Symbol>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A symbol
#[derive(Debug, Clone)]
pub struct Symbol {
    /// kind of symbol
    pub kind: SymKind,
    /// name when defined, it's not the full path
    pub name: String,
    /// (can't be explained easily)
    ///
    /// eg:
    /// - for a function the `which` of the first argument is 0, the second is 1
    /// - for a variable the `which` is set to 0 for the first variable, 1 for the
    ///   second etc..
    /// - for a global and a function this field is not really relevant, but is
    ///   still populated
    pub which: usize,
    /// the absolute path to the symbol
    pub path: EffectivePath,
    /// location of the identifier defining this symbol
    pub loc: Span,
}

/// The kind of symbol
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymKind {
    /// Local variable
    Local { mutable: bool },
    /// Argument
    Arg,
    /// Global
    Global { mutable: bool },
    /// Function
    Function,
    /// Module
    Module,
}

impl SymKind {
    pub fn is_global_def(&self) -> bool {
        matches!(self, Self::Global { .. } | Self::Function | Self::Module)
    }
}

impl Display for SymKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymKind::Local { .. } => f.write_str("local"),
            SymKind::Arg => f.write_str("argument"),
            SymKind::Global { .. } => f.write_str("global"),
            SymKind::Function => f.write_str("function"),
            SymKind::Module => f.write_str("module"),
        }
    }
}

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
        name_loc: Span,
        mutable: bool,
        typ: Option<DsExpression>,
        value: Box<DsExpression>,
        loc: Span,
        /// corresponding symbol of this definition
        sym: LazySymbol,
    },
    /// A [`Mod`], with its items inlined inside this member, constructed from
    /// the dsir directive `Mod` by the Desugarrer
    ///
    /// [`Mod`]: lunc_parser::directive::ItemDirective::Mod
    Module {
        name: String,
        module: DsModule,
        /// location of the directive that defined this module.
        loc: Span,
        /// corresponding symbol of this definition
        sym: LazySymbol,
    },
    /// See [`Item::Directive`]
    ///
    /// [`Item::Directive`]: lunc_parser::item::Item::Directive
    Directive(DsItemDirective),
}

/// See [`ItemDirective`]
///
/// [`ItemDirective`]: lunc_parser::directive::ItemDirective
#[derive(Debug, Clone)]
pub enum DsItemDirective {
    Use {
        path: QualifiedPath,
        alias: Option<String>,
        loc: Span,
    },
    /// NOTE: This directive will not be here after we pass the lowered DSIR to the desugarrer
    Mod { name: String, loc: Span },
}

impl FromHigher for DsItemDirective {
    type Higher = ItemDirective;

    fn lower(node: Self::Higher) -> Self {
        match node {
            ItemDirective::Mod { name, loc } => DsItemDirective::Mod {
                name,
                loc: Some(loc),
            },
            ItemDirective::Use { path, alias, loc } => Self::Use {
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
                typ,
                value,
                loc,
            } => DsItem::GlobalDef {
                sym: LazySymbol::Name(name.clone()),
                name,
                name_loc: Some(name_loc),
                mutable: false,
                typ: lower(typ),
                value: Box::new(lower(value)),
                loc: Some(loc),
            },
            Item::GlobalVar {
                name,
                name_loc,
                typ,
                value,
                loc,
            } => DsItem::GlobalDef {
                sym: LazySymbol::Name(name.clone()),
                name,
                name_loc: Some(name_loc),
                mutable: true,
                typ: lower(typ),
                value: Box::new(lower(value)),
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
    pub loc: Span,
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
            Expr::AddressOf { mutable, expr } => DsExpr::AddressOf {
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
            Expr::Block(block) => DsExpr::Block(lower(block)),
            Expr::PredicateLoop { cond, body } => DsExpr::Loop {
                // NOTE: here we make the following conversion eg:
                //
                // while condition {
                //     // body
                // }
                //
                // gets lowered down to
                //
                // loop {
                //     if !condition {
                //         break
                //     }
                //
                //     {
                //         // body
                //     }
                // }
                body: block(
                    vec![
                        stmt_expr(expr_if(
                            expr_unary(UnaryOp::Not, lower(*cond)),
                            expr_break(None),
                            None,
                        )),
                        stmt_expr(expr_block(lower(body))),
                    ],
                    None,
                ),
            },
            Expr::IteratorLoop { .. } => todo!("iterator loop"),
            Expr::InfiniteLoop { body } => DsExpr::Loop { body: lower(body) },
            Expr::Return { expr: val } => DsExpr::Return { expr: lower(val) },
            Expr::Break { expr: val } => DsExpr::Break { expr: lower(val) },
            Expr::Continue => DsExpr::Continue,
            Expr::Null => DsExpr::Null,
            Expr::MemberAccess { expr, member } => DsExpr::MemberAccess {
                expr: lower(expr),
                member,
            },
            Expr::Orb => DsExpr::Orb,
            Expr::FunDefinition {
                args,
                rettype,
                body,
            } => DsExpr::FunDefinition {
                args: lower(args),
                rettype: lower(rettype),
                body: lower(body),
            },
            Expr::PointerType { mutable, typ } => DsExpr::PointerType {
                mutable,
                typ: lower(typ),
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
            expr: DsExpr::Block(lower(*ifexpr.body)),
            loc: Some(ifexpr.loc.clone()),
        }),
        else_br: match ifexpr.else_br.map(|e| *e) {
            Some(Else::IfExpr(ifexp)) => Some(Box::new(DsExpression {
                loc: Some(ifexp.loc.clone()),
                expr: lower_if_expression(ifexp),
            })),
            Some(Else::Block(block)) => Some(Box::new(DsExpression {
                loc: Some(block.loc.clone()),
                expr: DsExpr::Block(lower(block)),
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
    /// See [`Expr::AddressOf`]
    ///
    /// [`Expr::AddressOf`]: lunc_parser::expr::Expr::AddressOf
    AddressOf {
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
    Block(DsBlock),
    /// See [`Expr::InfiniteLoop`], [`Expr::IteratorLoop`] and [`Expr::PredicateLoop`].
    ///
    /// [`Expr::InfiniteLoop`]: lunc_parser::expr::Expr::InfiniteLoop
    /// [`Expr::IteratorLoop`]: lunc_parser::expr::Expr::IteratorLoop
    /// [`Expr::PredicateLoop`]: lunc_parser::expr::Expr::PredicateLoop
    Loop { body: DsBlock },
    /// See [`Expr::Return`]
    ///
    /// [`Expr::Return`]: lunc_parser::expr::Expr::Return
    Return { expr: Option<Box<DsExpression>> },
    /// See [`Expr::Break`]
    ///
    /// [`Expr::Break`]: lunc_parser::expr::Expr::Break
    Break { expr: Option<Box<DsExpression>> },
    /// See [`Expr::Continue`]
    ///
    /// [`Expr::Continue`]: lunc_parser::expr::Expr::Continue
    Continue,
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
    /// See [`Expr::Orb`]
    ///
    /// [`Expr::Orb`]: lunc_parser::expr::Expr::Orb
    Orb,
    /// Constructed from member access, eg:
    ///
    /// `orb.driver.run` are member accesses and it refers to a function "run",
    /// so this expression is lowered down to an EffectivePath
    QualifiedPath {
        /// path to the symbol
        path: QualifiedPath,
        /// the symbol we are reffering to
        sym: LazySymbol,
    },
    /// Constructed from the lazy ident `_`, but only in certain cases, like
    /// when it's part of an assignement like so: `_ = expr`
    Underscore,
    /// See [`Expr::FunDefinition`]
    ///
    /// [`Expr::FunDefinition`]: lunc_parser::expr::Expr::FunDefinition
    FunDefinition {
        args: Vec<DsArg>,
        rettype: Option<Box<DsExpression>>,
        body: DsBlock,
    },
    /// See [`Expr::PointerType`]
    ///
    /// [`Expr::PointerType`]: lunc_parser::expr::Expr::PointerType
    PointerType {
        mutable: bool,
        typ: Box<DsExpression>,
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
pub fn expr_addrof(mutable: bool, val: DsExpression) -> DsExpression {
    DsExpression {
        expr: DsExpr::AddressOf {
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
        expr: DsExpr::Block(block),
        loc: None,
    }
}

/// Creates a loop expression without location.
pub fn expr_loop(body: DsBlock) -> DsExpression {
    DsExpression {
        expr: DsExpr::Loop { body },
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
pub fn expr_break(val: impl Into<Option<DsExpression>>) -> DsExpression {
    DsExpression {
        expr: DsExpr::Break {
            expr: val.into().map(Box::new),
        },
        loc: None,
    }
}

/// Creates a continue expression without location.
pub fn expr_continue() -> DsExpression {
    DsExpression {
        expr: DsExpr::Continue,
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

/// Creates an orb expression without location.
pub fn expr_orb() -> DsExpression {
    DsExpression {
        expr: DsExpr::Orb,
        loc: None,
    }
}

/// Creates a function definition expression without location.
pub fn expr_fundef(
    args: Vec<DsArg>,
    rettype: impl Into<Option<DsExpression>>,
    body: DsBlock,
) -> DsExpression {
    DsExpression {
        expr: DsExpr::FunDefinition {
            args,
            rettype: rettype.into().map(Box::new),
            body,
        },
        loc: None,
    }
}

/// Creates a pointer type expression without location.
pub fn expr_ptr_type(mutable: bool, typ: DsExpression) -> DsExpression {
    DsExpression {
        expr: DsExpr::PointerType {
            mutable,
            typ: Box::new(typ),
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
    pub loc: Span,
}

/// Creates a new block without a location
pub fn block(stmts: Vec<DsStatement>, last_expr: Option<Box<DsExpression>>) -> DsBlock {
    DsBlock {
        stmts,
        last_expr,
        loc: None,
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
    pub loc: Span,
}

impl FromHigher for DsStatement {
    type Higher = Statement;

    fn lower(node: Self::Higher) -> Self {
        let stmt = match node.stmt {
            Stmt::VariableDef {
                name,
                name_loc,
                mutable,
                typ,
                value,
            } => DsStmt::VariableDef {
                sym: LazySymbol::Name(name.clone()),
                name,
                name_loc: Some(name_loc),
                mutable,
                typ: lower(typ),
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
        name_loc: Span,
        mutable: bool,
        typ: Option<DsExpression>,
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
    pub name_loc: Span,
    pub typ: DsExpression,
    pub loc: Span,
    pub sym: LazySymbol,
}

impl FromHigher for DsArg {
    type Higher = Arg;

    fn lower(node: Self::Higher) -> Self {
        let Arg {
            name,
            name_loc,
            typ,
            loc,
        } = node;

        DsArg {
            sym: LazySymbol::Name(name.clone()),
            name,
            name_loc: Some(name_loc),
            typ: lower(typ),
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
    /// are we binding yet?
    binding: bool,
}

impl Desugarrer {
    /// Create a new desugarrer.
    pub fn new(sink: DiagnosticSink, orb_name: String) -> Desugarrer {
        Desugarrer {
            sink,
            table: SymbolTable::new(),
            orb: ModuleTree::new(Some(orb_name)),
            current_path: EffectivePath::with_root_member("orb"),
            binding: false,
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

        // resolve the root module, then it will recurse
        self.resolve_module(&mut module);

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
            if let DsItem::Directive(DsItemDirective::Mod { name, loc }) = item {
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
                    self.sink.push(ModuleFileDoesnotExist {
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
    pub fn resolve_module(&mut self, module: &mut DsModule) {
        self.table.scope_enter(); // module scope

        self.binding = true;
        self.bind_global_defs(module);
        self.binding = false;

        for item in &mut module.items {
            match self.resolve_item(item) {
                Ok(()) => {}
                Err(d) => self.sink.push(d),
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
                self.resolve_module(submod)
            }
        }
    }

    /// Resolve names of an item
    pub fn resolve_item(&mut self, item: &mut DsItem) -> Result<(), Diagnostic> {
        match item {
            DsItem::GlobalDef { typ, value, .. } => {
                if let Some(typ) = typ {
                    self.resolve_expr(typ)?;
                }

                self.resolve_expr(value)?;

                Ok(())
            }
            DsItem::Directive(DsItemDirective::Use {
                path,
                alias,
                loc: _,
            }) => {
                let mut mod_path = path.path.clone();

                let name = mod_path.pop().unwrap();

                if let Some(module) = self.orb.goto(&mod_path)
                    && let Some(symref) = module.def(&name)
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
            DsItem::Module { .. } | DsItem::Directive(_) => Ok(()),
        }
    }

    /// Resolve names in block
    pub fn resolve_block(&mut self, block: &mut DsBlock) {
        self.table.scope_enter(); // block scope

        for stmt in &mut block.stmts {
            match self.resolve_stmt(stmt) {
                Ok(()) => {}
                Err(d) => self.sink.push(d),
            }
        }

        if let Some(expr) = &mut block.last_expr {
            match self.resolve_expr(expr) {
                Ok(()) => {}
                Err(d) => self.sink.push(d),
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
                typ,
                value,
                sym,
            } => {
                match (|| -> Result<(), Diagnostic> {
                    if let Some(typ) = typ {
                        self.resolve_expr(typ)?;
                    }
                    self.resolve_expr(value)?;

                    Ok(())
                })() {
                    Ok(()) => {}
                    Err(d) => self.sink.push(d),
                }

                let symref = SymbolRef::local(
                    *mutable,
                    name.clone(),
                    self.table.local_count(),
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
                // we allow _ in lhs of assignement
                lhs.expr = DsExpr::Underscore;
                self.resolve_expr(rhs)
            }
            DsExpr::Binary { lhs, op: _, rhs } => {
                self.resolve_expr(lhs)?;
                self.resolve_expr(rhs)
            }
            DsExpr::Unary { op: _, expr } | DsExpr::AddressOf { mutable: _, expr } => {
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
            DsExpr::Block(block) | DsExpr::Loop { body: block } => {
                self.resolve_block(block);

                Ok(())
            }
            DsExpr::Return { expr } | DsExpr::Break { expr } => {
                if let Some(expr) = expr {
                    self.resolve_expr(expr)?;
                }

                Ok(())
            }
            DsExpr::Continue | DsExpr::Null | DsExpr::Orb => Ok(()),
            DsExpr::PointerType { mutable: _, typ } => self.resolve_expr(typ),
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
                let sym = symref.read().unwrap();

                if sym.name == "_" {
                    return Err(UnderscoreInExpression {
                        loc: expr.loc.clone().unwrap(),
                    }
                    .into_diag());
                }

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
                    unsafe { unreachable_unchecked() };
                };
                let mut mod_path = path.path.clone();

                mod_path.pop();

                if let Some(module) = self.orb.goto(&mod_path)
                    && let Some(symref) = module.def(sym_name)
                {
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
                        unsafe { unreachable_unchecked() }
                    };

                    self.resolve_expr(&mut *exp)?;

                    Ok(())
                }
            }
            DsExpr::FunDefinition {
                args,
                rettype,
                body,
            } => {
                for DsArg {
                    name,
                    name_loc,
                    typ,
                    loc: _,
                    sym,
                } in args
                {
                    match self.resolve_expr(typ) {
                        Ok(()) => {}
                        Err(d) => self.sink.push(d),
                    }

                    let symref =
                        SymbolRef::arg(name.clone(), self.table.local_count(), name_loc.clone());

                    *sym = LazySymbol::Sym(symref.clone());

                    self.table.bind(name.clone(), symref)?;
                }

                if let Some(ret) = rettype {
                    self.resolve_expr(ret)?;
                }

                self.resolve_block(body);

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
            DsExpr::Orb => {
                path.push("orb");
            }
            _ => return None,
        }

        path.reverse();

        if let Some(sym) = self.table.lookup(path.first().unwrap())
            && sym.read().unwrap().kind == SymKind::Module
        {
            Some(EffectivePath::from_iter(path.iter()))
        } else {
            None
        }
    }

    /// Bind all the global definitions before resolving recursively the dsir
    pub fn bind_global_defs(&mut self, module: &mut DsModule) {
        for item in &mut module.items {
            match self.bind_global_def(item) {
                Ok(()) => {}
                Err(d) => {
                    self.sink.push(d);
                }
            }
        }
    }

    fn bind_global_def(&mut self, item: &mut DsItem) -> Result<(), Diagnostic> {
        match item {
            DsItem::GlobalDef {
                name,
                name_loc,
                mutable: _,
                typ: _,
                value,
                loc: _,
                sym,
            } if value.expr.is_fundef() => {
                let symref = if self.binding {
                    let mut path = self.current_path.clone();
                    path.push(name.clone());

                    let symref = SymbolRef::function(
                        name.clone(),
                        self.table.fun_count(),
                        path,
                        name_loc.clone(),
                    );

                    self.orb
                        .goto_mut(&self.current_path)
                        .unwrap()
                        .define(name.clone(), symref.clone());

                    symref
                } else {
                    self.orb
                        .goto(&self.current_path)
                        .unwrap()
                        .def(&name)
                        .unwrap()
                };

                *sym = LazySymbol::Sym(symref.clone());

                match self.table.bind(name.clone(), symref) {
                    Ok(()) => {}
                    Err(d) => self.sink.push(d),
                }

                Ok(())
            }
            DsItem::GlobalDef {
                name,
                name_loc,
                mutable,
                typ: _,
                value: _,
                loc: _,
                sym,
            } => {
                let symref = if self.binding {
                    let mut path = self.current_path.clone();
                    path.push(name.clone());

                    let symref = SymbolRef::global(
                        *mutable,
                        name.clone(),
                        self.table.fun_count(),
                        path,
                        name_loc.clone(),
                    );

                    self.orb
                        .goto_mut(&self.current_path)
                        .unwrap()
                        .define(name.clone(), symref.clone());

                    symref
                } else {
                    self.orb
                        .goto(&self.current_path)
                        .unwrap()
                        .def(&name)
                        .unwrap()
                };

                *sym = LazySymbol::Sym(symref.clone());

                match self.table.bind(name.clone(), symref) {
                    Ok(()) => {}
                    Err(d) => self.sink.push(d),
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
                    SymbolRef::module(name.clone(), self.table.fun_count(), path, loc.clone());

                *sym = LazySymbol::Sym(symref.clone());

                self.orb
                    .goto_mut(&self.current_path)
                    .unwrap()
                    .define_mod(name.clone());

                match self.table.bind(name.clone(), symref) {
                    Ok(()) => {}
                    Err(d) => self.sink.push(d),
                }

                // change current path for the recursion to work
                self.current_path.push(name.clone());

                // start binding global defs of submodule
                self.bind_global_defs(module);

                // pop the current path to recover the path we had before
                self.current_path.pop();

                Ok(())
            }
            _ => Ok(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SymbolMap {
    map: HashMap<String, SymbolRef>,
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
        const PATH: EffectivePath = EffectivePath::new();

        SymbolMap {
            map: HashMap::from([
                (
                    "isz".to_string(),
                    SymbolRef::global(false, "isz".to_string(), 0, PATH, None),
                ),
                (
                    "i64".to_string(),
                    SymbolRef::global(false, "i64".to_string(), 0, PATH, None),
                ),
                (
                    "i32".to_string(),
                    SymbolRef::global(false, "i32".to_string(), 0, PATH, None),
                ),
                (
                    "i16".to_string(),
                    SymbolRef::global(false, "i16".to_string(), 0, PATH, None),
                ),
                (
                    "i8".to_string(),
                    SymbolRef::global(false, "i8".to_string(), 0, PATH, None),
                ),
                (
                    "usz".to_string(),
                    SymbolRef::global(false, "usz".to_string(), 0, PATH, None),
                ),
                (
                    "u64".to_string(),
                    SymbolRef::global(false, "u64".to_string(), 0, PATH, None),
                ),
                (
                    "u32".to_string(),
                    SymbolRef::global(false, "u32".to_string(), 0, PATH, None),
                ),
                (
                    "u16".to_string(),
                    SymbolRef::global(false, "u16".to_string(), 0, PATH, None),
                ),
                (
                    "u8".to_string(),
                    SymbolRef::global(false, "u8".to_string(), 0, PATH, None),
                ),
                (
                    "f16".to_string(),
                    SymbolRef::global(false, "f16".to_string(), 0, PATH, None),
                ),
                (
                    "f32".to_string(),
                    SymbolRef::global(false, "f32".to_string(), 0, PATH, None),
                ),
                (
                    "f64".to_string(),
                    SymbolRef::global(false, "f64".to_string(), 0, PATH, None),
                ),
                (
                    "bool".to_string(),
                    SymbolRef::global(false, "bool".to_string(), 0, PATH, None),
                ),
                (
                    "str".to_string(),
                    SymbolRef::global(false, "str".to_string(), 0, PATH, None),
                ),
                (
                    "noreturn".to_string(),
                    SymbolRef::global(false, "noreturn".to_string(), 0, PATH, None),
                ),
                (
                    "void".to_string(),
                    SymbolRef::global(false, "void".to_string(), 0, PATH, None),
                ),
                (
                    "orb".to_string(),
                    // NOTE: here we can set the loc to be 0..0 into the root
                    // file, its fine ig, a span from the first character to eof
                    // would be better but this works
                    SymbolRef::module(
                        "orb".to_string(),
                        0,
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

    /// Bind a name to a symbol in the current scope, will panick if name == `_`
    pub fn bind(&mut self, name: String, symref: SymbolRef) -> Result<(), Diagnostic> {
        let sym = symref.read().unwrap();

        match sym.kind {
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
                if let Some(previous_symref) = self.lookup(&name) {
                    let previous_sym = previous_symref.read().unwrap();

                    if let SymKind::Function = previous_sym.kind {
                        return Err(NameDefinedMultipleTimes {
                            name: &name,
                            loc_previous: previous_sym.loc.clone().unwrap(),
                            loc: sym.loc.clone().unwrap(),
                        }
                        .into_diag());
                    }
                }

                self.last_map_mut().fun_count += 1;
            }
            SymKind::Module => {
                self.last_map_mut().mod_count += 1;
            }
        }

        if name.as_str() == "_" {
            let sym = symref.read().unwrap();
            return Err(UnderscoreReservedIdent {
                loc: sym.loc.as_ref().unwrap().clone(),
            }
            .into_diag());
        }

        self.last_map_mut().map.insert(name, symref.clone());

        Ok(())
    }

    /// Return the current scope level
    pub fn level(&self) -> usize {
        self.tabs.len() - 1
    }

    /// Lookup for the symbol in the current scope, returns None if there is no
    /// symbol with this name in the current scope
    pub fn lookup_current(&self, name: impl AsRef<str>) -> Option<SymbolRef> {
        self.last_map().map.get(name.as_ref()).cloned()
    }

    /// Lookup for a symbol with the given name, starting at the current scope
    /// ending at the global scope, returns None if there is no symbol in any
    /// scopes
    pub fn lookup(&mut self, name: impl AsRef<str>) -> Option<SymbolRef> {
        let name = name.as_ref();

        for tab in self.tabs.iter().rev() {
            if let Some(symref) = tab.map.get(name) {
                let symref = symref.clone();
                return Some(symref);
            }
        }

        None
    }

    /// Edit a symbol in the scope `which` with the name `name`, will panick if
    /// the scope or the symbol doesn't exist
    pub fn edit(&mut self, which: usize, name: impl AsRef<str>, new_symbol: Symbol) {
        let symref = self.tabs[which].map.get_mut(name.as_ref()).unwrap().clone();
        let mut lock = symref.write().unwrap();

        *lock = new_symbol;
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
    defs: HashMap<String, SymbolRef>,
    /// is this module tree the root module?
    root_name: Option<String>,
}

impl ModuleTree {
    /// Creates a new ModuleTree, set `root_name` arg to None if the ModuleTree
    /// you want to create is not the root module of the orb.
    pub fn new(root_name: Option<String>) -> ModuleTree {
        ModuleTree {
            submodules: HashMap::default(),
            defs: HashMap::new(),
            root_name,
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
    pub fn define(&mut self, name: String, symref: SymbolRef) {
        let sym = symref.read().unwrap();
        assert!(matches!(
            sym.kind,
            SymKind::Global { .. } | SymKind::Function
        ));

        self.defs.insert(name, symref.clone());
    }

    /// Define a new module in the current module tree
    pub fn define_mod(&mut self, name: String) {
        self.submodules.insert(name, ModuleTree::new(None));
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
    pub fn def(&self, name: impl AsRef<str>) -> Option<SymbolRef> {
        self.defs.get(name.as_ref()).cloned()
    }
}
