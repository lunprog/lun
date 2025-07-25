//! Typed High-level Intermediate Representation of Lun.

use std::fmt::Debug;

use lunc_diag::{DiagnosticSink, FileId};
use lunc_dsir::{
    BinOp, DsArg, DsBlock, DsExpr, DsExpression, DsItem, DsItemDirective, DsModule, DsStatement,
    DsStmt, QualifiedPath, Span, UnaryOp,
};
use lunc_utils::{
    FromHigher, lower,
    symbol::{SymbolRef, Type},
};

pub mod pretty;

/// A semantic checked module, see the dsir version [`DsModule`]
///
/// [`DsModule`]: lunc_dsir::DsModule
#[derive(Debug, Clone)]
pub struct ScModule {
    pub items: Vec<ScItem>,
    pub fid: FileId,
}

impl FromHigher for ScModule {
    type Higher = DsModule;

    fn lower(node: Self::Higher) -> Self {
        let DsModule {
            items: ds_items,
            fid,
        } = node;

        let mut items = Vec::with_capacity(ds_items.len());

        for ds_item in ds_items {
            if let DsItem::Directive(DsItemDirective::Use { .. } | DsItemDirective::Mod { .. }) =
                ds_item
            {
                continue;
            }

            items.push(lower(ds_item));
        }

        ScModule { items, fid }
    }
}

/// A semantic checked item, see the dsir version [`DsItem`]
///
/// [`DsItem`]: lunc_dsir::DsItem
#[derive(Debug, Clone)]
pub enum ScItem {
    /// See [`DsItem::GlobalDef`]
    ///
    /// [`DsItem::GlobalDef`]: lunc_dsir::DsItem::GlobalDef
    GlobalDef {
        name: String,
        name_loc: Span,
        mutable: bool,
        typexpr: Option<ScExpression>,
        value: Box<ScExpression>,
        loc: Span,
        /// corresponding symbol of this definition
        sym: SymbolRef,
    },
    /// See [`DsItem::Module`]
    ///
    /// [`DsItem::Module`]: lunc_dsir::DsItem::Module
    Module {
        /// the name of the module when declared
        name: String,
        /// the items of the module
        module: ScModule,
        /// location of the directive that defined this module.
        loc: Span,
        /// corresponding symbol of this definition
        sym: SymbolRef,
    },
}

impl FromHigher for ScItem {
    type Higher = DsItem;

    fn lower(node: Self::Higher) -> Self {
        match node {
            DsItem::GlobalDef {
                name,
                name_loc,
                mutable,
                typexpr,
                value,
                loc,
                sym: lazy,
            } => ScItem::GlobalDef {
                name,
                name_loc,
                mutable,
                typexpr: lower(typexpr),
                value: lower(value),
                loc,
                sym: lazy.as_sym(),
            },
            DsItem::Module {
                name,
                module,
                loc,
                sym: lazy,
            } => ScItem::Module {
                name,
                module: lower(module),
                loc,
                sym: lazy.as_sym(),
            },
            DsItem::Directive(DsItemDirective::Use { .. } | DsItemDirective::Mod { .. }) => {
                unreachable!()
            }
        }
    }
}

/// A semantic checked expression, see the dsir version [`DsExpression`]
///
/// [`DsExpr`]: lunc_dsir::DsExpression
#[derive(Debug, Clone)]
pub struct ScExpression {
    pub expr: ScExpr,
    pub typ: Option<Type>,
    pub loc: Span,
}

impl FromHigher for ScExpression {
    type Higher = DsExpression;

    fn lower(node: Self::Higher) -> Self {
        let expr = match node.expr {
            DsExpr::IntLit(i) => ScExpr::IntLit(i),
            DsExpr::BoolLit(b) => ScExpr::BoolLit(b),
            DsExpr::StringLit(str) => ScExpr::StringLit(str),
            DsExpr::CharLit(c) => ScExpr::CharLit(c),
            DsExpr::FloatLit(f) => ScExpr::FloatLit(f),
            DsExpr::Ident(lazy) => ScExpr::Ident(lazy.as_sym()),
            DsExpr::Binary { lhs, op, rhs } => ScExpr::Binary {
                lhs: lower(lhs),
                op,
                rhs: lower(rhs),
            },
            DsExpr::Unary { op, expr } => ScExpr::Unary {
                op,
                expr: lower(expr),
            },
            DsExpr::AddressOf { mutable, expr } => ScExpr::AddressOf {
                mutable,
                expr: lower(expr),
            },
            DsExpr::FunCall { callee, args } => ScExpr::FunCall {
                callee: lower(callee),
                args: lower(args),
            },
            DsExpr::If {
                cond,
                then_br,
                else_br,
            } => ScExpr::If {
                cond: lower(cond),
                then_br: lower(then_br),
                else_br: lower(else_br),
            },
            DsExpr::Block { label, block } => ScExpr::Block {
                label,
                block: lower(block),
            },
            DsExpr::Loop { label, body } => ScExpr::Loop {
                label,
                body: lower(body),
            },
            DsExpr::Return { expr } => ScExpr::Return { expr: lower(expr) },
            DsExpr::Break { label, expr } => ScExpr::Break {
                label,
                expr: lower(expr),
            },
            DsExpr::Continue { label } => ScExpr::Continue { label },
            DsExpr::Null => ScExpr::Null,
            DsExpr::MemberAccess { expr, member } => ScExpr::MemberAccess {
                expr: lower(expr),
                member,
            },
            DsExpr::QualifiedPath { path, sym: lazy } => ScExpr::QualifiedPath {
                path,
                sym: lazy.as_sym(),
            },
            DsExpr::Underscore => ScExpr::Underscore,
            DsExpr::FunDefinition {
                args,
                rettypexpr,
                body,
            } => ScExpr::FunDefinition {
                args: lower(args),
                rettypexpr: lower(rettypexpr),
                body: lower(body),
            },
            DsExpr::PointerType { mutable, typexpr } => ScExpr::PointerType {
                mutable,
                typexpr: lower(typexpr),
            },
            DsExpr::FunPtrType { args, ret } => ScExpr::FunPtrType {
                args: lower(args),
                ret: lower(ret),
            },
        };

        ScExpression {
            expr,
            typ: None,
            loc: node.loc,
        }
    }
}

/// A semantic checked internal expression, see the dsir version [`DsExpr`]
///
/// [`DsExpr`]: lunc_dsir::DsExpr
#[derive(Debug, Clone)]
pub enum ScExpr {
    /// See [`DsExpr::IntLit`]
    ///
    /// [`DsExpr::IntLit`]: lunc_dsir::DsExpr::IntLit
    IntLit(u128),
    /// See [`DsExpr::BoolLit`]
    ///
    /// [`DsExpr::BoolLit`]: lunc_dsir::DsExpr::BoolLit
    BoolLit(bool),
    /// See [`DsExpr::StringLit`]
    ///
    /// [`DsExpr::StringLit`]: lunc_dsir::DsExpr::StringLit
    StringLit(String),
    /// See [`DsExpr::CharLit`]
    ///
    /// [`DsExpr::CharLit`]: lunc_dsir::DsExpr::CharLit
    CharLit(char),
    /// See [`DsExpr::FloatLit`]
    ///
    /// [`DsExpr::FloatLit`]: lunc_dsir::DsExpr::FloatLit
    FloatLit(f64),
    /// See [`DsExpr::Ident`]
    ///
    /// [`DsExpr::Ident`]: lunc_dsir::DsExpr::Ident
    Ident(SymbolRef),
    /// See [`DsExpr::Binary`]
    ///
    /// [`DsExpr::Binary`]: lunc_dsir::DsExpr::Binary
    Binary {
        lhs: Box<ScExpression>,
        op: BinOp,
        rhs: Box<ScExpression>,
    },
    /// See [`DsExpr::Unary`]
    ///
    /// [`DsExpr::Unary`]: lunc_dsir::DsExpr::Unary
    Unary {
        op: UnaryOp,
        expr: Box<ScExpression>,
    },
    /// See [`DsExpr::AddressOf`]
    ///
    /// [`DsExpr::AddressOf`]: lunc_dsir::DsExpr::AddressOf
    AddressOf {
        mutable: bool,
        expr: Box<ScExpression>,
    },
    /// See [`DsExpr::FunCall`]
    ///
    /// [`DsExpr::FunCall`]: lunc_dsir::DsExpr::FunCall
    FunCall {
        callee: Box<ScExpression>,
        args: Vec<ScExpression>,
    },
    /// See [`DsExpr::If`] and [`DsExpr::IfThenElse`]
    ///
    /// [`DsExpr::If`]: lunc_dsir::DsExpr::If
    /// [`DsExpr::IfThenElse`]: lunc_dsir::DsExpr::IfThenElse
    If {
        cond: Box<ScExpression>,
        then_br: Box<ScExpression>,
        else_br: Option<Box<ScExpression>>,
    },
    /// See [`DsExpr::Block`]
    ///
    /// [`DsExpr::Block`]: lunc_dsir::DsExpr::Block
    Block {
        label: Option<String>,
        block: ScBlock,
    },
    /// See [`DsExpr::Loop`]
    ///
    /// [`DsExpr::Loop`]: lunc_dsir::DsExpr::Loop
    Loop {
        label: Option<String>,
        body: ScBlock,
    },
    /// See [`DsExpr::Return`]
    ///
    /// [`DsExpr::Return`]: lunc_dsir::DsExpr::Return
    Return { expr: Option<Box<ScExpression>> },
    /// See [`DsExpr::Break`]
    ///
    /// [`DsExpr::Break`]: lunc_dsir::DsExpr::Break
    Break {
        label: Option<String>,
        expr: Option<Box<ScExpression>>,
    },
    /// See [`DsExpr::Continue`]
    ///
    /// [`DsExpr::Continue`]: lunc_dsir::DsExpr::Continue
    Continue { label: Option<String> },
    /// See [`DsExpr::Null`]
    ///
    /// [`DsExpr::Null`]: lunc_dsir::DsExpr::Null
    Null,
    /// See [`DsExpr::MemberAccess`]
    ///
    /// After the name resolution, member access of modules are converted to [`EffectivePath`]
    /// [`DsExpr::MemberAccess`]: lunc_dsir::DsExpr::MemberAccess
    MemberAccess {
        expr: Box<ScExpression>,
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
        sym: SymbolRef,
    },
    /// Constructed from the lazy ident `_`, but only in certain cases, like
    /// when it's part of an assignment like so: `_ = expr`
    Underscore,
    /// See [`DsExpr::FunDefinition`]
    ///
    /// [`DsExpr::FunDefinition`]: lunc_dsir::DsExpr::FunDefinition
    FunDefinition {
        args: Vec<ScArg>,
        rettypexpr: Option<Box<ScExpression>>,
        body: ScBlock,
    },
    /// See [`DsExpr::PointerType`]
    ///
    /// [`DsExpr::PointerType`]: lunc_dsir::DsExpr::PointerType
    PointerType {
        mutable: bool,
        typexpr: Box<ScExpression>,
    },
    /// See [`DsExpr::FunPtrType`]
    ///
    /// [`DsExpr::FunPtrType`]: lunc_dsir::DsExpr::FunPtrType
    FunPtrType {
        args: Vec<ScExpression>,
        ret: Option<Box<ScExpression>>,
    },
}

/// A semantic checked argument, see the dsir version [`DsArg`]
///
/// [`DsArg`]: lunc_dsir::DsArg
#[derive(Debug, Clone)]
pub struct ScArg {
    pub name: String,
    pub name_loc: Span,
    pub typexpr: ScExpression,
    pub loc: Span,
    pub sym: SymbolRef,
}

impl FromHigher for ScArg {
    type Higher = DsArg;

    fn lower(node: Self::Higher) -> Self {
        let DsArg {
            name,
            name_loc,
            typexpr,
            loc,
            sym: lazy,
        } = node;

        ScArg {
            name,
            name_loc,
            typexpr: lower(typexpr),
            loc,
            sym: lazy.as_sym(),
        }
    }
}

/// A semantic checked block, see the dsir version [`DsBlock`]
///
/// [`DsBlock`]: lunc_dsir::DsBlock
#[derive(Debug, Clone)]
pub struct ScBlock {
    pub stmts: Vec<ScStatement>,
    pub last_expr: Option<Box<ScExpression>>,
    pub loc: Span,
    pub typ: Option<Type>,
}

impl FromHigher for ScBlock {
    type Higher = DsBlock;

    fn lower(node: Self::Higher) -> Self {
        let DsBlock {
            stmts,
            last_expr,
            loc,
        } = node;

        ScBlock {
            stmts: lower(stmts),
            last_expr: lower(last_expr),
            loc,
            typ: None,
        }
    }
}

/// A semantic checked statement, see the dsir version [`DsStatement`]
///
/// [`DsStatement`]: lunc_dsir::DsStatement
#[derive(Debug, Clone)]
pub struct ScStatement {
    pub stmt: ScStmt,
    pub loc: Span,
}

impl FromHigher for ScStatement {
    type Higher = DsStatement;

    fn lower(node: Self::Higher) -> Self {
        let stmt = match node.stmt {
            DsStmt::VariableDef {
                name,
                name_loc,
                mutable,
                typexpr,
                value,
                sym: lazy,
            } => ScStmt::VariableDef {
                name,
                name_loc,
                mutable,
                typexpr: lower(typexpr),
                value: lower(value),
                sym: lazy.as_sym(),
            },
            DsStmt::Defer { expr } => ScStmt::Defer { expr: lower(expr) },
            DsStmt::Expression(expr) => ScStmt::Expression(lower(expr)),
        };

        ScStatement {
            stmt,
            loc: node.loc,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ScStmt {
    /// See [`DsStmt::VariableDef`]
    ///
    /// [`DsStmt::VariableDef`]: lunc_dsir::DsStmt::VariableDef
    VariableDef {
        name: String,
        name_loc: Span,
        mutable: bool,
        typexpr: Option<ScExpression>,
        value: Box<ScExpression>,
        sym: SymbolRef,
    },
    /// See [`DsStmt::Defer`]
    ///
    /// [`DsStmt::Defer`]: lunc_dsir::DsStmt::Defer
    Defer { expr: ScExpression },
    /// See [`DsStmt::Expression`]
    ///
    /// [`DsStmt::Expression`]: lunc_dsir::DsStmt::Expression
    Expression(ScExpression),
}

#[derive(Debug, Clone)]
pub struct SemaChecker {
    sink: DiagnosticSink,
}

impl SemaChecker {
    pub fn new(sink: DiagnosticSink) -> SemaChecker {
        SemaChecker { sink }
    }

    pub fn produce(&mut self, dsir: DsModule) -> Option<ScModule> {
        let module = lower(dsir);

        _ = self.sink;

        Some(module)
    }
}
