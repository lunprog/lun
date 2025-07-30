//! Typed High-level Intermediate Representation of Lun.

use std::fmt::Debug;

use diags::{CantResolveComptimeValue, ExpectedTypeFoundExpr};
use lunc_diag::{Diagnostic, DiagnosticSink, FileId, feature_todo};
use lunc_dsir::{
    BinOp, DsArg, DsBlock, DsExpr, DsExpression, DsItem, DsItemDirective, DsModule, DsStatement,
    DsStmt, OSpan, QualifiedPath, UnaryOp,
};
use lunc_utils::{
    FromHigher, Span, lower,
    symbol::{Symbol, Type, ValueExpr},
};

pub mod diags;
pub mod pretty;
pub mod typeck;

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
        name_loc: OSpan,
        mutable: bool,
        typexpr: Box<Option<ScExpression>>,
        value: Box<ScExpression>,
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: Symbol,
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
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: Symbol,
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
                typexpr: Box::new(lower(typexpr)),
                value: lower(value),
                loc,
                sym: lazy.unwrap_sym(),
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
                sym: lazy.unwrap_sym(),
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
    pub typ: Type,
    pub loc: OSpan,
}

impl ScExpression {
    /// Is the expression a place expression kind?
    ///
    /// # Definition
    ///
    /// A place expression, is an expression that represents a memory location,
    /// like a local / global variable / definition that is mutable, a
    /// dereference expression.
    pub fn is_place(&self) -> bool {
        match &self.expr {
            ScExpr::Ident(sym) if sym.is_place() => true,
            ScExpr::Unary {
                op: UnaryOp::Dereference,
                expr: _,
            } => true,
            _ => false,
        }
    }

    pub fn is_underscore(&self) -> bool {
        matches!(self.expr, ScExpr::Underscore)
    }
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
            DsExpr::Ident(lazy) => ScExpr::Ident(lazy.unwrap_sym()),
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
                sym: lazy.unwrap_sym(),
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
            typ: Type::default(),
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
    Ident(Symbol),
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
    /// See [`DsExpr::If`]
    ///
    /// [`DsExpr::If`]: lunc_dsir::DsExpr::If
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
    ///
    /// [`DsExpr::MemberAccess`]: lunc_dsir::DsExpr::MemberAccess
    /// [`EffectivePath`]: lunc_utils::symbol::EffectivePath
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
        sym: Symbol,
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
    pub name_loc: OSpan,
    pub typexpr: ScExpression,
    pub loc: OSpan,
    pub sym: Symbol,
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
            sym: lazy.unwrap_sym(),
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
    pub loc: OSpan,
    pub typ: Type,
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
            typ: Type::Unknown,
        }
    }
}

/// A semantic checked statement, see the dsir version [`DsStatement`]
///
/// [`DsStatement`]: lunc_dsir::DsStatement
#[derive(Debug, Clone)]
pub struct ScStatement {
    pub stmt: ScStmt,
    pub loc: OSpan,
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
                sym: lazy.unwrap_sym(),
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
        name_loc: OSpan,
        mutable: bool,
        typexpr: Option<ScExpression>,
        value: Box<ScExpression>,
        sym: Symbol,
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
        let mut root = lower(dsir);

        self.pre_ck_module(&mut root);
        self.typeck_mod(&mut root);

        if self.sink.failed() {
            return None;
        }

        Some(root)
    }

    /// Tries to evaluate the expression given as argument, if it can't, it
    /// returns Err with the location of the expression that fails to evaluate
    /// at compile time.
    pub fn evaluate_expr(
        &mut self,
        expr: &ScExpression,
        typ: Option<Type>,
    ) -> Result<ValueExpr, Span> {
        match &expr.expr {
            ScExpr::IntLit(i) => match typ {
                Some(Type::I8) => Ok(ValueExpr::I8(*i as i8)),
                Some(Type::I16) => Ok(ValueExpr::I16(*i as i16)),
                Some(Type::I32) => Ok(ValueExpr::I32(*i as i32)),
                Some(Type::I64) => Ok(ValueExpr::I64(*i as i64)),
                Some(Type::I128) => Ok(ValueExpr::I128(*i as i128)),
                Some(Type::Isz) => Ok(ValueExpr::Isz(*i as isize)),
                Some(Type::U8) => Ok(ValueExpr::U8(*i as u8)),
                Some(Type::U16) => Ok(ValueExpr::U16(*i as u16)),
                Some(Type::U32) => Ok(ValueExpr::U32(*i as u32)),
                Some(Type::U64) => Ok(ValueExpr::U64(*i as u64)),
                Some(Type::U128) => Ok(ValueExpr::U128(*i /* as u128 */)),
                Some(Type::Usz) => Ok(ValueExpr::Usz(*i as usize)),
                _ => Ok(ValueExpr::I32(*i as i32)),
            },
            ScExpr::BoolLit(b) => Ok(ValueExpr::Boolean(*b)),
            ScExpr::StringLit(str) => Ok(ValueExpr::Str(str.clone())),
            ScExpr::CharLit(c) => Ok(ValueExpr::Char(*c)),
            ScExpr::FloatLit(f) => match typ {
                Some(Type::F16 | Type::F128) => {
                    self.sink.emit(feature_todo! {
                        feature: "f16 / f128 compile-time evaluation",
                        label: "",
                        loc: expr.loc.clone().unwrap(),
                    });
                    Ok(ValueExpr::F32(*f as f32))
                }
                Some(Type::F32) => Ok(ValueExpr::F32(*f as f32)),
                Some(Type::F64) => Ok(ValueExpr::F64(*f /* as f64 */)),
                _ => Ok(ValueExpr::F32(*f as f32)),
            },
            ScExpr::Ident(sym) if sym.is_comptime_known() => {
                sym.value().ok_or(expr.loc.clone().unwrap())
            }
            ScExpr::PointerType { mutable, typexpr } => {
                let typ = self
                    .evaluate_expr(typexpr, Some(Type::Type))?
                    .as_type()
                    .unwrap_or(Type::Void);
                // NOTE: we do not emit a diagnostic because we already did in
                // the type checking

                Ok(ValueExpr::Type(Type::Ptr {
                    mutable: *mutable,
                    typ: Box::new(typ),
                }))
            }
            ScExpr::FunPtrType { args, ret } => {
                // collect the arguments types
                let mut args_typ = Vec::new();

                for arg in args {
                    let value_typ_arg = match self.evaluate_expr(arg, Some(Type::Type)) {
                        Ok(typ) => typ,
                        Err(loc) => {
                            self.sink.emit(CantResolveComptimeValue {
                                loc_expr: arg.loc.clone().unwrap(),
                                loc: loc.clone(),
                            });

                            ValueExpr::Type(Type::Void)
                        }
                    };

                    let arg_typ = match value_typ_arg.as_type() {
                        Some(typ) => typ,
                        None => {
                            self.sink.emit(ExpectedTypeFoundExpr {
                                loc: arg.loc.clone().unwrap(),
                            });
                            Type::Void
                        }
                    };

                    args_typ.push(arg_typ.clone());
                }

                // evaluate the return type expression
                let ret_typ = if let Some(ret_typexpr) = ret {
                    let value_typ_ret = match self.evaluate_expr(ret_typexpr, Some(Type::Type)) {
                        Ok(typ) => typ,
                        Err(loc) => {
                            self.sink.emit(CantResolveComptimeValue {
                                loc_expr: ret_typexpr.loc.clone().unwrap(),
                                loc: loc.clone(),
                            });

                            ValueExpr::Type(Type::Void)
                        }
                    };

                    match value_typ_ret.as_type() {
                        Some(typ) => typ,
                        None => {
                            self.sink.emit(ExpectedTypeFoundExpr {
                                loc: ret_typexpr.loc.clone().unwrap(),
                            });
                            Type::Void
                        }
                    }
                } else {
                    Type::Void
                };

                Ok(ValueExpr::Type(Type::FunPtr {
                    args: args_typ,
                    ret: Box::new(ret_typ),
                }))
            }
            _ => Err(expr.loc.clone().unwrap()),
        }
    }
}
