//! Typed High-level Intermediate Representation of Lun.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/logo/logo_no_bg_black.png"
)]

use std::fmt::Debug;

use diags::{CantResolveComptimeValue, ExpectedTypeFoundExpr};
use lunc_diag::{Diagnostic, DiagnosticSink, FileId, ToDiagnostic, feature_todo};
use lunc_dsir::{
    DsArg, DsBlock, DsDirective, DsExpr, DsExpression, DsItem, DsModule, DsStatement, DsStmt,
    OSpan, QualifiedPath,
};
use lunc_utils::{
    FromHigher, Span, lower, opt_unreachable,
    symbol::{Symbol, Type, ValueExpr},
    target::{PtrWidth, TargetTriplet},
};

pub use lunc_dsir::{Abi, BinOp, UnaryOp};

use crate::diags::OutsideExternBlock;

pub mod checking;
pub mod diags;
pub mod pretty;
pub mod safety_ck;

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
            if let DsItem::Directive(DsDirective::Import { .. } | DsDirective::Mod { .. }) = ds_item
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
    /// See [`DsItem::GlobalUninit`]
    ///
    /// [`DsItem::GlobalUninit`]: lunc_dsir::DsItem::GlobalUninit
    GlobalUninit {
        name: String,
        name_loc: OSpan,
        typexpr: ScExpression,
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: Symbol,
    },
    /// A [`DsItem::GlobalDef`] and a [`DsExpr::FunDefinition`] combined.
    ///
    /// [`DsExpr::FunDefinition`]: lunc_dsir::DsExpr::FunDefinition
    /// [`DsItem::GlobalDef`]: lunc_dsir::DsItem::GlobalDef
    FunDefinition {
        name: String,
        name_loc: OSpan,
        typexpr: Box<Option<ScExpression>>,
        args: Vec<ScArg>,
        rettypexpr: Option<Box<ScExpression>>,
        body: ScBlock,
        /// set to `true` if it was defined in a mutable global def (this is to
        /// emit E040).
        defined_mut: bool,
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: Symbol,
    },
    /// A [`DsItem::GlobalDef`] and a [`DsExpr::FunDeclaration`] combined.
    ///
    /// [`DsExpr::FunDeclaration`]: lunc_dsir::DsExpr::FunDeclaration
    /// [`DsItem::GlobalDef`]: lunc_dsir::DsItem::GlobalDef
    FunDeclaration {
        name: String,
        name_loc: OSpan,
        typexpr: Box<Option<ScExpression>>,
        args: Vec<ScExpression>,
        rettypexpr: Option<Box<ScExpression>>,
        /// set to `true` if it was defined in a mutable global def (this is to
        /// emit E040).
        defined_mut: bool,
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
    /// See [`DsItem::ExternBlock`]
    ///
    /// [`DsItem::ExternBlock`]: lunc_dsir::DsItem::ExternBlock
    ExternBlock {
        abi: Abi,
        items: Vec<ScItem>,
        loc: OSpan,
    },
}

impl ScItem {
    /// Get the location of the item
    pub fn loc(&self) -> Span {
        match self {
            ScItem::GlobalDef { loc, .. }
            | ScItem::GlobalUninit { loc, .. }
            | ScItem::Module { loc, .. }
            | ScItem::FunDefinition { loc, .. }
            | ScItem::FunDeclaration { loc, .. }
            | ScItem::ExternBlock { loc, .. } => loc.clone().unwrap(),
        }
    }
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
                sym,
            } if value.is_fundef() => {
                let DsExpr::FunDefinition {
                    args,
                    rettypexpr,
                    body,
                } = value.expr
                else {
                    // SAFETY: we already checked in the `if` clause of the match arm.
                    opt_unreachable!();
                };

                ScItem::FunDefinition {
                    name,
                    name_loc,
                    typexpr: Box::new(lower(typexpr)),
                    args: lower(args),
                    rettypexpr: lower(rettypexpr),
                    body: lower(body),
                    defined_mut: mutable,
                    loc,
                    sym: sym.unwrap_sym(),
                }
            }
            DsItem::GlobalDef {
                name,
                name_loc,
                mutable,
                typexpr,
                value,
                loc,
                sym,
            } if value.is_fundecl() => {
                let DsExpr::FunDeclaration { args, rettypexpr } = value.expr else {
                    // SAFETY: we already checked in the `if` clause of the match arm.
                    opt_unreachable!();
                };

                ScItem::FunDeclaration {
                    name,
                    name_loc,
                    typexpr: Box::new(lower(typexpr)),
                    args: lower(args),
                    rettypexpr: lower(rettypexpr),
                    defined_mut: mutable,
                    loc,
                    sym: sym.unwrap_sym(),
                }
            }
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
            DsItem::GlobalUninit {
                name,
                name_loc,
                typexpr,
                loc,
                sym,
            } => ScItem::GlobalUninit {
                name,
                name_loc,
                typexpr: lower(typexpr),
                loc,
                sym: sym.unwrap_sym(),
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
            DsItem::ExternBlock { abi, items, loc } => ScItem::ExternBlock {
                abi,
                items: lower(items),
                loc,
            },
            DsItem::Directive(DsDirective::Import { .. } | DsDirective::Mod { .. }) => {
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
    /// Is the expression a place expression kind? Returns
    ///
    /// # Definition
    ///
    /// A place expression, is an expression that represents a memory location,
    /// like a local / global variable / definition that is mutable, a
    /// dereference expression.
    pub fn is_place(&self) -> Option<String> {
        match &self.expr {
            ScExpr::Ident(sym) => {
                if sym.is_place() {
                    None
                } else {
                    Some("variable isn't mutable".to_string())
                }
            }
            ScExpr::Unary {
                op: UnaryOp::Dereference,
                expr,
            } => {
                if expr.typ.is_mut_ptr() {
                    None
                } else {
                    Some("the dereferenced expression is not of type '*mut T'".to_string())
                }
            }
            _ => Some(String::new()),
        }
    }

    /// Is the expression an underscore expression?
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
            DsExpr::Borrow { mutable, expr } => ScExpr::Borrow {
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
                index: None,
            },
            DsExpr::Loop { label, body } => ScExpr::Loop {
                label,
                body: lower(body),
                index: None,
            },
            DsExpr::Return { expr } => ScExpr::Return { expr: lower(expr) },
            DsExpr::Break { label, expr } => ScExpr::Break {
                label,
                expr: lower(expr),
                index: None,
            },
            DsExpr::Continue { label } => ScExpr::Continue { label, index: None },
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
            DsExpr::FunDefinition { .. } => ScExpr::Poisoned {
                diag: Some(feature_todo! {
                    feature: "local function definition",
                    label: "fundefs inside an expression isn't supported",
                    loc: node.loc.clone().unwrap(),
                }),
            },
            DsExpr::FunDeclaration { .. } => ScExpr::Poisoned {
                diag: Some(
                    OutsideExternBlock {
                        item_name: "function declaration",
                        loc: node.loc.clone().unwrap(),
                    }
                    .into_diag(),
                ),
            },
            DsExpr::PointerType { mutable, typexpr } => ScExpr::PointerType {
                mutable,
                typexpr: lower(typexpr),
            },
            DsExpr::FunPtrType { args, ret } => ScExpr::FunPtrType {
                args: lower(args),
                ret: lower(ret),
            },
            DsExpr::Poisoned { diag: _ } => {
                // NOTE: didn't used `opt_unreachable`, i didn't wanted to
                // ensure it was truly unreachable
                unreachable!()
            }
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
    /// See [`DsExpr::Borrow`]
    ///
    /// [`DsExpr::Borrow`]: lunc_dsir::DsExpr::Borrow
    Borrow {
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
        label: Option<(String, Span)>,
        block: ScBlock,
        /// label index after checking MUST be `Some(..)`
        index: Option<usize>,
    },
    /// See [`DsExpr::Loop`]
    ///
    /// [`DsExpr::Loop`]: lunc_dsir::DsExpr::Loop
    Loop {
        label: Option<(String, Span)>,
        body: ScBlock,
        /// label index after checking MUST be `Some(..)`
        index: Option<usize>,
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
        /// label index after checking MUST be `Some(..)`
        index: Option<usize>,
    },
    /// See [`DsExpr::Continue`]
    ///
    /// [`DsExpr::Continue`]: lunc_dsir::DsExpr::Continue
    Continue {
        label: Option<String>,
        /// label index after checking MUST be `Some(..)`
        index: Option<usize>,
    },
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
    /// See [`DsExpr::Poisoned`]
    ///
    /// # Note
    ///
    /// This node is not emitted from the DsExpr equivalent it is emitted when
    /// we encounter an error in the lowering.
    ///
    /// [`DsExpr::Poisoned`]: lunc_dsir::DsExpr::Poisoned
    Poisoned { diag: Option<Diagnostic> },
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

/// The thing that contains the items
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ItemContainer {
    Module,
    ExternBlock,
}

/// The semantic checker, it turn **DSIR** into **SCIR** and along the way it
/// performs all the checks to ensure the program is semantically valid.
#[derive(Debug, Clone)]
pub struct SemaChecker {
    /// the diagnostic sink to report diagnostics
    sink: DiagnosticSink,
    /// the return type of the function we are currently checking
    fun_retty: Type,
    /// location where the return type was defined
    fun_retty_loc: OSpan,
    /// it is used to check the types and correctness of label using expression
    label_stack: LabelStack,
    /// the target we are compiling to
    target: TargetTriplet,
    /// container of the item currently being checked
    container: ItemContainer,
}

impl SemaChecker {
    pub fn new(sink: DiagnosticSink, target: TargetTriplet) -> SemaChecker {
        SemaChecker {
            sink,
            fun_retty: Type::Unknown,
            fun_retty_loc: None,
            label_stack: LabelStack::new(),
            target,
            container: ItemContainer::Module,
        }
    }

    pub fn produce(&mut self, dsir: DsModule) -> Option<ScModule> {
        let mut root = lower(dsir);

        // we pre check the modules to compute the types of the global definitions
        self.pre_ck_module(&mut root);

        // we check all of the SCIR
        self.ck_mod(&mut root);

        // check the safety of the SCIR, we check if there is no integer literal overflow, float literal overflow..
        self.safety_ck_mod(&root);

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
    ) -> Result<ValueExpr, (Span, Option<String>)> {
        let expr_loc = expr.loc.clone().unwrap();

        match &expr.expr {
            ScExpr::IntLit(i) => match expr.typ {
                Type::I8 => Ok(ValueExpr::I8(*i as i8)),
                Type::I16 => Ok(ValueExpr::I16(*i as i16)),
                Type::I32 => Ok(ValueExpr::I32(*i as i32)),
                Type::I64 => Ok(ValueExpr::I64(*i as i64)),
                Type::I128 => Ok(ValueExpr::I128(*i as i128)),
                Type::Isz => match self.target.ptr_width() {
                    PtrWidth::Ptr16 => Ok(ValueExpr::I16(*i as i16)),
                    PtrWidth::Ptr32 => Ok(ValueExpr::I32(*i as i32)),
                    PtrWidth::Ptr64 => Ok(ValueExpr::I64(*i as i64)),
                },
                Type::U8 => Ok(ValueExpr::U8(*i as u8)),
                Type::U16 => Ok(ValueExpr::U16(*i as u16)),
                Type::U32 => Ok(ValueExpr::U32(*i as u32)),
                Type::U64 => Ok(ValueExpr::U64(*i as u64)),
                Type::U128 => Ok(ValueExpr::U128(*i /* as u128 */)),
                Type::Usz => match self.target.ptr_width() {
                    PtrWidth::Ptr16 => Ok(ValueExpr::U16(*i as u16)),
                    PtrWidth::Ptr32 => Ok(ValueExpr::U32(*i as u32)),
                    PtrWidth::Ptr64 => Ok(ValueExpr::U64(*i as u64)),
                },
                _ => Ok(ValueExpr::I32(*i as i32)),
            },
            ScExpr::BoolLit(b) => Ok(ValueExpr::Boolean(*b)),
            ScExpr::StringLit(str) => Ok(ValueExpr::Str(str.clone())),
            ScExpr::CharLit(c) => Ok(ValueExpr::Char(*c)),
            ScExpr::FloatLit(f) => match expr.typ {
                Type::F16 | Type::F128 => {
                    self.sink.emit(feature_todo! {
                        feature: "f16 / f128 compile-time evaluation",
                        label: "",
                        loc: expr.loc.clone().unwrap(),
                    });
                    Ok(ValueExpr::F32(*f as f32))
                }
                Type::F32 => Ok(ValueExpr::F32(*f as f32)),
                Type::F64 => Ok(ValueExpr::F64(*f /* as f64 */)),
                _ => Ok(ValueExpr::F32(*f as f32)),
            },
            ScExpr::Ident(sym) if sym.is_comptime_known() => sym.value().ok_or((expr_loc, None)),
            ScExpr::Binary { lhs, op, rhs } => {
                let lhs_val = self.evaluate_expr(lhs)?;
                let rhs_val = self.evaluate_expr(rhs)?;

                match op {
                    BinOp::Add => Ok(lhs_val.add(&rhs_val).map_err(|note| (expr_loc, note))?),
                    BinOp::Sub => Ok(lhs_val.sub(&rhs_val).map_err(|note| (expr_loc, note))?),
                    BinOp::Mul => Ok(lhs_val.mul(&rhs_val).map_err(|note| (expr_loc, note))?),
                    BinOp::Div => Ok(lhs_val.div(&rhs_val).map_err(|note| (expr_loc, note))?),
                    BinOp::Rem => Ok(lhs_val.rem(&rhs_val).map_err(|note| (expr_loc, note))?),
                    _ => Err((expr_loc, None)),
                }
            }
            ScExpr::Block {
                label: _,
                block,
                index: _,
            } if block.stmts.is_empty() && block.last_expr.is_none() => {
                // minimal support for blocks evaluation
                Ok(ValueExpr::Void)
            }
            ScExpr::PointerType { mutable, typexpr } => {
                let typ = self.evaluate_expr(typexpr)?.as_type().unwrap_or(Type::Void);
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
                    let value_typ_arg = match self.evaluate_expr(arg) {
                        Ok(typ) => typ,
                        Err((loc, note)) => {
                            self.sink.emit(CantResolveComptimeValue {
                                note,
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
                    let value_typ_ret = match self.evaluate_expr(ret_typexpr) {
                        Ok(typ) => typ,
                        Err((loc, note)) => {
                            self.sink.emit(CantResolveComptimeValue {
                                note,
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
            _ => Err((expr_loc, None)),
        }
    }
}

#[derive(Debug, Clone)]
pub enum LabelKind {
    /// the label is on a block, like
    ///
    /// ```lun
    /// blk: {};
    /// ```
    Block,
    /// the label is on a infinite loop, like
    ///
    /// ```lun
    /// lab: loop {};
    /// ```
    InfiniteLoop,
    /// the label is on a predicate loop, like
    ///
    /// ```lun
    /// lab: while {};
    /// ```
    PredicateLoop,
}

impl LabelKind {
    /// Is this label kind a loop?
    pub fn is_loop(&self) -> bool {
        !matches!(self, LabelKind::Block)
    }

    /// Can this label kind have a value in `break` expressions?
    pub fn can_have_val(&self) -> bool {
        matches!(self, LabelKind::Block | LabelKind::InfiniteLoop)
    }
}

#[derive(Debug, Clone)]
pub struct LabelInfo {
    /// name of the label, `:label` in continue / break and `label:` in
    /// block and loops expression and its location
    pub name: Option<(String, Span)>,
    /// index of the loop
    pub index: usize,
    /// expected type of the loop
    pub typ: Type,
    /// what kind of label it is.
    pub kind: LabelKind,
    /// **For loop**'s label, if set to `true` it indicates that we `break`'d
    /// of the loop and `false` if we never `break`'d of the loop. It is used
    /// to compute the type of a loop, because if the loop is truly infinite:
    /// we can't reach the statement after the loop, then the type of the loop
    /// is `noreturn`.
    ///
    /// **For block**'s label, it can indicate the we never used the label to
    /// short circuit the block.
    pub break_out: bool,
}

/// Stores the definitions of the label
///
/// # Note
///
/// The label live for the entirety of a function after that the stack is
/// cleared.
#[derive(Debug, Clone)]
pub struct LabelStack {
    labels: Vec<LabelInfo>,
    last: usize,
}

impl LabelStack {
    /// Create a new label stack
    pub fn new() -> LabelStack {
        LabelStack {
            labels: Vec::new(),
            last: 0,
        }
    }

    /// Defines a new label
    pub fn define_label(&mut self, name: Option<(String, Span)>, kind: LabelKind) -> usize {
        let index = self.last;
        self.last += 1;

        self.labels.push(LabelInfo {
            name,
            index,
            typ: Type::Unknown,
            kind,
            break_out: false,
        });

        index
    }

    /// Return the last label of the loop
    pub fn last(&self) -> Option<&LabelInfo> {
        self.labels.last()
    }

    /// Reset the content of the label stack to it's defaults
    pub fn reset(&mut self) {
        *self = Default::default();
    }

    /// Get the label info by index
    pub fn get_by_idx(&self, needle: usize) -> Option<&LabelInfo> {
        self.labels.iter().find(|&info| info.index == needle)
    }

    /// Get a mutable ref to the label info by index
    pub fn get_mut_by_idx(&mut self, needle: usize) -> Option<&mut LabelInfo> {
        self.labels.iter_mut().find(|info| info.index == needle)
    }

    /// Get the label info by name
    pub fn get_by_name(&self, needle: impl AsRef<str>) -> Option<&LabelInfo> {
        for info in &self.labels {
            if let Some((name, _)) = &info.name
                && name == needle.as_ref()
            {
                return Some(info);
            }
        }

        None
    }

    /// Get a mutable reference to the label info by name
    pub fn get_mut_by_name(&mut self, needle: impl AsRef<str>) -> Option<&mut LabelInfo> {
        for info in &mut self.labels {
            if let Some((name, _)) = &info.name
                && name == needle.as_ref()
            {
                return Some(info);
            }
        }

        None
    }

    /// Indicate that the label was used in a `break` expression
    pub fn set_breaked_out(&mut self, idx: usize) {
        self.get_mut_by_idx(idx)
            .expect("should be a working label")
            .break_out = true;
    }
}

impl Default for LabelStack {
    fn default() -> Self {
        Self::new()
    }
}
