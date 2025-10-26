//! Semantic Checked Intermediate Representation of Lun.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::fmt::Debug;

use lunc_ast::{
    Abi, BinOp, ItemContainer, Mutability, Spanned, UnOp,
    symbol::{SymKind, Symbol, Type, Typeness, ValueExpr},
};
use lunc_desugar::{
    DsArg, DsBlock, DsDirective, DsExprKind, DsExpression, DsItem, DsModule, DsStatement,
    DsStmtKind, OSpan, SpannedPath,
};
use lunc_diag::{Diagnostic, DiagnosticSink, FileId, ToDiagnostic, feature_todo};
use lunc_llib_meta::ModuleTree;
use lunc_token::{Lit, LitKind, LitVal};
use lunc_utils::{
    BuildOptions, FromHigher, OrbType, Span, lower, opt_unreachable, target::PointerWidth,
};

use crate::diags::{
    BadMainSignature, CantResolveComptimeValue, ExpectedTypeFoundExpr, MainUndefined,
    OutsideExternBlock,
};

mod checking;
pub mod diags;
pub mod pretty;
mod safety_ck;

/// A semantic checked module, see the dsir version [`DsModule`]
///
/// [`DsModule`]: lunc_desugar::DsModule
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
/// [`DsItem`]: lunc_desugar::DsItem
#[derive(Debug, Clone)]
pub enum ScItem {
    /// See [`DsItem::GlobalDef`]
    ///
    /// [`DsItem::GlobalDef`]: lunc_desugar::DsItem::GlobalDef
    GlobalDef {
        name: Spanned<String>,
        mutability: Mutability,
        typeexpr: Box<Option<ScExpression>>,
        value: Box<ScExpression>,
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: Symbol,
    },
    /// See [`DsItem::GlobalUninit`]
    ///
    /// [`DsItem::GlobalUninit`]: lunc_desugar::DsItem::GlobalUninit
    GlobalUninit {
        name: Spanned<String>,
        typeexpr: ScExpression,
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: Symbol,
    },
    /// A [`DsItem::GlobalDef`] and a [`DsExprKind::FunDefinition`] combined.
    ///
    /// [`DsExprKind::FunDefinition`]: lunc_desugar::DsExprKind::FunDefinition
    /// [`DsItem::GlobalDef`]: lunc_desugar::DsItem::GlobalDef
    FunDefinition {
        name: Spanned<String>,
        typeexpr: Box<Option<ScExpression>>,
        args: Vec<ScArg>,
        rettypeexpr: Option<Box<ScExpression>>,
        body: ScBlock,
        info: FunDefInfo,
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: Symbol,
    },
    /// A [`DsItem::GlobalDef`] and a [`DsExprKind::FunDeclaration`] combined.
    ///
    /// [`DsExprKind::FunDeclaration`]: lunc_desugar::DsExprKind::FunDeclaration
    /// [`DsItem::GlobalDef`]: lunc_desugar::DsItem::GlobalDef
    FunDeclaration {
        name: Spanned<String>,
        typeexpr: Box<Option<ScExpression>>,
        args: Vec<ScExpression>,
        rettypeexpr: Option<Box<ScExpression>>,
        /// set to `true` if it was defined in a mutable global def (this is to
        /// emit E040).
        defined_mut: bool,
        loc: OSpan,
        /// corresponding symbol of this definition
        sym: Symbol,
    },
    /// See [`DsItem::Module`]
    ///
    /// [`DsItem::Module`]: lunc_desugar::DsItem::Module
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
    /// [`DsItem::ExternBlock`]: lunc_desugar::DsItem::ExternBlock
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

    pub fn symbol(&self) -> Option<Symbol> {
        match self {
            Self::GlobalDef { sym, .. }
            | Self::GlobalUninit { sym, .. }
            | Self::FunDefinition { sym, .. }
            | Self::FunDeclaration { sym, .. }
            | Self::Module { sym, .. } => Some(sym.clone()),
            Self::ExternBlock { .. } => None,
        }
    }
}

impl FromHigher for ScItem {
    type Higher = DsItem;

    fn lower(node: Self::Higher) -> Self {
        match node {
            DsItem::GlobalDef {
                name,
                mutability,
                typeexpr,
                value,
                loc,
                sym,
            } if value.is_fundef() => {
                let DsExprKind::FunDefinition {
                    args,
                    rettypeexpr,
                    body,
                } = value.expr
                else {
                    // SAFETY: we already checked in the `if` clause of the match arm.
                    opt_unreachable!();
                };

                ScItem::FunDefinition {
                    name,
                    typeexpr: Box::new(lower(typeexpr)),
                    args: lower(args),
                    rettypeexpr: lower(rettypeexpr),
                    body: lower(body),
                    info: FunDefInfo {
                        defined_mut: mutability.is_mut(),
                    },
                    loc,
                    sym: sym.unwrap_sym(),
                }
            }
            DsItem::GlobalDef {
                name,
                mutability,
                typeexpr,
                value,
                loc,
                sym,
            } if value.is_fundecl() => {
                let DsExprKind::FunDeclaration { args, rettypeexpr } = value.expr else {
                    // SAFETY: we already checked in the `if` clause of the match arm.
                    opt_unreachable!();
                };

                ScItem::FunDeclaration {
                    name,
                    typeexpr: Box::new(lower(typeexpr)),
                    args: lower(args),
                    rettypeexpr: lower(rettypeexpr),
                    defined_mut: mutability.is_mut(),
                    loc,
                    sym: sym.unwrap_sym(),
                }
            }
            DsItem::GlobalDef {
                name,
                mutability,
                typeexpr,
                value,
                loc,
                sym: lazy,
            } => ScItem::GlobalDef {
                name,
                mutability,
                typeexpr: Box::new(lower(typeexpr)),
                value: lower(value),
                loc,
                sym: lazy.unwrap_sym(),
            },
            DsItem::GlobalUninit {
                name,
                typeexpr,
                loc,
                sym,
            } => ScItem::GlobalUninit {
                name,
                typeexpr: lower(typeexpr),
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

/// Infos, used across the compiler to emit errors later, ease the lowering of
/// SCIR to CLIF.
#[derive(Debug, Clone)]
pub struct FunDefInfo {
    /// set to `true` if it was defined in a mutable global def (this is
    /// used to emit E040).
    pub defined_mut: bool,
}

/// A semantic checked expression, see the dsir version [`DsExpression`]
///
/// [`DsExpr`]: lunc_desugar::DsExpression
#[derive(Debug, Clone)]
pub struct ScExpression {
    pub expr: ScExprKind,
    pub typ: Type,
    pub loc: OSpan,
}

impl ScExpression {
    /// Is the expression a place expression kind? Returns `None`, if it is a
    /// place, or returns `Some("..")` with a note explaining why
    ///
    /// # Definition
    ///
    /// A place expression, is an expression that represents a memory location,
    /// like a local / global variable / definition that is mutable, a
    /// dereference expression.
    pub fn is_place(&self) -> Option<String> {
        match &self.expr {
            ScExprKind::Path(sym) => {
                if sym.is_place() {
                    None
                } else {
                    Some("variable isn't mutable".to_string())
                }
            }
            ScExprKind::Unary {
                op: UnOp::Dereference,
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
        matches!(self.expr, ScExprKind::Underscore)
    }

    /// Returns the typeness of an expression
    pub fn typeness(&self) -> Typeness {
        match &self.expr {
            ScExprKind::Lit(Lit {
                kind: LitKind::Integer | LitKind::Float,
                ..
            }) => Typeness::Implicit,
            ScExprKind::BoolLit(_) | ScExprKind::Lit(_) => Typeness::Explicit,
            ScExprKind::Path(symref) => symref.typeness(),
            ScExprKind::Binary { lhs, op: _, rhs } => {
                if lhs.typeness() == Typeness::Explicit || rhs.typeness() == Typeness::Explicit {
                    Typeness::Explicit
                } else {
                    Typeness::Implicit
                }
            }
            ScExprKind::Unary { op: _, expr } | ScExprKind::Borrow(_, expr) => expr.typeness(),
            ScExprKind::Call { .. } => Typeness::Explicit,
            ScExprKind::If {
                cond: _,
                then_br,
                else_br,
            } => {
                if then_br.typeness() == Typeness::Explicit {
                    Typeness::Explicit
                } else if let Some(else_br) = else_br
                    && else_br.typeness() == Typeness::Explicit
                {
                    Typeness::Explicit
                } else {
                    Typeness::Implicit
                }
            }
            ScExprKind::Block { .. }
            | ScExprKind::Loop { .. }
            | ScExprKind::Return { .. }
            | ScExprKind::Break { .. }
            | ScExprKind::Continue { .. }
            | ScExprKind::Null
            | ScExprKind::Field { .. }
            | ScExprKind::QualifiedPath { .. }
            | ScExprKind::Underscore
            | ScExprKind::PointerType { .. }
            | ScExprKind::FunPtrType { .. } => Typeness::Explicit,
            ScExprKind::Poisoned { .. } => unreachable!("poisoned expr"),
        }
    }
}

impl FromHigher for ScExpression {
    type Higher = DsExpression;

    fn lower(node: Self::Higher) -> Self {
        let expr = match node.expr {
            DsExprKind::Lit(lit) => ScExprKind::Lit(lit),
            DsExprKind::BoolLit(b) => ScExprKind::BoolLit(b),
            DsExprKind::Path(lazy) => ScExprKind::Path(lazy.unwrap_sym()),
            DsExprKind::Binary { lhs, op, rhs } => ScExprKind::Binary {
                lhs: lower(lhs),
                op,
                rhs: lower(rhs),
            },
            DsExprKind::Unary { op, expr } => ScExprKind::Unary {
                op,
                expr: lower(expr),
            },
            DsExprKind::Borrow(mutability, expr) => ScExprKind::Borrow(mutability, lower(expr)),
            DsExprKind::Call { callee, args } => ScExprKind::Call {
                callee: lower(callee),
                args: lower(args),
            },
            DsExprKind::If {
                cond,
                then_br,
                else_br,
            } => ScExprKind::If {
                cond: lower(cond),
                then_br: lower(then_br),
                else_br: lower(else_br),
            },
            DsExprKind::Block { label, block } => ScExprKind::Block {
                label,
                block: lower(block),
                index: None,
            },
            DsExprKind::Loop { label, body } => ScExprKind::Loop {
                label,
                body: lower(body),
                index: None,
            },
            DsExprKind::Return { expr } => ScExprKind::Return { expr: lower(expr) },
            DsExprKind::Break { label, expr } => ScExprKind::Break {
                label,
                expr: lower(expr),
                index: None,
            },
            DsExprKind::Continue { label } => ScExprKind::Continue { label, index: None },
            DsExprKind::Null => ScExprKind::Null,
            DsExprKind::Field {
                expr,
                field: member,
            } => ScExprKind::Field {
                expr: lower(expr),
                member,
            },
            DsExprKind::Underscore => ScExprKind::Underscore,
            DsExprKind::FunDefinition { .. } => ScExprKind::Poisoned {
                diag: Some(feature_todo! {
                    feature: "local function definition",
                    label: "fundefs inside an expression isn't supported",
                    loc: node.loc.clone().unwrap(),
                }),
            },
            DsExprKind::FunDeclaration { .. } => ScExprKind::Poisoned {
                diag: Some(
                    OutsideExternBlock {
                        item_name: "function declaration",
                        loc: node.loc.clone().unwrap(),
                    }
                    .into_diag(),
                ),
            },
            DsExprKind::PointerType(mutability, typeexpr) => {
                ScExprKind::PointerType(mutability, lower(typeexpr))
            }
            DsExprKind::FunPtrType { args, ret } => ScExprKind::FunPtrType {
                args: lower(args),
                ret: lower(ret),
            },
            DsExprKind::Poisoned { diag: _ } => {
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

/// A semantic checked internal expression, see the dsir version [`DsExprKind`]
///
/// [`DsExprKind`]: lunc_desugar::DsExprKind
#[derive(Debug, Clone)]
pub enum ScExprKind {
    /// See [`DsExprKind::Lit`]
    ///
    /// [`DsExprKind::Lit`]: lunc_desugar::DsExprKind::Lit
    Lit(Lit),
    /// See [`DsExprKind::BoolLit`]
    ///
    /// [`DsExprKind::BoolLit`]: lunc_desugar::DsExprKind::BoolLit
    BoolLit(bool),
    /// See [`DsExprKind::Path`]
    ///
    /// [`DsExprKind::Path`]: lunc_desugar::DsExprKind::Path
    Path(Symbol),
    /// See [`DsExprKind::Binary`]
    ///
    /// [`DsExprKind::Binary`]: lunc_desugar::DsExprKind::Binary
    Binary {
        lhs: Box<ScExpression>,
        op: BinOp,
        rhs: Box<ScExpression>,
    },
    /// See [`DsExprKind::Unary`]
    ///
    /// [`DsExprKind::Unary`]: lunc_desugar::DsExprKind::Unary
    Unary { op: UnOp, expr: Box<ScExpression> },
    /// See [`DsExprKind::Borrow`]
    ///
    /// [`DsExprKind::Borrow`]: lunc_desugar::DsExprKind::Borrow
    Borrow(Mutability, Box<ScExpression>),
    /// See [`DsExprKind::Call`]
    ///
    /// [`DsExprKind::Call`]: lunc_desugar::DsExprKind::Call
    Call {
        callee: Box<ScExpression>,
        args: Vec<ScExpression>,
    },
    /// See [`DsExprKind::If`]
    ///
    /// [`DsExprKind::If`]: lunc_desugar::DsExprKind::If
    If {
        cond: Box<ScExpression>,
        then_br: Box<ScExpression>,
        else_br: Option<Box<ScExpression>>,
    },
    /// See [`DsExprKind::Block`]
    ///
    /// [`DsExprKind::Block`]: lunc_desugar::DsExprKind::Block
    Block {
        label: Option<Spanned<String>>,
        block: ScBlock,
        /// label index after checking MUST be `Some(..)`
        index: Option<usize>,
    },
    /// See [`DsExprKind::Loop`]
    ///
    /// [`DsExprKind::Loop`]: lunc_desugar::DsExprKind::Loop
    Loop {
        label: Option<Spanned<String>>,
        body: ScBlock,
        /// label index after checking MUST be `Some(..)`
        index: Option<usize>,
    },
    /// See [`DsExprKind::Return`]
    ///
    /// [`DsExprKind::Return`]: lunc_desugar::DsExprKind::Return
    Return { expr: Option<Box<ScExpression>> },
    /// See [`DsExprKind::Break`]
    ///
    /// [`DsExprKind::Break`]: lunc_desugar::DsExprKind::Break
    Break {
        label: Option<String>,
        expr: Option<Box<ScExpression>>,
        /// label index after checking MUST be `Some(..)`
        index: Option<usize>,
    },
    /// See [`DsExprKind::Continue`]
    ///
    /// [`DsExprKind::Continue`]: lunc_desugar::DsExprKind::Continue
    Continue {
        label: Option<String>,
        /// label index after checking MUST be `Some(..)`
        index: Option<usize>,
    },
    /// See [`DsExprKind::Null`]
    ///
    /// [`DsExprKind::Null`]: lunc_desugar::DsExprKind::Null
    Null,
    /// See [`DsExprKind::Field`]
    ///
    /// After the name resolution, member access of modules are converted to [`EffectivePath`]
    ///
    /// [`DsExprKind::Field`]: lunc_desugar::DsExprKind::Field
    /// [`EffectivePath`]: lunc_ast::symbol::EffectivePath
    Field {
        expr: Box<ScExpression>,
        member: String,
    },
    /// Constructed from member access, eg:
    ///
    /// `orb.driver.run` are member accesses and it refers to a function "run",
    /// so this expression is lowered down to an EffectivePath
    QualifiedPath {
        /// path to the symbol
        path: SpannedPath,
        /// the symbol we are referring to
        sym: Symbol,
    },
    /// Constructed from the lazy ident `_`, but only in certain cases, like
    /// when it's part of an assignment like so: `_ = expr`
    Underscore,
    /// See [`DsExprKind::PointerType`]
    ///
    /// [`DsExprKind::PointerType`]: lunc_desugar::DsExprKind::PointerType
    PointerType(Mutability, Box<ScExpression>),
    /// See [`DsExprKind::FunPtrType`]
    ///
    /// [`DsExprKind::FunPtrType`]: lunc_desugar::DsExprKind::FunPtrType
    FunPtrType {
        args: Vec<ScExpression>,
        ret: Option<Box<ScExpression>>,
    },
    /// See [`DsExprKind::Poisoned`]
    ///
    /// # Note
    ///
    /// This node is not emitted from the DsExpr equivalent it is emitted when
    /// we encounter an error in the lowering.
    ///
    /// [`DsExprKind::Poisoned`]: lunc_desugar::DsExprKind::Poisoned
    Poisoned { diag: Option<Diagnostic> },
}

/// A semantic checked argument, see the dsir version [`DsArg`]
///
/// [`DsArg`]: lunc_desugar::DsArg
#[derive(Debug, Clone)]
pub struct ScArg {
    pub name: String,
    pub name_loc: OSpan,
    pub typeexpr: ScExpression,
    pub loc: OSpan,
    pub sym: Symbol,
}

impl FromHigher for ScArg {
    type Higher = DsArg;

    fn lower(node: Self::Higher) -> Self {
        let DsArg {
            name,
            name_loc,
            typeexpr,
            loc,
            sym: lazy,
        } = node;

        ScArg {
            name,
            name_loc,
            typeexpr: lower(typeexpr),
            loc,
            sym: lazy.unwrap_sym(),
        }
    }
}

/// A semantic checked block, see the dsir version [`DsBlock`]
///
/// [`DsBlock`]: lunc_desugar::DsBlock
#[derive(Debug, Clone)]
pub struct ScBlock {
    pub stmts: Vec<ScStatement>,
    pub last_expr: Option<Box<ScExpression>>,
    pub loc: OSpan,
    pub typ: Type,
}

impl ScBlock {
    /// Is the block empty? (no stmts and no last expr)
    pub fn is_empty(&self) -> bool {
        self.stmts.is_empty() && self.last_expr.is_none()
    }
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
/// [`DsStatement`]: lunc_desugar::DsStatement
#[derive(Debug, Clone)]
pub struct ScStatement {
    pub stmt: ScStmtKind,
    pub loc: OSpan,
}

impl FromHigher for ScStatement {
    type Higher = DsStatement;

    fn lower(node: Self::Higher) -> Self {
        let stmt = match node.stmt {
            DsStmtKind::BindingDef {
                name,
                mutability,
                typeexpr,
                value,
                sym: lazy,
            } => ScStmtKind::BindingDef {
                name,
                mutability,
                typeexpr: lower(typeexpr),
                value: lower(value),
                sym: lazy.unwrap_sym(),
            },
            DsStmtKind::Defer { expr } => ScStmtKind::Defer { expr: lower(expr) },
            DsStmtKind::Expression(expr) => ScStmtKind::Expression(lower(expr)),
        };

        ScStatement {
            stmt,
            loc: node.loc,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ScStmtKind {
    /// See [`DsStmtKind::BindingDef`]
    ///
    /// [`DsStmtKind::BindingDef`]: lunc_desugar::DsStmtKind::BindingDef
    BindingDef {
        name: Spanned<String>,
        mutability: Mutability,
        typeexpr: Option<ScExpression>,
        value: Box<ScExpression>,
        sym: Symbol,
    },
    /// See [`DsStmtKind::Defer`]
    ///
    /// [`DsStmtKind::Defer`]: lunc_desugar::DsStmtKind::Defer
    Defer { expr: ScExpression },
    /// See [`DsStmtKind::Expression`]
    ///
    /// [`DsStmtKind::Expression`]: lunc_desugar::DsStmtKind::Expression
    Expression(ScExpression),
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
    /// container of the item currently being checked
    container: ItemContainer,
    /// root module tree of the orb being built
    orbtree: ModuleTree,
    /// the build options
    opts: BuildOptions,
}

impl SemaChecker {
    pub fn new(sink: DiagnosticSink, orbtree: ModuleTree, opts: BuildOptions) -> SemaChecker {
        SemaChecker {
            sink,
            fun_retty: Type::Unknown,
            fun_retty_loc: None,
            label_stack: LabelStack::new(),
            container: ItemContainer::Module,
            orbtree,
            opts,
        }
    }

    /// Produce the semantic checked root module, with the given dsir module.
    pub fn produce(&mut self, dsir: DsModule) -> Option<ScModule> {
        let mut root = lower(dsir);

        // we pre check the modules to compute the types of the global definitions
        self.pre_ck_module(&mut root);

        // we check all of the SCIR
        self.ck_mod(&mut root);

        // check the safety of the SCIR, we check if there is no integer literal overflow, float literal overflow..
        self.safety_ck_mod(&mut root);

        if self.opts.orb_type() == OrbType::Bin {
            if let Some(sym) = self.orbtree.def("main") {
                // main definition present
                let main_t = Type::FunPtr {
                    args: Vec::new(),
                    ret: Box::new(Type::Void),
                };
                let sym_t = sym.typ();

                if sym.kind() != SymKind::Function || sym_t != main_t {
                    // main doesn't have the correct signature
                    self.sink.emit(BadMainSignature {
                        got: sym_t,
                        expected: main_t,
                        loc: sym.loc().unwrap(),
                    });
                } else {
                    // everything is fine we have the main definition and it's correct
                }
            } else {
                // main definition not present
                self.sink.emit(MainUndefined);
            }
        }

        Some(root)
    }

    /// Returns the module tree of the last module checked
    pub fn module_tree(self) -> ModuleTree {
        self.orbtree
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
            ScExprKind::Lit(Lit {
                kind: LitKind::Integer,
                value: LitVal::Int(i),
                tag: _,
            }) => match expr.typ {
                Type::I8 => Ok(ValueExpr::I8(*i as i8)),
                Type::I16 => Ok(ValueExpr::I16(*i as i16)),
                Type::I32 => Ok(ValueExpr::I32(*i as i32)),
                Type::I64 => Ok(ValueExpr::I64(*i as i64)),
                Type::I128 => Ok(ValueExpr::I128(*i as i128)),
                Type::Isz => match self.opts.target().pointer_width().unwrap() {
                    PointerWidth::U16 => Ok(ValueExpr::I16(*i as i16)),
                    PointerWidth::U32 => Ok(ValueExpr::I32(*i as i32)),
                    PointerWidth::U64 => Ok(ValueExpr::I64(*i as i64)),
                },
                Type::U8 => Ok(ValueExpr::U8(*i as u8)),
                Type::U16 => Ok(ValueExpr::U16(*i as u16)),
                Type::U32 => Ok(ValueExpr::U32(*i as u32)),
                Type::U64 => Ok(ValueExpr::U64(*i as u64)),
                Type::U128 => Ok(ValueExpr::U128(*i /* as u128 */)),
                Type::Usz => match self.opts.target().pointer_width().unwrap() {
                    PointerWidth::U16 => Ok(ValueExpr::U16(*i as u16)),
                    PointerWidth::U32 => Ok(ValueExpr::U32(*i as u32)),
                    PointerWidth::U64 => Ok(ValueExpr::U64(*i as u64)),
                },
                _ => Ok(ValueExpr::I32(*i as i32)),
            },
            ScExprKind::BoolLit(b) => Ok(ValueExpr::Boolean(*b)),
            ScExprKind::Lit(Lit {
                kind: LitKind::Str,
                value: LitVal::Str(str),
                tag: _,
            }) => Ok(ValueExpr::Str(str.clone())),
            ScExprKind::Lit(Lit {
                kind: LitKind::Char,
                value: LitVal::Char(c),
                tag: _,
            }) => Ok(ValueExpr::Char(*c)),
            ScExprKind::Lit(Lit {
                kind: LitKind::Float,
                value: LitVal::Float(f),
                tag: _,
            }) => match expr.typ {
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
            ScExprKind::Path(sym) if sym.is_comptime_known() => sym.value().ok_or((expr_loc, None)),
            ScExprKind::Binary { lhs, op, rhs } => {
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
            ScExprKind::Block {
                label: _,
                block,
                index: _,
            } if block.stmts.is_empty() && block.last_expr.is_none() => {
                // minimal support for blocks evaluation
                Ok(ValueExpr::Void)
            }
            ScExprKind::PointerType(mutability, typeexpr) => {
                let typ = self
                    .evaluate_expr(typeexpr)?
                    .as_type()
                    .unwrap_or(Type::Void);
                // NOTE: we do not emit a diagnostic because we already did in
                // the type checking

                Ok(ValueExpr::Type(Type::Ptr(*mutability, Box::new(typ))))
            }
            ScExprKind::FunPtrType { args, ret } => {
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
                let ret_typ = if let Some(ret_typeexpr) = ret {
                    let value_typ_ret = match self.evaluate_expr(ret_typeexpr) {
                        Ok(typ) => typ,
                        Err((loc, note)) => {
                            self.sink.emit(CantResolveComptimeValue {
                                note,
                                loc_expr: ret_typeexpr.loc.clone().unwrap(),
                                loc: loc.clone(),
                            });

                            ValueExpr::Type(Type::Void)
                        }
                    };

                    match value_typ_ret.as_type() {
                        Some(typ) => typ,
                        None => {
                            self.sink.emit(ExpectedTypeFoundExpr {
                                loc: ret_typeexpr.loc.clone().unwrap(),
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
    pub name: Option<Spanned<String>>,
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
    /// is `never`.
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
    pub fn define_label(&mut self, name: Option<Spanned<String>>, kind: LabelKind) -> usize {
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
            if let Some(Spanned { node: name, loc: _ }) = &info.name
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
            if let Some(Spanned { node: name, loc: _ }) = &info.name
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
