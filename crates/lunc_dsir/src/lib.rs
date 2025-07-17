//! Desugared Intermediate Representation of Lun.

use std::{fs, path::PathBuf};

use diags::ModuleFileDoesnotExist;
use lunc_diag::{DiagnosticSink, FileId};
use lunc_lexer::Lexer;
use lunc_parser::{
    Parser,
    directive::{EffectivePath, ItemDirective},
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
    Sym(Symbol),
}

impl From<String> for LazySymbol {
    fn from(value: String) -> Self {
        LazySymbol::Name(value)
    }
}

impl From<Symbol> for LazySymbol {
    fn from(value: Symbol) -> Self {
        LazySymbol::Sym(value)
    }
}

/// A symbol
#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: String,
    pub loc: Span,
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
        path: EffectivePath,
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
            Expr::AddressOf { mutable, val } => DsExpr::AddressOf {
                mutable,
                val: lower(val),
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
            Expr::Return { val } => DsExpr::Return { val: lower(val) },
            Expr::Break { val } => DsExpr::Break { val: lower(val) },
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
        val: Box<DsExpression>,
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
    Return { val: Option<Box<DsExpression>> },
    /// See [`Expr::Break`]
    ///
    /// [`Expr::Break`]: lunc_parser::expr::Expr::Break
    Break { val: Option<Box<DsExpression>> },
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
    /// [`Expr::MemberAccess`]: lunc_parser::expr::Expr::MemberAccess
    MemberAccess {
        expr: Box<DsExpression>,
        member: String,
    },
    /// See [`Expr::Orb`]
    ///
    /// [`Expr::Orb`]: lunc_parser::expr::Expr::Orb
    Orb,
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
            val: Box::new(val),
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
            val: val.into().map(Box::new),
        },
        loc: None,
    }
}

/// Creates a break expression without location.
pub fn expr_break(val: impl Into<Option<DsExpression>>) -> DsExpression {
    DsExpression {
        expr: DsExpr::Break {
            val: val.into().map(Box::new),
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
    sink: DiagnosticSink,
}

impl Desugarrer {
    /// Create a new desugarrer.
    pub const fn new(sink: DiagnosticSink) -> Desugarrer {
        Desugarrer { sink }
    }

    pub fn produce(&mut self, ast: Module) -> Option<DsModule> {
        let mut root = lower(ast);

        self.inline_modules(&mut root);

        if self.sink.failed() {
            return None;
        }

        Some(root)
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
                };
            }
        }

        // we successfully inlined all modules :)
    }
}
