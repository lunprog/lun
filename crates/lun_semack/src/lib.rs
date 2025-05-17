use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::iter::zip;

use ckast::{
    CkArg, CkChunk, CkElseIf, CkExpr, CkExpression, CkStatement, CkStmt, FromAst, MaybeUnresolved,
};
use diags::{
    CallRequiresFuncType, ExpectedType, ExpectedTypeFoundExpr, NeverUsedSymbol, NotFoundInScope,
    ReturnOutsideFunc, TypeAnnotationsNeeded, UnderscoreReservedIdent,
};
use lun_diag::{Diagnostic, DiagnosticSink, Label, StageResult, ToDiagnostic};
use lun_parser::expr::{BinOp, UnaryOp};
use lun_parser::stmt::{Chunk, Vis};
use lun_utils::Span;

pub mod ckast;
pub mod diags;

/// Semantic checker, ensure all of the lun's semantic is correct, it also
/// include type checking.
#[derive(Debug, Clone)]
pub struct SemanticCk {
    ast: Chunk,
    sink: DiagnosticSink,
    table: SymbolTable,
    retstack: ReturnStack,
}

impl SemanticCk {
    pub fn new(ast: Chunk, sink: DiagnosticSink) -> SemanticCk {
        SemanticCk {
            ast,
            sink,
            table: SymbolTable::new(),
            retstack: ReturnStack::new(),
        }
    }

    pub fn produce(&mut self) -> StageResult<CkChunk> {
        // 1. create the checked ast from the unchecked ast.
        let mut ckast = CkChunk::from_ast(self.ast.clone());

        // 2. check the first chunk and it will recurse.
        self.table.scope_enter();

        match self.check_chunk(&mut ckast) {
            Ok(()) => {}
            Err(diag) => self.sink.push(diag),
        }

        self.table.scope_exit(&mut self.sink);

        if self.sink.failed() {
            StageResult::Fail(self.sink.clone())
        } else if !self.sink.is_empty() {
            StageResult::Part(ckast, self.sink.clone())
        } else {
            StageResult::Good(ckast)
        }
    }

    pub fn check_chunk(&mut self, chunk: &mut CkChunk) -> Result<(), Diagnostic> {
        // 1. register global defs
        for stmt in &mut chunk.stmts {
            match &mut stmt.stmt {
                CkStmt::VariableDef {
                    vis,
                    name,
                    name_loc,
                    ..
                } if *vis == Vis::Public => {
                    // when type checking the expression and type of this
                    // variable definition change the symbol's typ.
                    let mut ckname = name.clone();
                    if name == "_" {
                        self.sink.push(UnderscoreReservedIdent {
                            loc: name_loc.clone(),
                        });

                        ckname = String::from("\0");
                    }

                    self.table.bind(
                        ckname,
                        Symbol::global(
                            Type::Unknown,
                            name.clone(),
                            self.table.level(),
                            name_loc.clone(),
                        ),
                    );
                }
                CkStmt::FunDef {
                    vis,
                    name,
                    args,
                    rettype,
                    ..
                } => {
                    // true type of the arguments
                    let mut args_true = Vec::new();
                    for CkArg { typ, .. } in args {
                        self.check_expr(typ)?;

                        if typ.typ != Type::ComptimeType {
                            self.sink.push(ExpectedTypeFoundExpr {
                                loc: typ.loc.clone(),
                            });
                        }

                        args_true.push(Type::from_expr(typ.clone()));
                    }

                    let ret_true = if let Some(typ) = rettype {
                        self.check_expr(typ)?;
                        Box::new(Type::from_expr(typ.clone()))
                    } else {
                        Box::new(Type::Nil)
                    };

                    let mut ckname = name.clone();
                    if name == "_" {
                        // TODO: a better location, that points to the function's
                        // name is prefered here.
                        self.sink.push(UnderscoreReservedIdent {
                            loc: stmt.loc.clone(),
                        });
                        ckname = String::from("\0");
                    }

                    self.table.bind(
                        ckname,
                        Symbol::global(
                            Type::Func {
                                args: args_true,
                                ret: ret_true,
                            },
                            name.clone(),
                            self.table.level(),
                            // TODO: add a new loc that points to the signature
                            stmt.loc.clone(),
                        ),
                    );
                }
                _ => {}
            }
        }

        // 2. type check, if you encounter another chunk recurse this function
        for stmt in &mut chunk.stmts {
            self.check_stmt(stmt)?;
        }

        Ok(())
    }

    pub fn check_stmt(&mut self, stmt: &mut CkStatement) -> Result<(), Diagnostic> {
        match &mut stmt.stmt {
            CkStmt::Assignement { variable, value } => {
                // if the variable has a type then we ensure that value is of the same type,
                // otherwise we set the type of variable to the type of value.
                self.check_expr(value)?;

                let Some(symbol) = self.table.lookup(&*variable, true).cloned() else {
                    return Err(NotFoundInScope {
                        name: variable.clone(),
                        loc: stmt.loc.clone(),
                    }
                    .into_diag());
                };

                if &symbol.name == "_" {
                    // do nothing the assignement is to the _ identifier so we don't do anything
                } else if symbol.typ == Type::Unknown && symbol.kind != SymKind::Arg {
                    // we don't know the type of the local / global, so we change it
                    self.table.edit(
                        symbol.which,
                        symbol.name.clone(),
                        symbol.typ(value.clone().typ),
                    );
                } else {
                    // we know the type of the variable and need to ensure the value is of the same type.
                    if symbol.typ != value.typ {
                        self.sink.push(ExpectedType {
                            expected: vec![symbol.typ.clone()],
                            found: value.typ.clone(),
                            loc: value.loc.clone(),
                        })
                    }
                }
            }
            CkStmt::VariableDef {
                vis,
                name,
                name_loc,
                typ,
                value,
            } => {
                // check the type
                if let Some(ty) = typ {
                    self.check_expr(ty)?;

                    if ty.typ != Type::ComptimeType {
                        self.sink.push(
                            ExpectedTypeFoundExpr {
                                loc: ty.loc.clone(),
                            }
                            .into_diag(),
                        );
                    }
                }
                if let Some(value) = value {
                    // check the value
                    self.check_expr(value)?;

                    if let Some(ty) = typ {
                        let expected_ty = Type::from_expr(ty.clone());
                        if value.typ != expected_ty {
                            self.sink.push(ExpectedType {
                                expected: vec![expected_ty],
                                found: value.typ.clone(),
                                loc: value.loc.clone(),
                            })
                        }
                    }
                } else {
                    // TODO: implement variable initialization checking
                    self.sink.push(
                        Diagnostic::error()
                            .with_message("post variable initialization is not yet support")
                            .with_label(Label::primary((), stmt.loc.clone())),
                    )
                }

                let realtyp = if let Some(value) = value {
                    value.typ.clone()
                } else if let Some(typ) = typ {
                    Type::from_expr(typ.clone())
                } else {
                    Type::Unknown
                };

                if *vis == Vis::Private {
                    // define the symbol because we didn't do it before
                    let mut ckname = name.clone();
                    if name == "_" {
                        self.sink.push(UnderscoreReservedIdent {
                            loc: name_loc.clone(),
                        });
                        ckname = String::from("\0");
                    }

                    self.table.bind(
                        ckname,
                        // TODO: add a new loc that point to the variable name and use it in the Symbol
                        Symbol::local(realtyp, name.clone(), self.table.level(), stmt.loc.clone()),
                    )
                } else {
                    // just edit the type of the global variable
                    let Some(sym) = self.table.lookup(name, false).cloned() else {
                        unreachable!()
                    };

                    self.table
                        .edit(sym.which, sym.name.clone(), sym.typ(realtyp));
                }
            }
            CkStmt::IfThenElse {
                cond,
                body,
                else_ifs,
                else_body,
            } => {
                self.check_expr(cond)?;

                if cond.typ != Type::Bool {
                    self.sink.push(ExpectedType {
                        expected: vec![Type::Bool],
                        found: cond.typ.clone(),
                        loc: cond.loc.clone(),
                    })
                }

                self.table.scope_enter();

                self.check_chunk(body)?;

                self.table.scope_exit(&mut self.sink);

                for CkElseIf { cond, body, .. } in else_ifs {
                    self.check_expr(cond)?;

                    if cond.typ != Type::Bool {
                        self.sink.push(ExpectedType {
                            expected: vec![Type::Bool],
                            found: cond.typ.clone(),
                            loc: cond.loc.clone(),
                        })
                    }

                    self.table.scope_enter();

                    self.check_chunk(body)?;

                    self.table.scope_exit(&mut self.sink);
                }

                if let Some(body) = else_body {
                    self.table.scope_enter();

                    self.check_chunk(body)?;

                    self.table.scope_exit(&mut self.sink);
                }
            }
            CkStmt::DoBlock { body } => {
                self.table.scope_enter();

                self.check_chunk(body)?;

                self.table.scope_exit(&mut self.sink);
            }
            CkStmt::FunCall {
                name: MaybeUnresolved::Unresolved(id),
                args,
            } => {
                let Some(sym) = self.table.lookup(&*id, true).cloned() else {
                    return Err(NotFoundInScope {
                        name: id.clone(),
                        loc: stmt.loc.clone(),
                    }
                    .into_diag());
                };

                let Type::Func {
                    args: args_ty,
                    ret: _,
                } = &sym.typ
                else {
                    return Err(CallRequiresFuncType {
                        is_expr: false,
                        loc: stmt.loc.clone(),
                    }
                    .into_diag());
                };

                for (arg, ty) in zip(args, args_ty) {
                    self.check_expr(arg)?;
                    if &arg.typ != ty {
                        self.sink.push(ExpectedType {
                            expected: vec![arg.typ.clone()],
                            found: ty.clone(),
                            loc: arg.loc.clone(),
                        })
                    }
                }

                // TODO: emit a warning diag if the return type of the function
                // is not `Nil` because the value isn't used.
            }
            CkStmt::FunCall {
                name: MaybeUnresolved::Resolved(_),
                ..
            } => unreachable!(),
            CkStmt::While { .. } | CkStmt::For { .. } => {
                // TODO: implement loops checking
                return Err(
                    Diagnostic::error()
                        .with_message("`while` loops, generic `for` loops and numeric `for` loops aren't yet checked")
                        .with_label(Label::primary((), stmt.loc.clone())
                        )
                );
            }
            CkStmt::FunDef {
                vis: _,
                name,
                name_loc: _,
                args,
                rettype: _,
                body,
            } => {
                let Some(Symbol {
                    typ: Type::Func { ret, .. },
                    ..
                }) = self.table.lookup(name, false)
                else {
                    unreachable!()
                };
                self.retstack.push(*ret.clone());

                self.table.scope_enter();

                for CkArg {
                    name,
                    name_loc,
                    typ,
                    loc: _,
                } in args
                {
                    let ty = Type::from_expr(typ.clone());

                    let mut ckname = name.clone();
                    if name == "_" {
                        self.sink.push(UnderscoreReservedIdent {
                            loc: name_loc.clone(),
                        });
                        ckname = String::from("\0");
                    }

                    self.table.bind(
                        ckname.clone(),
                        Symbol::param(ty, ckname.clone(), self.table.level(), name_loc.clone()),
                    )
                }

                self.check_chunk(body)?;

                self.retstack.pop();

                self.table.scope_exit(&mut self.sink);
            }
            CkStmt::Return { val } | CkStmt::Break { val } => {
                // TODO: if the expected type is `Nil` and there is some val but
                // not of type `Nil`, suggest in a Help to remove the code
                if let Some(val) = val {
                    self.check_expr(val)?;

                    let Some(func_ret) = self.retstack.last() else {
                        return Err(ReturnOutsideFunc {
                            loc: stmt.loc.clone(),
                        }
                        .into_diag());
                    };

                    if &val.typ != func_ret {
                        self.sink.push(ExpectedType {
                            expected: vec![func_ret.clone()],
                            found: val.typ.clone(),
                            loc: val.loc.clone(),
                        })
                    }
                }
            }
        }
        Ok(())
    }

    pub fn check_expr(&mut self, expr: &mut CkExpression) -> Result<(), Diagnostic> {
        match &mut expr.expr {
            CkExpr::IntLit(_) => {
                expr.typ = Type::Integer;
            }
            CkExpr::BoolLit(_) => {
                expr.typ = Type::Bool;
            }
            CkExpr::StringLit(_) => {
                expr.typ = Type::String;
            }
            CkExpr::Grouping(expr) => self.check_expr(expr)?,
            CkExpr::Ident(MaybeUnresolved::Unresolved(name)) => {
                let Some(sym) = self.table.lookup(&*name, true) else {
                    return Err(NotFoundInScope {
                        name: name.clone(),
                        loc: expr.loc.clone(),
                    }
                    .into_diag());
                };

                if sym.typ == Type::Unknown {
                    self.sink.push(TypeAnnotationsNeeded {
                        loc: sym.loc.clone(),
                    })
                }
                expr.typ = sym.typ.clone();
                expr.expr = CkExpr::Ident(MaybeUnresolved::Resolved(sym.clone()));
            }
            CkExpr::Ident(MaybeUnresolved::Resolved(_)) => {
                unreachable!("i think it's a bug not sure tho")
            }
            CkExpr::Binary { lhs, op, rhs } => {
                self.check_expr(lhs)?;
                self.check_expr(rhs)?;

                if lhs.typ != rhs.typ {
                    self.sink.push(ExpectedType {
                        expected: vec![lhs.typ.clone()],
                        found: rhs.typ.clone(),
                        loc: rhs.loc.clone(),
                    });
                }

                expr.typ = if op.is_relational() | op.is_logical() {
                    Type::Bool
                } else {
                    lhs.typ.clone()
                };
            }
            CkExpr::Unary { op, expr: exp } => match op {
                UnaryOp::Negation => {
                    if exp.typ != Type::Integer || exp.typ != Type::Float {
                        self.sink.push(ExpectedType {
                            expected: vec![Type::Integer, Type::Float],
                            found: exp.typ.clone(),
                            loc: exp.loc.clone(),
                        })
                    }
                    expr.typ = exp.typ.clone();
                }
                UnaryOp::Not => {
                    if exp.typ != Type::Bool {
                        self.sink.push(ExpectedType {
                            expected: vec![Type::Bool],
                            found: exp.typ.clone(),
                            loc: exp.loc.clone(),
                        });
                    }
                    expr.typ = Type::Bool;
                }
            },
            CkExpr::FunCall { called, args } => {
                self.check_expr(called)?;

                let Type::Func {
                    args: args_ty,
                    ret: ret_ty,
                } = &called.typ
                else {
                    return Err(ExpectedTypeFoundExpr {
                        loc: called.loc.clone(),
                    }
                    .into_diag());
                };

                assert!(called.typ.is_func());

                for (val, ty) in zip(args, args_ty) {
                    self.check_expr(val)?;

                    if &val.typ != ty {
                        self.sink.push(ExpectedType {
                            expected: vec![ty.clone()],
                            found: val.typ.clone(),
                            loc: val.loc.clone(),
                        })
                    }
                }

                expr.typ = *ret_ty.clone();
            }
        }
        debug_assert_ne!(expr.typ, Type::Unknown);
        Ok(())
    }
}

/// Symbol
#[derive(Debug, Clone)]
pub struct Symbol {
    /// local, parameter or global
    pub kind: SymKind,
    /// actual type of the
    pub typ: Type,
    /// the name of the symbol
    pub name: String,
    /// which scope the symbol is referring to
    pub which: usize,
    /// location of the definition of the symbol, must point to at least the
    /// identifier and can point to more: the identifier and the type ...
    pub loc: Span,
    /// count of how many times this symbol is used
    pub uses: usize,
}

impl Symbol {
    /// Create a new symbol
    pub fn new(kind: SymKind, typ: Type, name: String, which: usize, loc: Span) -> Symbol {
        Symbol {
            kind,
            typ,
            name,
            which,
            loc,
            uses: 0,
        }
    }

    /// Create a new local symbol
    pub fn local(typ: Type, name: String, which: usize, loc: Span) -> Symbol {
        Symbol {
            kind: SymKind::Var,
            typ,
            name,
            which,
            loc,
            uses: 0,
        }
    }

    /// Create a new param symbol
    pub fn param(typ: Type, name: String, which: usize, loc: Span) -> Symbol {
        Symbol {
            kind: SymKind::Arg,
            typ,
            name,
            which,
            loc,
            uses: 0,
        }
    }

    /// Create a new global symbol
    pub fn global(typ: Type, name: String, which: usize, loc: Span) -> Symbol {
        Symbol {
            kind: SymKind::Global,
            typ,
            name,
            which,
            loc,
            uses: 0,
        }
    }

    pub fn kind(mut self, kind: SymKind) -> Symbol {
        self.kind = kind;
        self
    }

    pub fn typ(mut self, typ: Type) -> Symbol {
        self.typ = typ;
        self
    }

    pub fn name(mut self, name: String) -> Symbol {
        self.name = name;
        self
    }

    pub fn which(mut self, which: usize) -> Symbol {
        self.which = which;
        self
    }
}

/// Symbol type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymKind {
    /// Variable
    Var,
    /// Argument
    Arg,
    /// Global
    Global,
}

impl Display for SymKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymKind::Var => f.write_str("local"),
            SymKind::Arg => f.write_str("parameter"),
            SymKind::Global => f.write_str("global"),
        }
    }
}

/// Symbol type, the actual type of a symbol
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum Type {
    /// Unknown, at the end of type checking this type is an error.
    #[default]
    Unknown,
    /// equivalent of Rust's `i64`
    Integer,
    /// equivalent of Rust's `f64`
    Float,
    /// equivalent of Rust's `bool`, always one byte long. Can only contain
    /// `true` -> 1 and `false` -> 0
    Bool,
    // TODO: implement strings
    /// a string, nothing for now, we can't use them
    String,
    /// a nil value, just the `nil` literal or nothing
    Nil,
    /// a function type, can only be constructed from a function definition.
    Func {
        /// types of the arguments
        args: Vec<Type>,
        /// the return type
        ret: Box<Type>,
    },
    /// Comptime Type, a type in the Type System.
    ///
    /// Because lun have types that are expression, types get typed checked as
    /// well. So the identifier `int` will be evaluated in EVERY expression to
    /// be of type `comptime type`.
    ComptimeType,
}

impl Type {
    // TODO: add more atomic types, u8, u16, u32, u64, u128, i8, i16,
    // i32, i64, i128, f16, f32, f64, f128
    pub const ATOMIC_TYPES: [&str; 4] = ["int", "float", "bool", "string"];

    pub const ATOMIC_TYPES_PAIR: [(&str, Type); 4] = [
        ("int", Type::Integer),
        ("float", Type::Float),
        ("bool", Type::Bool),
        ("string", Type::String),
    ];

    /// returns true if the type is a function
    pub const fn is_func(&self) -> bool {
        matches!(self, Type::Func { .. })
    }

    /// Converts a type expression to a type.
    pub fn from_expr(expr: CkExpression) -> Type {
        let CkExpr::Ident(MaybeUnresolved::Resolved(Symbol { name, .. })) = expr.expr else {
            unreachable!("the type should just be a symbol")
        };

        for (tyname, ty) in Type::ATOMIC_TYPES_PAIR {
            if tyname == name {
                return ty;
            }
        }

        unreachable!(
            "the type was in the SymbolTable but couldn't be converted to a\
            real type"
        )
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unknown => f.write_str("unknown"),
            Type::Integer => f.write_str("integer"),
            Type::Float => f.write_str("float"),
            Type::Bool => f.write_str("bool"),
            Type::String => f.write_str("string"),
            Type::Nil => f.write_str("nil"),
            // TODO: implement a proper display for function type, like `func(int, float) -> bool`
            Type::Func { .. } => f.write_str("func"),
            Type::ComptimeType => f.write_str("comptime type"),
        }
    }
}

pub type SymbolMap = HashMap<String, Symbol>;

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
        // TODO: load with atomic types like int, float etc etc
        SymbolTable {
            tabs: vec![HashMap::from_iter(
                // TODO: probably change this shit it's not pretty
                Type::ATOMIC_TYPES
                    .iter()
                    .map(|a| {
                        (
                            a.to_string(),
                            Symbol::global(Type::ComptimeType, a.to_string(), 0, Span::ZERO),
                        )
                    })
                    .chain(Some((
                        String::from("_"),
                        Symbol::global(Type::Unknown, "_".to_string(), 0, Span::ZERO),
                    ))),
            )],
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
    pub fn scope_exit(&mut self, sink: &mut DiagnosticSink) {
        assert_ne!(self.tabs.len(), 1, "can't exit out of the global scope");

        for sym in self.last_map().values() {
            // type annotation needed the type is unknown
            if sym.typ == Type::Unknown {
                sink.push(TypeAnnotationsNeeded {
                    loc: sym.loc.clone(),
                })
            }

            // unused symbol check
            if sym.kind != SymKind::Global && sym.uses == 0 {
                // the symbol isn't global and isn't used so we push a warning
                sink.push(NeverUsedSymbol {
                    kind: sym.kind.clone(),
                    name: sym.name.clone(),
                    loc: sym.loc.clone(),
                })
            }
        }

        self.tabs.pop();
    }

    /// Bind a name to a symbol in the current scope, will panick if name == `_`
    pub fn bind(&mut self, name: String, sym: Symbol) {
        assert_ne!(name.as_str(), "_", "`_` is a reserved identifier");
        self.last_map_mut().insert(name, sym);
    }

    /// Return the current scope level
    pub fn level(&self) -> usize {
        self.tabs.len() - 1
    }

    /// Lookup for the symbol in the current scope, returns None if there is no
    /// symbol with this name in the current scope
    pub fn lookup_current(&self, name: impl AsRef<str>) -> Option<&Symbol> {
        self.last_map().get(name.as_ref())
    }

    /// Lookup for a symbol with the given name, starting at the current scope
    /// ending at the global scope, returns None if there is no symbol in any
    /// scopes
    pub fn lookup(&mut self, name: impl AsRef<str>, used: bool) -> Option<&Symbol> {
        for i in (0..=self.level()).rev() {
            if let res @ Some(_) = self.tabs[i].get_mut(name.as_ref()) {
                if used {
                    if let Some(val) = res {
                        val.uses += 1;
                    }
                }
                return self.tabs[i].get(name.as_ref());
            }
        }
        None
    }

    /// Edit a symbol in the scope `which` with the name `name`, will panick if
    /// the scope or the symbol doesn't exist
    pub fn edit(&mut self, which: usize, name: impl AsRef<str>, new_symbol: Symbol) {
        *self.tabs[which].get_mut(name.as_ref()).unwrap() = new_symbol;
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

/// A stack of function's return type, it is used to ensure the return type of
/// the `return` statement is the same as the function's return type. It is a
/// stack because lun supports (or will support) nested functions.
#[derive(Debug, Clone)]
pub struct ReturnStack {
    stack: Vec<Type>,
}

impl ReturnStack {
    pub const fn new() -> ReturnStack {
        ReturnStack { stack: Vec::new() }
    }

    /// Push a return type to the top of the stack
    pub fn push(&mut self, ret: Type) {
        self.stack.push(ret);
    }

    /// Pop the last return type out of the stack, and returns it.
    /// Will panick if there is no more return types.
    pub fn pop(&mut self) -> Type {
        self.stack.pop().unwrap()
    }

    /// Returns a reference to the last return type, panics if there is no more return types.
    #[track_caller]
    pub fn last(&self) -> Option<&Type> {
        self.stack.last()
    }
}

impl Default for ReturnStack {
    fn default() -> Self {
        ReturnStack::new()
    }
}
