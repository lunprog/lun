use std::collections::HashMap;
use std::fmt::Debug;
use std::iter::zip;

use ckast::{
    CkArg, CkChunk, CkElseIf, CkExpr, CkExpression, CkStatement, CkStmt, FromAst, MaybeUnresolved,
};
use lun_diag::{DiagnosticSink, StageResult};
use lun_parser::expr::{BinOp, UnaryOp};
use lun_parser::stmt::Chunk;
use lun_utils::Span;

pub mod ckast;

// TODO: implement a 2 pass semantic checker:
// 1. collect all of the global defs in a chunk
// 2. do the type checking of that chunk
// voilà

/// Semantic checker, ensure all of the lun's semantic is correct, it also
/// include type checking.
#[derive(Debug, Clone)]
pub struct SemanticCk {
    ast: Chunk,
    sink: DiagnosticSink,
    table: SymbolTable,
}

impl SemanticCk {
    pub fn new(ast: Chunk, sink: DiagnosticSink) -> SemanticCk {
        SemanticCk {
            ast,
            sink,
            table: SymbolTable::new(),
        }
    }

    pub fn produce(&mut self) -> StageResult<CkChunk> {
        // 1. create the checked ast from the unchecked ast.
        let mut ckast = CkChunk::from_ast(self.ast.clone());

        // 2. check the first chunk and it will recurse.
        self.check_chunk(&mut ckast);

        if self.sink.failed() {
            return StageResult::Fail(self.sink.clone());
        }

        StageResult::Good(ckast)
    }

    pub fn check_chunk(&mut self, chunk: &mut CkChunk) {
        // TODO(URGENT): make this return Result<(), Diagnostic>
        self.table.scope_enter();
        // 1. register global defs
        for stmt in &mut chunk.stmts {
            match &mut stmt.stmt {
                CkStmt::VariableDef {
                    local, variable, ..
                } if !*local => {
                    // when type checking the expression and type of this
                    // variable definition change the symbol's typ.
                    self.table.bind(
                        variable.clone(),
                        Symbol::global(Type::Unknown, variable.clone(), self.table.level()),
                    );
                }
                CkStmt::FunDef {
                    local,
                    name,
                    args,
                    rettype,
                    ..
                } if !*local => {
                    // true type of the arguments
                    let mut args_true = Vec::new();
                    for CkArg { typ, .. } in args {
                        self.check_expr(typ);

                        // TODO(URGENT): emit a diag.
                        assert_eq!(
                            typ.typ,
                            Type::ComptimeType,
                            "expected a type found an expression"
                        );

                        args_true.push(Type::from_expr(typ.clone()));
                    }

                    let ret_true = if let Some(typ) = rettype {
                        self.check_expr(typ);
                        Box::new(Type::from_expr(typ.clone()))
                    } else {
                        Box::new(Type::Nil)
                    };

                    self.table.bind(
                        name.clone(),
                        Symbol::global(
                            Type::Func {
                                args: args_true,
                                ret: ret_true,
                            },
                            name.clone(),
                            self.table.level(),
                        ),
                    );
                }
                _ => {}
            }
        }

        // 2. type check, if you encounter another chunk recurse this function
        for stmt in &mut chunk.stmts {
            self.check_stmt(stmt);
        }

        self.table.scope_exit();
    }

    pub fn check_stmt(&mut self, stmt: &mut CkStatement) {
        match &mut stmt.stmt {
            CkStmt::Assignement { variable, value } => {
                // if the variable has a type then we ensure that value is of the same type,
                // otherwise we set the type of variable to the type of value.
                self.check_expr(value);

                let Some(symbol) = self.table.lookup(variable) else {
                    // TODO(URGENT): return a diag
                    panic!("cannot find variable `...` in this scope")
                };

                if symbol.typ == Type::Unknown && symbol.kind != SymKind::Param {
                    // we don't know the type of the local / global, so we change it
                    self.table.edit(
                        symbol.which,
                        symbol.name.clone(),
                        symbol.clone().typ(value.clone().typ),
                    );
                } else {
                    // we know the type of the variable and need to ensure the value is of the same type.
                    // TODO(URGENT): emit a diag.
                    assert_eq!(symbol.typ, value.typ);
                }
            }
            CkStmt::VariableDef {
                local,
                variable,
                typ,
                value,
            } => {
                // check the value
                self.check_expr(value);

                // check the type
                if let Some(ty) = typ {
                    self.check_expr(ty);

                    // TODO(URGENT): emit a diag.
                    assert_eq!(
                        ty.typ,
                        Type::ComptimeType,
                        "expected a type found an expression"
                    );

                    // TODO(URGENT): emit a diag.
                    assert_eq!(
                        value.typ,
                        Type::from_expr(ty.clone()),
                        "expected type ... found ..."
                    );
                }

                if *local {
                    // define the symbol because we didn't do it before
                    self.table.bind(
                        variable.clone(),
                        Symbol::local(value.typ.clone(), variable.clone(), self.table.level()),
                    )
                } else {
                    // just edit the type of the global variable
                    let Some(sym) = self.table.lookup(variable) else {
                        unreachable!()
                    };

                    self.table.edit(
                        sym.which,
                        sym.name.clone(),
                        sym.clone().typ(value.typ.clone()),
                    );
                }
            }
            CkStmt::IfThenElse {
                cond,
                body,
                else_ifs,
                else_body,
            } => {
                self.check_expr(cond);

                // TODO(URGENT): emit diag
                assert_eq!(cond.typ, Type::Bool);

                self.check_chunk(body);

                for CkElseIf { cond, body, .. } in else_ifs {
                    self.check_expr(cond);

                    // TODO(URGENT): emit diag
                    assert_eq!(cond.typ, Type::Bool);

                    self.check_chunk(body);
                }

                if let Some(body) = else_body {
                    self.check_chunk(body);
                }
            }
            CkStmt::DoBlock { body } => {
                self.check_chunk(body);
            }
            CkStmt::FunCall {
                name: MaybeUnresolved::Unresolved(id),
                args,
            } => {
                // TODO(URGENT): emit a diag
                let sym = self.table.lookup(id).unwrap().clone();

                let Type::Func { args: args_ty, ret } = &sym.typ else {
                    panic!("function call requires function type");
                };

                for (arg, ty) in zip(args, args_ty) {
                    self.check_expr(arg);
                    // TODO(URGENT): emit a diag
                    assert_eq!(&arg.typ, ty, "expected type ... found ...");
                }

                // TODO: emit a warning diag if the return type of the function
                // is not `Nil` because the value isn't used.
            }
            CkStmt::FunCall {
                name: MaybeUnresolved::Resolved(_),
                ..
            } => unreachable!(),
            CkStmt::While { .. } | CkStmt::NumericFor { .. } | CkStmt::GenericFor { .. } => {
                // TODO(URGENT): return a diag
                // TODO: implement loops checking
                todo!("EMIT A DIAGNOSTIC INSTEAD")
            }
            CkStmt::FunDef {
                local,
                name,
                args,
                rettype,
                body,
            } => {
                if *local {
                    let mut args_true = Vec::new();
                    for CkArg { typ, .. } in &mut *args {
                        self.check_expr(typ);

                        // TODO(URGENT): emit a diag.
                        assert_eq!(
                            typ.typ,
                            Type::ComptimeType,
                            "expected a type found an expression"
                        );

                        args_true.push(Type::from_expr(typ.clone()));
                    }

                    let ret_true = if let Some(typ) = rettype {
                        self.check_expr(typ);
                        Box::new(Type::from_expr(typ.clone()))
                    } else {
                        Box::new(Type::Nil)
                    };

                    self.table.bind(
                        name.clone(),
                        Symbol::local(
                            Type::Func {
                                args: args_true,
                                ret: ret_true,
                            },
                            name.clone(),
                            self.table.level(),
                        ),
                    );
                }

                for CkArg { name, typ, .. } in args {
                    let ty = Type::from_expr(typ.clone());

                    self.table.bind(
                        name.clone(),
                        Symbol::param(ty, name.clone(), self.table.level()),
                    )
                }

                self.check_chunk(body);
            }
            CkStmt::Return { val } | CkStmt::Break { val } => {
                // TODO(URGENT): ensure the thing we return is the type of
                // the last function's return type.
                //
                // maybe do it with a stack based approach, like we push a new
                // expected return type of a function when we go in FunDef's
                // checking and after it we pop it so when checking return we
                // can actually ensure a good type
                //
                // TODO: if the expected type is `Nil` and there is some val but
                // not of type `Nil`, suggest in a Help to remove the code
                if let Some(val) = val {
                    self.check_expr(val);
                }
            }
        }
    }

    pub fn check_expr(&mut self, expr: &mut CkExpression) {
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
            CkExpr::Grouping(expr) => self.check_expr(expr),
            CkExpr::Ident(MaybeUnresolved::Unresolved(name)) => {
                // TODO(URGENT): remove this unwrap and return a diag
                let sym = self.table.lookup(name).unwrap();

                // TODO(URGENT): emit an error, the symbol's type isn't known
                assert_ne!(sym.typ, Type::Unknown);
                expr.typ = sym.typ.clone();
                expr.expr = CkExpr::Ident(MaybeUnresolved::Resolved(sym.clone()));
            }
            CkExpr::Ident(MaybeUnresolved::Resolved(_)) => {
                unreachable!("i think it's a bug not sure tho")
            }
            CkExpr::Binary { lhs, op, rhs } => {
                self.check_expr(lhs);
                self.check_expr(rhs);

                // TODO(URGENT): emit a diag (not return)
                assert_eq!(lhs.typ, rhs.typ);

                expr.typ = if op.is_relational() | op.is_logical() {
                    Type::Bool
                } else {
                    lhs.typ.clone()
                };
            }
            CkExpr::Unary { op, expr: exp } => match op {
                // TODO(URGENT): emit diags.
                UnaryOp::Negation => {
                    assert!(matches!(exp.typ, Type::Integer | Type::Float));
                    expr.typ = exp.typ.clone();
                }
                UnaryOp::Not => {
                    assert_eq!(exp.typ, Type::Bool);
                    expr.typ = Type::Bool;
                }
            },
            CkExpr::FunCall { called, args } => {
                self.check_expr(called);

                let Type::Func {
                    args: args_ty,
                    ret: ret_ty,
                } = &called.typ
                else {
                    // TODO(URGENT): return a diag
                    panic!("call expression requires function type");
                };

                assert!(called.typ.is_func());

                for (val, ty) in zip(args, args_ty) {
                    self.check_expr(val);
                    // TODO(URGENT): emit a diag
                    assert_eq!(&val.typ, ty, "expected type ... found type ...");
                }

                expr.typ = *ret_ty.clone();
            }
        }
        debug_assert_ne!(expr.typ, Type::Unknown);
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
}

impl Symbol {
    /// Create a new symbol
    pub fn new(kind: SymKind, typ: Type, name: String, which: usize) -> Symbol {
        Symbol {
            kind,
            typ,
            name,
            which,
        }
    }

    /// Create a new local symbol
    pub fn local(typ: Type, name: String, which: usize) -> Symbol {
        Symbol {
            kind: SymKind::Local,
            typ,
            name,
            which,
        }
    }

    /// Create a new param symbol
    pub fn param(typ: Type, name: String, which: usize) -> Symbol {
        Symbol {
            kind: SymKind::Param,
            typ,
            name,
            which,
        }
    }

    /// Create a new global symbol
    pub fn global(typ: Type, name: String, which: usize) -> Symbol {
        Symbol {
            kind: SymKind::Global,
            typ,
            name,
            which,
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
    Local,
    Param,
    Global,
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
            todo!("idk could be a bug")
        };

        for (tyname, ty) in Type::ATOMIC_TYPES_PAIR {
            if tyname == name {
                return ty;
            }
        }

        todo!("idk could also be a bug")
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
            tabs: vec![HashMap::from_iter(Type::ATOMIC_TYPES.iter().map(|a| {
                (
                    a.to_string(),
                    Symbol::global(Type::ComptimeType, a.to_string(), 0),
                )
            }))],
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
        assert_ne!(self.tabs.len(), 1, "can't exit out of the global scope")
    }

    /// Bind a name to a symbol in the current scope
    pub fn bind(&mut self, name: String, sym: Symbol) {
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
    pub fn lookup(&self, name: impl AsRef<str>) -> Option<&Symbol> {
        for i in (0..=self.level()).rev() {
            if let res @ Some(_) = self.tabs[i].get(name.as_ref()) {
                return res;
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
