//! Parsing of lun's statements and chunk.

use super::*;

/// Every source file is a Chunk, a Chunk is a sequence of Statements
#[derive(Debug, Clone)]
pub struct Chunk {
    pub stmts: Vec<Statement>,
    pub loc: Span,
}

impl AstNode for Chunk {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let mut stmts = Vec::new();

        // note, here it's fine to unwrap we know there is always a EOF token at the end.
        let lo = parser.peek_tok().unwrap().loc.clone();
        let mut hi = lo.clone();

        loop {
            match parser.peek_tt() {
                Some(EOF) | Some(Kw(Keyword::End | Keyword::Else)) | None => {
                    break;
                }
                _ => {}
            }

            let stmt = parse!(parser => Statement);
            hi = stmt.loc.clone();

            stmts.push(stmt);

            if let Some(Punct(Punctuation::SemiColon)) = parser.peek_tt() {
                // pop the optional semicolon
                parser.pop();
            }
        }

        Ok(Chunk {
            stmts,
            loc: Span::from_ends(lo, hi),
        })
    }
}

/// Visibility
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum Vis {
    #[default]
    Private,
    Public,
}

/// A lun statement
#[derive(Debug, Clone)]
pub struct Statement {
    pub stmt: Stmt,
    pub loc: Span,
}

// TODO(URGENT): change the `local: bool` fields with a `vis: Visibility` field
// it will be clearer
#[derive(Debug, Clone)]
pub enum Stmt {
    /// assignement
    ///
    /// ident "=" expr
    Assignement { variable: String, value: Expression },
    // TODO: add checking for uninitialized variables
    //
    // ```lun
    // var a: int
    //
    // // ...
    //
    // a = 24
    // ```
    // here `a` is defined, we can use it after the `a = 24` but between the
    // definition and the initialization we can't
    //
    // ```lun
    // var a: int
    //
    // // ...
    //
    // if some_logic() then
    //     a = 12
    // else
    //     a = 25
    // end
    //
    // ```
    // here everything is fine, we can use `a` after the condition so it is
    // initialized
    //
    // ```lun
    // var a: int
    //
    // if something do
    //     a = 12
    // else if something_else do
    //     a = 34
    // end
    // ```
    // here we can't use `a` because it is partially initialized, the compiler
    // is not sure if `a` is initialized, even tho `something_else = !something`
    //
    /// variable definition
    ///
    /// [ "pub" ] "var" ident [ ":" expr ] [ "=" expr ]
    ///
    /// OR
    ///
    /// ident ":" [ expr ] "=" expr
    VariableDef {
        vis: Vis,
        name: String,
        name_loc: Span,
        typ: Option<Expression>,
        value: Option<Expression>,
    },
    /// if then else statement
    ///
    /// "if" expr "then" chunk { "else" "if" expr "then" chunk } [ "else"  chunk] "end"
    IfThenElse {
        /// the condition after the `if`
        cond: Expression,
        /// the chunk after the first `if`
        body: Chunk,
        /// all of the else-ifs cases
        else_ifs: Vec<ElseIf>,
        /// optional else case
        else_body: Option<Chunk>,
    },
    /// do block
    ///
    /// "do" chunk "end"
    DoBlock { body: Chunk },
    // TODO: is the syntax like `add 1, 2, 3` in addition of `add(1, 2, 3)`
    // a good idea? like it could be nice to have sth like that `print "Hello
    // world!"` idk but only for statement function call
    // TODO: add support for the syntax like in Nim `identifier"string literal"`
    // and it would be equivalent to `identifier("string literal")` AND MORE
    // IMPORTANTLY
    // TODO: add support custom numeric literal like ` 123'custom ` is
    // equivalent to `custom("123")` idk but the idea is cool :) so if in the
    // future we add other integer types we can do `123'i8` and it wont be some
    // magical syntax but a numeric literal idk
    /// function call
    ///
    /// ident "(" ( expr ),* ")"
    FunCall {
        /// what is called? a function, a value in a variable, an argument ? etc
        name: String,
        /// the arguments
        args: Vec<Expression>,
    },
    /// while statement
    ///
    /// "while" expr "do" chunk "end"
    While { cond: Expression, body: Chunk },
    /// for statement
    ///
    /// "for" ident "in" expr "do" chunk "end"
    For {
        /// the variable that contains values of the iterator
        variable: String,
        /// the iterator
        iterator: Expression,
        /// the body we run every time the iterator return something non-nil.
        body: Chunk,
    },
    /// function definition
    ///
    /// [ "pub" ] "fun" ident "(" ( ident ":" expr ),* ")" [ "->" expr ] chunk "end"
    FunDef {
        vis: Vis,
        name: String,
        name_loc: Span,
        args: Vec<Arg>,
        rettype: Option<Expression>,
        body: Chunk,
    },
    /// return statement
    ///
    /// "return" [ expr ]
    Return { val: Option<Expression> },
    // TODO: it shouldn't contain an expression when you think about it
    /// break statement
    ///
    /// "break" [ expr ]
    Break { val: Option<Expression> },
}

#[derive(Debug, Clone)]
pub struct ElseIf {
    pub cond: Expression,
    pub body: Chunk,
    pub loc: Span,
}

#[derive(Debug, Clone)]
pub struct Arg {
    pub name: String,
    pub name_loc: Span,
    pub typ: Expression,
    pub loc: Span,
}

impl AstNode for Statement {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        match parser.peek_tt() {
            Some(Kw(Keyword::Pub)) => match parser.nth_tt(1) {
                Some(Kw(Keyword::Var)) => parse_var_stmt(parser),
                Some(Kw(Keyword::Fun)) => parse_fundef_stmt(parser),
                Some(_) => {
                    // pop the `pub` kw
                    parser.pop();
                    // t is the token after `pub`
                    let t = parser.pop().unwrap();

                    Err(ExpectedToken::new(
                        [Kw(Keyword::Var), Kw(Keyword::Fun)],
                        t.tt,
                        Some("statement"),
                        t.loc,
                    )
                    .into_diag())
                }
                None => Err(parser.eof_diag()),
            },
            Some(Ident(_)) => parse_ident_stmt(parser),
            Some(Kw(Keyword::If)) => parse_if_stmt(parser),
            Some(Kw(Keyword::While)) => parse_while_stmt(parser),
            Some(Kw(Keyword::For)) => parse_for_stmt(parser),
            Some(Kw(Keyword::Fun)) => parse_fundef_stmt(parser),
            Some(Kw(Keyword::Return)) => parse_return_stmt(parser),
            Some(Kw(Keyword::Break)) => parse_break_stmt(parser),
            Some(Kw(Keyword::Var)) => parse_var_stmt(parser),
            Some(_) => {
                // unwrap is safe because we already know the next has a token
                // type
                let t = parser.peek_tok().unwrap().clone();
                // TODO: make the parser retry if he failed to parse the
                // statement with a loop, see parsing of expressions also
                Err(ExpectedToken::new(
                    [
                        Ident(String::new()),
                        Kw(Keyword::Pub),
                        Kw(Keyword::If),
                        Kw(Keyword::Do),
                        Kw(Keyword::While),
                        Kw(Keyword::For),
                        Kw(Keyword::Fun),
                        Kw(Keyword::Return),
                        Kw(Keyword::Break),
                        Kw(Keyword::Var),
                    ],
                    t.tt,
                    Some("statement".to_string()),
                    t.loc,
                )
                .into_diag())
            }
            None => Err(parser.eof_diag()),
        }
    }
}

/// parses both assignement, variable definition and function call in statements
pub fn parse_ident_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (name, lo) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    match parser.peek_tt() {
        Some(Punct(Punctuation::Colon)) => {
            // no need to use expect_token here because we already know its a colon
            parser.pop();

            let typ = if let Some(Punct(Punctuation::Equal)) = parser.peek_tt() {
                parser.pop();
                None
            } else {
                let typ = parse!(parser => Expression);
                expect_token!(parser => [Punct(Punctuation::Equal), ()], Punctuation::Equal);
                Some(typ)
            };

            let value = parse!(parser => Expression);
            Ok(Statement {
                loc: Span::from_ends(lo.clone(), value.loc.clone()),
                stmt: Stmt::VariableDef {
                    vis: Vis::Private,
                    name,
                    name_loc: lo,
                    typ,
                    value: Some(value),
                },
            })
        }
        Some(Punct(Punctuation::LParen)) => {
            // we pop the ( no need of expect_token! we already know it is (
            parser.pop();

            let mut args = Vec::new();

            let hi = loop {
                if let Some(Punct(Punctuation::RParen)) = parser.peek_tt() {
                    break parser.pop().unwrap().loc;
                }

                let arg = parse!(parser => Expression);
                args.push(arg);

                expect_token!(parser => [Punct(Punctuation::Comma), ()], Punct(Punctuation::Comma));
            };

            Ok(Statement {
                stmt: Stmt::FunCall { name, args },
                loc: Span::from_ends(lo, hi),
            })
        }
        _ => {
            expect_token!(parser => [Punct(Punctuation::Equal), ()], Punctuation::Equal);

            let value = parse!(parser => Expression);

            Ok(Statement {
                loc: Span::from_ends(lo, value.loc.clone()),
                stmt: Stmt::Assignement {
                    variable: name,
                    value,
                },
            })
        }
    }
}

/// parses if statements
pub fn parse_if_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::If), ()], Kw(Keyword::If));

    let cond = parse!(parser => Expression);

    expect_token!(parser => [Kw(Keyword::Then), ()], Kw(Keyword::Then));

    let body = parse!(parser => Chunk);

    let mut else_ifs = Vec::new();
    while let (Some(Kw(Keyword::Else)), Some(Kw(Keyword::If))) =
        (parser.peek_tt(), parser.nth_tt(1))
    {
        // pop the "else" and "if" keywords
        parser.pop();
        parser.pop();

        let cond = parse!(parser => Expression);

        expect_token!(parser => [Kw(Keyword::Then), ()], Kw(Keyword::Then));

        let body = parse!(parser => Chunk);

        let loc = Span::from_ends(cond.loc.clone(), body.loc.clone());

        else_ifs.push(ElseIf { cond, body, loc });
    }

    let else_body = if let Some(Kw(Keyword::Else)) = parser.peek_tt() {
        // pop the "else" keyword
        parser.pop();

        Some(parse!(parser => Chunk))
    } else {
        None
    };

    let (_, hi) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

    Ok(Statement {
        stmt: Stmt::IfThenElse {
            cond,
            body,
            else_ifs,
            else_body,
        },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses do block statement
pub fn parse_do_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Do), ()], Kw(Keyword::Do));

    let body = parse!(parser => Chunk);

    let (_, hi) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

    Ok(Statement {
        stmt: Stmt::DoBlock { body },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses while statement
pub fn parse_while_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::While), ()], Kw(Keyword::While));

    let cond = parse!(parser => Expression);

    expect_token!(parser => [Kw(Keyword::Do), ()], Kw(Keyword::Do));

    let body = parse!(parser => Chunk);

    let (_, hi) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

    Ok(Statement {
        stmt: Stmt::While { cond, body },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses numeric and generic for statement
pub fn parse_for_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    // "for" ident "in" expr "do" chunk "end"
    let (_, lo) = expect_token!(parser => [Kw(Keyword::For), ()], Kw(Keyword::For));

    let (variable, _) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    // pop the `in` keyword
    parser.pop();
    expect_token!(parser => [Kw(Keyword::In), ()], Kw(Keyword::In));

    let iterator = parse!(parser => Expression);

    expect_token!(parser => [Kw(Keyword::Do), ()], Kw(Keyword::Do));

    let body = parse!(parser => Chunk);

    let (_, hi) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

    Ok(Statement {
        stmt: Stmt::For {
            variable,
            iterator,
            body,
        },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses function definition
pub fn parse_fundef_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (vis, pub_loc) = if let Some(Kw(Keyword::Pub)) = parser.peek_tt() {
        let loc = parser.pop().unwrap().loc;
        (Vis::Public, Some(loc))
    } else {
        (Vis::Private, None)
    };

    let (_, lo) = expect_token!(parser => [Kw(Keyword::Fun), ()], Kw(Keyword::Fun));

    let lo = pub_loc.unwrap_or(lo);

    let (name, name_loc) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    expect_token!(parser => [Punct(Punctuation::LParen), ()], Punctuation::LParen);

    let mut args = Vec::new();

    loop {
        if let Some(Punct(Punctuation::RParen)) = parser.peek_tt() {
            break;
        }

        let (name, lo_arg) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punct(Punctuation::Colon));

        let typ = parse!(parser => Expression);

        args.push(Arg {
            name,
            name_loc: lo_arg.clone(),
            typ: typ.clone(),
            loc: Span::from_ends(lo_arg, typ.loc),
        });

        expect_token!(parser => [Punct(Punctuation::Comma), (); Punct(Punctuation::RParen), (), in break], Punct(Punctuation::Comma));
    }
    expect_token!(parser => [Punct(Punctuation::RParen), ()], Punct(Punctuation::RParen));

    let rettype = if let Some(Punct(Punctuation::Arrow)) = parser.peek_tt() {
        parser.pop();
        Some(parse!(parser => Expression))
    } else {
        None
    };

    let body = parse!(parser => Chunk);

    let (_, hi) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

    Ok(Statement {
        stmt: Stmt::FunDef {
            vis,
            name,
            name_loc,
            args,
            rettype,
            body,
        },
        loc: Span::from_ends(lo, hi),
    })
}

pub fn parse_return_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Return), ()], Kw(Keyword::Return));

    if parser.is_stmt_end() {
        Ok(Statement {
            stmt: Stmt::Return { val: None },
            loc: lo,
        })
    } else {
        let expr = parse!(parser => Expression);

        Ok(Statement {
            stmt: Stmt::Return {
                val: Some(expr.clone()),
            },
            loc: Span::from_ends(lo, expr.loc),
        })
    }
}

pub fn parse_break_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Break), ()], Kw(Keyword::Break));

    if parser.is_stmt_end() {
        Ok(Statement {
            stmt: Stmt::Break { val: None },
            loc: lo,
        })
    } else {
        let expr = parse!(parser => Expression);

        Ok(Statement {
            stmt: Stmt::Break {
                val: Some(expr.clone()),
            },
            loc: Span::from_ends(lo, expr.loc),
        })
    }
}

/// [ "pub" ] "var" ident [ ":" expr ] [ "=" expr ]
pub fn parse_var_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (vis, pub_loc) = if let Some(Kw(Keyword::Pub)) = parser.peek_tt() {
        let loc = parser.pop().unwrap().loc;
        (Vis::Public, Some(loc))
    } else {
        (Vis::Private, None)
    };

    let (_, lo) = expect_token!(parser => [Kw(Keyword::Var), ()], Kw(Keyword::Var));

    let lo = pub_loc.unwrap_or(lo);

    let (name, name_loc) =
        expect_token!(parser => [Ident(name), name.clone()], Ident(String::new()));

    let typ = if let Some(Punct(Punctuation::Colon)) = parser.peek_tt() {
        parser.pop();
        Some(parse!(parser => Expression))
    } else {
        None
    };

    let value = if let Some(Punct(Punctuation::Equal)) = parser.peek_tt() {
        parser.pop();
        Some(parse!(parser => Expression))
    } else {
        None
    };

    let hi = value
        .clone()
        .map(|v| v.loc.clone())
        .or(typ.clone().map(|t| t.loc))
        .unwrap_or(name_loc.clone());

    Ok(Statement {
        stmt: Stmt::VariableDef {
            vis,
            name,
            name_loc,
            typ,
            value,
        },
        loc: Span::from_ends(lo, hi),
    })
}
