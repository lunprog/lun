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
        let start = parser.peek_tok().unwrap().loc.clone();
        let mut end = start.clone();

        loop {
            match parser.peek_tt() {
                Some(EOF) | Some(Kw(Keyword::End | Keyword::Else)) | None => {
                    break;
                }
                _ => {}
            }

            let stmt = parse!(parser => Statement);
            end = stmt.loc.clone();

            stmts.push(stmt);

            if let Some(Punct(Punctuation::SemiColon)) = parser.peek_tt() {
                // pop the optional semicolon
                parser.pop();
            }
        }

        Ok(Chunk {
            stmts,
            loc: Span::from_ends(start, end),
        })
    }
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
    // TODO: make the value optional so that we can define variables and
    // initiliaze them later, like:
    //
    // ```lun
    // local a: int
    //
    // // ...
    //
    // a = 24
    // ```
    //
    // but we need to ensure that a is initialized when you use it, and be able
    // to conditionally initialize it like:
    //
    // ```lun
    // local a: int
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
    //
    // here `a` is initialized conditionally, if the else cause was not present
    // `a` would be partially initialized: if the logic returned true `a` is
    // initialized but if it returned false `a` isn't initialized, and we don't
    // want uninitialized variables
    //
    /// variable definition
    ///
    /// [ "local" ] ident ":" [ expr ] "=" expr
    VariableDef {
        local: bool,
        variable: String,
        typ: Option<Expression>,
        value: Expression,
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
    /// numeric for statement
    ///
    /// "for" ident ":" [ expr ] "=" expr [ "," expr ] "do" chunk "end"
    ///                              ^ in typeck, must be of range type.
    NumericFor {
        /// variable that will contain the value that will change based on the
        /// step
        variable: String,
        /// the type of the variable, optional as usual
        var_type: Option<Expression>,
        /// initial value of the variable
        var_value: Expression,
        /// the step by which we increment the variable
        step: Option<Expression>,
        /// the body we run every step
        body: Chunk,
    },
    /// generic for statement
    ///
    /// "for" ident "in" expr "do" chunk "end"
    GenericFor {
        /// the variable that contains values of the iterator
        variable: String,
        /// the iterator
        iterator: Expression,
        /// the body we run every time the iterator return something non-nil.
        body: Chunk,
    },
    /// function definition
    ///
    /// [ "local" ] "fun" ident "(" ( ident ":" expr ),* ")" [ "->" expr ] chunk "end"
    FunDef {
        local: bool,
        name: String,
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
    pub typ: Expression,
    pub loc: Span,
}

impl AstNode for Statement {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        match parser.peek_tt() {
            Some(Kw(Keyword::Local)) => match parser.nth_tt(1) {
                Some(Ident(_)) => parse_ident_stmt(parser),
                Some(Kw(Keyword::Fun)) => parse_fundef_stmt(parser),
                Some(_) => {
                    // we can unwrap here, we know there is a token
                    let t = parser.pop().unwrap();

                    Err(ExpectedToken::new(
                        [Ident(String::new()), Kw(Keyword::Fun)],
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
            Some(_) => {
                // unwrap is safe because we already know the next has a token
                // type
                let t = parser.peek_tok().unwrap().clone();
                // TODO: make the parser retry if he failed to parse the
                // statement with a loop, see parsing of expressions also
                Err(ExpectedToken::new(
                    [
                        Ident(String::new()),
                        Kw(Keyword::Local),
                        Kw(Keyword::If),
                        Kw(Keyword::Do),
                        Kw(Keyword::While),
                        Kw(Keyword::For),
                        Kw(Keyword::Fun),
                        Kw(Keyword::Return),
                        Kw(Keyword::Break),
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
    let (local, local_loc) = if let Some(Kw(Keyword::Local)) = parser.peek_tt() {
        let loc = parser.pop().unwrap().loc;
        (true, Some(loc))
    } else {
        (false, None)
    };

    let (variable, lo) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

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
                loc: Span::from_ends(local_loc.unwrap_or(lo), value.loc.clone()),
                stmt: Stmt::VariableDef {
                    local,
                    variable,
                    typ,
                    value,
                },
            })
        }
        Some(Punct(Punctuation::LParen)) => {
            if local {
                // a function call can't be prefixed by "local"
                parser.sink.push(ExpectedToken::new(
                    Ident(String::new()),
                    Kw(Keyword::Local),
                    Some("statement"),
                    local_loc.unwrap(),
                ));
            }
            // we pop the ( no need of expect_token! we already know it is (
            parser.pop();

            let mut args = Vec::new();

            let end = loop {
                if let Some(Punct(Punctuation::RParen)) = parser.peek_tt() {
                    break parser.pop().unwrap().loc;
                }

                let arg = parse!(parser => Expression);
                args.push(arg);

                expect_token!(parser => [Punct(Punctuation::Comma), ()], Punct(Punctuation::Comma));
            };

            Ok(Statement {
                stmt: Stmt::FunCall {
                    name: variable,
                    args,
                },
                loc: Span::from_ends(lo, end),
            })
        }
        _ => {
            if local {
                // a variable assignement can't be prefixed by "local"
                parser.sink.push(ExpectedToken::new(
                    Ident(String::new()),
                    Kw(Keyword::Local),
                    Some("statement"),
                    local_loc.unwrap(),
                ));
            }

            expect_token!(parser => [Punct(Punctuation::Equal), ()], Punctuation::Equal);

            let value = parse!(parser => Expression);

            Ok(Statement {
                loc: Span::from_ends(lo, value.loc.clone()),
                stmt: Stmt::Assignement { variable, value },
            })
        }
    }
}

/// parses if statements
pub fn parse_if_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (_, start) = expect_token!(parser => [Kw(Keyword::If), ()], Kw(Keyword::If));

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

    let (_, end) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

    Ok(Statement {
        stmt: Stmt::IfThenElse {
            cond,
            body,
            else_ifs,
            else_body,
        },
        loc: Span::from_ends(start, end),
    })
}

/// parses do block statement
pub fn parse_do_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (_, start) = expect_token!(parser => [Kw(Keyword::Do), ()], Kw(Keyword::Do));

    let body = parse!(parser => Chunk);

    let (_, end) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

    Ok(Statement {
        stmt: Stmt::DoBlock { body },
        loc: Span::from_ends(start, end),
    })
}

/// parses while statement
pub fn parse_while_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (_, start) = expect_token!(parser => [Kw(Keyword::While), ()], Kw(Keyword::While));

    let cond = parse!(parser => Expression);

    expect_token!(parser => [Kw(Keyword::Do), ()], Kw(Keyword::Do));

    let body = parse!(parser => Chunk);

    let (_, end) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

    Ok(Statement {
        stmt: Stmt::While { cond, body },
        loc: Span::from_ends(start, end),
    })
}

/// parses numeric and generic for statement
pub fn parse_for_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (_, start) = expect_token!(parser => [Kw(Keyword::For), ()], Kw(Keyword::For));

    let (variable, _) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    match parser.peek_tt() {
        Some(Punct(Punctuation::Colon)) => {
            // numeric for:
            // "for" ident ":" [ expr ] "=" expr [ "," expr ] "do" chunk "end"
            //
            // pop the colon
            parser.pop();

            let var_type = if let Some(Punct(Punctuation::Equal)) = parser.peek_tt() {
                None
            } else {
                Some(parse!(parser => Expression))
            };

            expect_token!(parser => [Punct(Punctuation::Equal), ()], Punctuation::Equal);

            let var_value = parse!(parser => Expression);

            let step = if let Some(Punct(Punctuation::Comma)) = parser.peek_tt() {
                None
            } else {
                parser.pop();
                Some(parse!(parser => Expression))
            };

            expect_token!(parser => [Kw(Keyword::Do), ()], Kw(Keyword::Do));

            let body = parse!(parser => Chunk);

            let (_, end) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

            Ok(Statement {
                stmt: Stmt::NumericFor {
                    variable,
                    var_type,
                    var_value,
                    step,
                    body,
                },
                loc: Span::from_ends(start, end),
            })
        }
        Some(Kw(Keyword::In)) => {
            // generic for:
            // "for" ident "in" expr "do" chunk "end"
            //
            // pop the `in` keyword
            parser.pop();

            let iterator = parse!(parser => Expression);

            expect_token!(parser => [Kw(Keyword::Do), ()], Kw(Keyword::Do));

            let body = parse!(parser => Chunk);

            let (_, end) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

            Ok(Statement {
                stmt: Stmt::GenericFor {
                    variable,
                    iterator,
                    body,
                },
                loc: Span::from_ends(start, end),
            })
        }
        Some(_) => {
            // we can unwrap because we know there is a token
            let t = parser.pop().unwrap();

            Err(ExpectedToken::new(
                [Punct(Punctuation::Colon), Kw(Keyword::In)],
                t.tt,
                Some("for statement"),
                t.loc,
            )
            .into_diag())
        }
        None => Err(parser.eof_diag()),
    }
}

/// parses function definition
pub fn parse_fundef_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (local, local_loc) = if let Some(Kw(Keyword::Local)) = parser.peek_tt() {
        let loc = parser.pop().unwrap().loc;
        (true, Some(loc))
    } else {
        (false, None)
    };

    let (_, lo) = expect_token!(parser => [Kw(Keyword::Fun), ()], Kw(Keyword::Fun));

    let start = local_loc.unwrap_or(lo);

    let (name, _) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    expect_token!(parser => [Punct(Punctuation::LParen), ()], Punctuation::LParen);

    let mut args = Vec::new();

    loop {
        if let Some(Punct(Punctuation::RParen)) = parser.peek_tt() {
            break;
        }

        let (name, start_arg) =
            expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punct(Punctuation::Colon));

        let typ = parse!(parser => Expression);

        args.push(Arg {
            name,
            typ: typ.clone(),
            loc: Span::from_ends(start_arg, typ.loc),
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

    let (_, end) = expect_token!(parser => [Kw(Keyword::End), ()], Kw(Keyword::End));

    Ok(Statement {
        stmt: Stmt::FunDef {
            local,
            name,
            args,
            rettype,
            body,
        },
        loc: Span::from_ends(start, end),
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
