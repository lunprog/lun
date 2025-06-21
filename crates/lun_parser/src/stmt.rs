//! Parsing of lun's statements and chunk.

use std::hint::unreachable_unchecked;

use crate::expr::parse_type_expression;

use super::*;

/// Block of Lun statements
#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<Statement>,
    pub last_expr: Option<Box<Expression>>,
    pub loc: Span,
}

impl AstNode for Block {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let mut stmts = Vec::new();

        let (_, lo) =
            expect_token!(parser => [Punct(Punctuation::LBrace), ()], Punctuation::LBrace);

        let mut last_expr = None;

        loop {
            match parser.peek_tt() {
                Some(EOF) | Some(Punct(Punctuation::RBrace)) | None => {
                    break;
                }
                _ => {}
            }
            // TODO: add the semicolon to the loc of the statement / expr

            let stmt = parse!(parser => Statement);

            let next_brace = if let Some(Punct(Punctuation::RBrace)) = parser.peek_tt() {
                true
            } else {
                false
            };
            let is_expr = stmt.is_expr();

            match (next_brace, is_expr) {
                (true, true) => {
                    // here we found the last expression, because the
                    // following token is } and the last "statement" was
                    // an expression.
                    let Statement {
                        stmt: Stmt::Expression(expr),
                        loc: _,
                    } = stmt
                    else {
                        // NOTE: here we are fine because, we checked that stmt
                        // is an expr before.
                        unsafe { unreachable_unchecked() }
                    };

                    last_expr = Some(Box::new(expr));

                    break;
                }
                // here, the next thing is a brace so, no need to keep parsing
                // there is nothing more.
                (true, false) => break,
                (false, true) => {
                    // here we have a statement expression, we require a
                    // semicolon if the expression isn't a ExpressionWithBlock
                    let Statement {
                        stmt: Stmt::Expression(ref expr),
                        loc: _,
                    } = stmt
                    else {
                        // NOTE: here we are fine because, we checked that stmt
                        // is an expr before.
                        unsafe { unreachable_unchecked() }
                    };

                    stmts.push(stmt.clone());
                    if expr.is_expr_with_block() {
                        expect_token!(parser => [Punct(Punctuation::SemiColon), ()] else { continue; });
                    } else {
                        expect_token!(parser => [Punct(Punctuation::SemiColon), ()], Punct(Punctuation::SemiColon));
                    }
                }
                (false, false) => {
                    // here, nothing fancy, we have a statement, the next
                    // thing isn't a }, so we push the Statement and expect
                    // a semicolon
                    stmts.push(stmt.clone());
                    expect_token!(parser => [Punct(Punctuation::SemiColon), ()], Punct(Punctuation::SemiColon));
                }
            }
        }

        let (_, hi) =
            expect_token!(parser => [Punct(Punctuation::RBrace), ()], Punctuation::RBrace);

        Ok(Block {
            stmts,
            last_expr,
            loc: Span::from_ends(lo, hi),
        })
    }
}

/// A lun statement
#[derive(Debug, Clone)]
pub struct Statement {
    pub stmt: Stmt,
    pub loc: Span,
}

impl Statement {
    pub fn is_expr(&self) -> bool {
        matches!(self.stmt, Stmt::Expression(_))
    }
}

#[derive(Debug, Clone)]
pub enum Stmt {
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
    /// "let" "mut"? ident [ ":" expr ] [ "=" expr ]
    VariableDef {
        name: String,
        name_loc: Span,
        mutable: bool,
        typ: Option<Expression>,
        value: Option<Expression>,
    },
    /// statement expression
    ///
    /// expression
    Expression(Expression),
}

impl AstNode for Statement {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        match parser.peek_tt() {
            Some(Kw(Keyword::Let)) => parse_variable_def_stmt(parser),
            Some(_) => {
                let expr = parse!(parser => Expression);

                Ok(Statement {
                    loc: expr.loc.clone(),
                    stmt: Stmt::Expression(expr),
                })
            }
            None => Err(parser.eof_diag()),
        }
    }
}

/// "let" "mut"? ident [ ":" expr ] [ "=" expr ]
pub fn parse_variable_def_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Let), ()], Kw(Keyword::Let));

    let mutable = if let Some(Kw(Keyword::Mut)) = parser.peek_tt() {
        parser.pop();
        true
    } else {
        false
    };

    let (name, name_loc) =
        expect_token!(parser => [Ident(name), name.clone()], Ident(String::new()));

    let typ = if let Some(Punct(Punctuation::Colon)) = parser.peek_tt() {
        parser.pop();
        Some(parse!(@fn parser => parse_type_expression))
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
            name,
            name_loc,
            mutable,
            typ,
            value,
        },
        loc: Span::from_ends(lo, hi),
    })
}
