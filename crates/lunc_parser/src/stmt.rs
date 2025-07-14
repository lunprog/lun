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

            let next_brace = matches!(parser.peek_tt(), Some(Punct(Punctuation::RBrace)));
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
                        expect_token!(parser => [Punct(Punctuation::Semicolon), ()] else { continue; });
                    } else {
                        expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punct(Punctuation::Semicolon));
                    }
                }
                (false, false) => {
                    // if the statement is a defer with a block expression
                    // inside we don't expect a semicolon
                    if !matches!(stmt.stmt, Stmt::Defer { ref expr } if expr.is_expr_with_block()) {
                        expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punct(Punctuation::Semicolon));
                    }

                    stmts.push(stmt.clone());
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
    /// variable definition
    ///
    /// "let" "mut"? ident [ ":" expr ] "=" expr
    /// ident ":" [ expr ] ":" expr ";"
    /// ident ":" [ expr ] "=" expr ";"
    VariableDef {
        name: String,
        name_loc: Span,
        mutable: bool,
        typ: Option<Expression>,
        value: Box<Expression>,
    },
    /// defer statement
    ///
    /// "defer" expr
    Defer { expr: Expression },
    /// statement expression
    ///
    /// expression
    Expression(Expression),
}

impl AstNode for Statement {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        match parser.peek_tt() {
            Some(Kw(Keyword::Let)) => parse_variable_def_stmt(parser),
            Some(Kw(Keyword::Defer)) => parse_defer_statement(parser),
            Some(Ident(_)) if parser.nth_tt(1) == Some(&Punct(Punctuation::Colon)) => {
                parse_short_variable_stmt(parser)
            }
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

/// "let" "mut"? ident [ ":" expr ] "=" expr
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

    expect_token!(parser => [Punct(Punctuation::Equal), ()], Punctuation::Equal);
    let value = parse!(box: parser => Expression);

    let hi = value.loc.clone();

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

/// ident ":" [ expr ] ":" expr ";"
/// ident ":" [ expr ] "=" expr ";"
pub fn parse_short_variable_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let (name, lo) = expect_token!(parser => [Ident(id), id.clone()], [Ident(String::new())]);

    expect_token!(parser => [Punct(Punctuation::Colon), ()], Punctuation::Colon);

    let typ = match parser.peek_tt() {
        Some(Punct(Punctuation::Colon | Punctuation::Equal)) => None,
        _ => Some(parse!(@fn parser => parse_type_expression)),
    };

    let (mutable, _) = expect_token!(
        parser => [
            Punct(Punctuation::Colon), false;
            Punct(Punctuation::Equal), true;
        ],
        [Punctuation::Colon, Punctuation::Equal]
    );

    let value = parse!(box: parser => Expression);

    let hi = value.loc.clone();

    Ok(Statement {
        stmt: Stmt::VariableDef {
            name,
            name_loc: lo.clone(),
            mutable,
            typ,
            value,
        },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses a defer statement
pub fn parse_defer_statement(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    let ((), lo) = expect_token!(parser => [Kw(Keyword::Defer), ()], Kw(Keyword::Defer));

    let expr = parse!(parser => Expression);

    let loc = Span::from_ends(lo, expr.loc.clone());

    Ok(Statement {
        stmt: Stmt::Defer { expr },
        loc,
    })
}
