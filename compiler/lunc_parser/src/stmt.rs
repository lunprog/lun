//! Parsing of lun's statements and chunk.

use lunc_utils::opt_unreachable;

use crate::expr::parse_typexpr;

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

        // TEST: no. 1
        let (_, lo) = expect_token!(parser => [LCurly, ()], LCurly);

        let mut last_expr = None;

        loop {
            match parser.peek_tt() {
                Some(EOF) | Some(RCurly) | None => {
                    break;
                }
                _ => {}
            }
            // TODO: add the semicolon to the loc of the statement / expr

            let stmt = parse!(parser => Statement);

            let next_brace = matches!(parser.peek_tt(), Some(RCurly));
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
                        opt_unreachable!()
                    };

                    last_expr = Some(Box::new(expr));

                    break;
                }
                (true, false) => {
                    // there is a statement at the end of the block and we need
                    // to parse the semicolon after appending the stmt to the
                    // block
                    stmts.push(stmt.clone());

                    // TEST: no. 2
                    expect_token!(parser => [Semi, ()], Semi);
                }
                (false, true) => {
                    // here we have a statement expression, we require a
                    // semicolon if the expression isn't a ExpressionWithBlock
                    let Statement {
                        stmt: Stmt::Expression(ref expr),
                        loc: _,
                    } = stmt
                    else {
                        // SAFETY: here we are fine because, we checked that
                        // stmt is an expr before.
                        opt_unreachable!()
                    };

                    stmts.push(stmt.clone());
                    if expr.is_expr_with_block() {
                        // TEST: n/a
                        expect_token!(parser => [Semi, ()] else { continue; });
                    } else {
                        // TEST: no. 3
                        expect_token!(parser => [Semi, ()], Semi);
                    }
                }
                (false, false) => {
                    // if the statement is a defer with a block expression
                    // inside we don't expect a semicolon
                    if !matches!(stmt.stmt, Stmt::Defer { ref expr } if expr.is_expr_with_block()) {
                        // TEST: no. 4
                        expect_token!(parser => [Semi, ()], Semi);
                    }

                    stmts.push(stmt.clone());
                }
            }
        }

        // TEST: no. 5
        let (_, hi) = expect_token!(parser => [RCurly, ()], RCurly);

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
    /// `"let" "mut"? ident [ ":" expr ] "=" expr`
    /// `ident ":" [ expr ] ":" expr ";"`
    /// `ident ":" [ expr ] "=" expr ";"`
    VariableDef {
        name: String,
        name_loc: Span,
        mutable: bool,
        typexpr: Option<Expression>,
        value: Box<Expression>,
    },
    /// defer statement
    ///
    /// `"defer" expr`
    Defer { expr: Expression },
    /// statement expression
    ///
    /// `expression`
    Expression(Expression),
}

impl AstNode for Statement {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        match parser.peek_tt() {
            Some(KwLet) => parse_variable_def_stmt(parser),
            Some(KwDefer) => parse_defer_statement(parser),
            Some(Ident(_)) if parser.is_short_variable_def() => parse_short_variable_stmt(parser),
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

impl Parser {
    pub fn is_short_variable_def(&self) -> bool {
        matches!(self.nth_tt(1), Some(Colon))
            && !matches!(self.nth_tt(2), Some(KwWhile | KwFor | KwLoop | LCurly))
    }
}

/// `"let" "mut"? ident [ ":" expr ] "=" expr`
pub fn parse_variable_def_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [KwLet, ()], KwLet);

    let mutable = if let Some(KwMut) = parser.peek_tt() {
        parser.pop();
        true
    } else {
        false
    };

    // TEST: no. 1
    let (name, name_loc) =
        expect_token!(parser => [Ident(name), name.clone()], Ident(String::new()));

    let typexpr = if let Some(Colon) = parser.peek_tt() {
        parser.pop();
        Some(parse!(@fn parser => parse_typexpr))
    } else {
        None
    };

    // TEST: no. 2
    expect_token!(parser => [Eq, ()], Eq);
    let value = parse!(box: parser => Expression);

    let hi = value.loc.clone();

    Ok(Statement {
        stmt: Stmt::VariableDef {
            name,
            name_loc,
            mutable,
            typexpr,
            value,
        },
        loc: Span::from_ends(lo, hi),
    })
}

/// `ident ":" [ expr ] ":" expr ";"`
/// `ident ":" [ expr ] "=" expr ";"`
pub fn parse_short_variable_stmt(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    // TEST: n/a
    let (name, lo) = expect_token!(parser => [Ident(id), id.clone()], [Ident(String::new())]);

    // TEST: n/a
    expect_token!(parser => [Colon, ()], Colon);

    let typexpr = match parser.peek_tt() {
        Some(Colon | Eq) => None,
        _ => Some(parse!(@fn parser => parse_typexpr)),
    };

    // TEST: no. 1
    let (mutable, _) = expect_token!(
        parser => [
            Colon, false;
            Eq, true;
        ],
        [Colon, Eq]
    );

    let value = parse!(box: parser => Expression);

    let hi = value.loc.clone();

    Ok(Statement {
        stmt: Stmt::VariableDef {
            name,
            name_loc: lo.clone(),
            mutable,
            typexpr,
            value,
        },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses a defer statement
pub fn parse_defer_statement(parser: &mut Parser) -> Result<Statement, Diagnostic> {
    // TEST: n/a
    let ((), lo) = expect_token!(parser => [KwDefer, ()], KwDefer);

    let expr = parse!(parser => Expression);

    let loc = Span::from_ends(lo, expr.loc.clone());

    Ok(Statement {
        stmt: Stmt::Defer { expr },
        loc,
    })
}
