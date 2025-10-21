//! Parsing of lun's statements and chunk.

use lunc_diag::ResultExt;
use lunc_utils::default;

use super::*;

/// Block of Lun statements
#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<Statement>,
    pub last_expr: Option<Box<Expression>>,
    pub loc: Span,
}

impl Block {
    /// Dummy block, used as a fallback to handle errors
    pub fn dummy() -> Block {
        Block {
            stmts: Vec::new(),
            last_expr: None,
            loc: Span::ZERO,
        }
    }
}

/// A lun statement
#[derive(Debug, Clone)]
pub struct Statement {
    pub stmt: StmtKind,
    pub loc: Span,
}

impl Statement {
    /// Returns true if self is [`StmtKind::Expression`]
    pub fn is_expr(&self) -> bool {
        matches!(self.stmt, StmtKind::Expression(_))
    }
}

/// Kind of statement
#[derive(Debug, Clone)]
pub enum StmtKind {
    /// variable definition
    ///
    /// `"let" "mut"? ident [ ":" typeexpr ] "=" expr`
    /// `"mut"? ident ":" typeexpr? "=" expr ";"`
    BindingDef {
        name: Spanned<String>,
        mutability: Mutability,
        typeexpr: Option<Expression>,
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

/// Parsing of statements and block.
impl Parser {
    /// Parses a block.
    pub fn parse_block(&mut self) -> IResult<Block> {
        let mut stmts = Vec::new();

        // TEST: no. 1
        let lo = self.expect(ExpToken::LCurly)?;

        let mut last_expr = None;

        loop {
            if self.eat_one_of([], [ExpToken::Eof, ExpToken::RCurly]) {
                break;
            }

            let stmt = match self.parse_stmt() {
                Ok(stmt) => stmt,
                Err(recovered) => {
                    if let Recovered::Unable(d) = recovered {
                        self.sink.emit(d);
                    }

                    // after recovering from a faulty stmt, the parser is bumped
                    // until prev_token is one of `is_stmt_end`. It's smart so
                    // he knows about opening and closing curly.
                    //
                    // After there is two options:
                    // - we keep parsing stmt / the last_expr
                    // - we are in front of the RCurly, either because the
                    //   faulty stmt was the last one or the recovery failed to
                    //   do something better.

                    self.recover_stmt_in_block();
                    continue;
                }
            };

            let next_brace = self.token.tt == RCurly;
            let is_expr = stmt.is_expr();

            match (next_brace, is_expr) {
                (true, true) => {
                    // here we found the last expression, because the
                    // following token is } and the last "statement" was
                    // an expression.
                    let Statement {
                        stmt: StmtKind::Expression(expr),
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
                    self.expect_nae(ExpToken::Semi).emit(self.x());
                }
                (false, true) => {
                    // here we have a statement expression, we require a
                    // semicolon if the expression isn't a ExpressionWithBlock
                    let Statement {
                        stmt: StmtKind::Expression(ref expr),
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
                        self.eat_no_expect(ExpToken::Semi);
                    } else {
                        // TEST: no. 3
                        self.expect(ExpToken::Semi)?;
                    }
                }
                (false, false) => {
                    // if the statement is a defer with a block expression
                    // inside we don't expect a semicolon
                    if !matches!(stmt.stmt, StmtKind::Defer { ref expr } if expr.is_expr_with_block())
                    {
                        // TEST: no. 4
                        self.expect_nae(ExpToken::Semi).emit(self.x());
                    }

                    stmts.push(stmt.clone());
                }
            }
        }

        // TEST: no. 5
        let hi = self.expect(ExpToken::RCurly)?;

        Ok(Block {
            stmts,
            last_expr,
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Tries to recover the parsing of statements in a block.
    ///
    /// The parser is bumped until prev_token is one of `is_stmt_end`. It's
    /// smart so he knows about opening and closing curly.
    ///
    /// After there is two options:
    /// - we keep parsing stmt / the last_expr
    /// - we are in front of the RCurly, either because the faulty stmt was the
    ///   last one or the recovery failed to do something better.
    pub fn recover_stmt_in_block(&mut self) {
        let mut remaining_rcurly = 0;

        while (!self.token.is_stmt_end() || self.check_no_expect(ExpToken::RCurly))
            && !self.check_no_expect(ExpToken::Eof)
        {
            if self.check_no_expect(ExpToken::LCurly) {
                remaining_rcurly += 1;
            } else if self.check_no_expect(ExpToken::RCurly) {
                if remaining_rcurly == 0 {
                    // eat the }
                    self.bump();

                    break;
                } else {
                    remaining_rcurly -= 1;
                }
            }

            self.bump();
        }

        self.bump();
    }

    /// Parses a statement
    pub fn parse_stmt(&mut self) -> IResult<Statement> {
        match self.token.tt {
            KwLet => self.parse_let_binding_stmt(),
            KwMut => self.parse_short_binding_stmt(),
            Ident(_) if self.is_short_binding_def() => self.parse_short_binding_stmt(),
            KwDefer => self.parse_defer_statement(),
            _ => {
                let expr = self.parse_expr().emit_wval(self.x(), Expression::dummy);

                Ok(Statement {
                    loc: expr.loc.clone(),
                    stmt: StmtKind::Expression(expr),
                })
            }
        }
    }

    /// Can the `token + 1` and `token + 2` tokens be the start of a short variable definition?
    pub fn is_short_binding_def(&self) -> bool {
        self.look_many_tt(1, |tts| {
            matches!(tts, [Colon, _]) && !matches!(tts, [_, KwWhile | KwFor | KwLoop | LCurly])
        })
    }

    /// Parses let-binding statement,
    ///
    /// `"let" "mut"? ident [ ":" expr ] "=" expr`
    pub fn parse_let_binding_stmt(&mut self) -> IResult<Statement> {
        // TEST: n/a
        let lo = self.expect(ExpToken::KwLet)?;

        let mutability = self.parse_mutability();

        // TEST: no. 1
        let name_loc = self.expect(ExpToken::Ident).emit_wval(self.x(), default);
        let name = self.as_ident();

        let typeexpr = if self.eat_no_expect(ExpToken::Colon) {
            Some(self.parse_typeexpr()?)
        } else {
            None
        };

        // TEST: no. 2
        self.expect(ExpToken::Eq).emit(self.x());
        let value = Box::new(self.parse_expr()?);

        let hi = value.loc.clone();

        Ok(Statement {
            stmt: StmtKind::BindingDef {
                name: Spanned {
                    node: name,
                    loc: name_loc,
                },
                mutability,
                typeexpr,
                value,
            },
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses a short binding def statement
    ///
    /// `"mut"? ident ":" typeexpr? "=" expr ";"`
    pub fn parse_short_binding_stmt(&mut self) -> IResult<Statement> {
        // TEST: n/a
        let (mutability, mut_loc) = self.parse_spanned_mutability();

        // TEST: no. 1
        let lo_ident = self.expect(ExpToken::Ident).emit_wval(self.x(), default);
        let name = self.as_ident();

        let lo = mut_loc.unwrap_or(lo_ident);

        // TEST: no. 2
        self.expect(ExpToken::Colon)?;

        let typeexpr = match self.token.tt {
            Eq => None,
            _ => Some(self.parse_typeexpr()?),
        };

        // TEST: no. 3
        self.expect(ExpToken::Eq)?;

        let value = Box::new(self.parse_expr().emit_wval(self.x(), Expression::dummy));

        let hi = value.loc.clone();

        Ok(Statement {
            stmt: StmtKind::BindingDef {
                name: Spanned {
                    node: name,
                    loc: lo.clone(),
                },
                mutability,
                typeexpr,
                value,
            },
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses a defer statement
    pub fn parse_defer_statement(&mut self) -> IResult<Statement> {
        // TEST: n/a
        let lo = self.expect(ExpToken::KwDefer)?;

        let expr = self.parse_expr()?;

        let loc = Span::from_ends(lo, expr.loc.clone());

        Ok(Statement {
            stmt: StmtKind::Defer { expr },
            loc,
        })
    }
}
