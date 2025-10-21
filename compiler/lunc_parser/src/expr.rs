//! Parsing of lun's expressions.

use lunc_ast::{BinOp, Mutability, UnOp};
use lunc_diag::ResultExt;
use lunc_token::Lit;
use lunc_utils::opt_unreachable;

use crate::stmt::Block;

use super::*;

/// The associativity, is used to parse the binary operations
#[derive(Clone, Debug, PartialEq)]
pub enum Associativity {
    LeftToRight,
    RightToLeft,
    None,
}

/// Expression in lun.
#[derive(Debug, Clone)]
pub struct Expression {
    pub kind: ExprKind,
    pub loc: Span,
}

impl Expression {
    /// Dummy expression, used as a fallback value when trying to parse.
    pub const DUMMY: Expression = Expression {
        kind: ExprKind::Null,
        loc: Span::ZERO,
    };

    /// Used by `emit_wval` as a fallback value.
    pub const fn dummy() -> Expression {
        Expression::DUMMY
    }

    /// Is the expression `ExpressionWithBlock`?
    pub fn is_expr_with_block(&self) -> bool {
        matches!(
            self.kind,
            ExprKind::If(_)
                | ExprKind::Block(_)
                | ExprKind::BlockWithLabel { .. }
                | ExprKind::PredicateLoop { .. }
                | ExprKind::IteratorLoop { .. }
                | ExprKind::FunDefinition { .. }
                | ExprKind::InfiniteLoop { .. }
        )
    }
}

/// Kind of expression.
#[derive(Debug, Clone)]
pub enum ExprKind {
    /// boolean literal expression
    ///
    /// `"true" | "false"`
    BoolLit(bool),
    /// literal expression
    ///
    /// `integer | string | c_str | char | float`
    Lit(Lit),
    /// parenthesis expression
    ///
    /// `"(" expr ")"`
    Paren(Box<Expression>),
    /// an identifier expression
    ///
    /// `ident`
    Ident(String),
    // /// a path expression
    // ///
    /// e.g: `abc`, `core::panic`, `core::Number::max`
    // Path(Path),
    /// binary operation
    ///
    /// `expr op expr`
    Binary {
        lhs: Box<Expression>,
        op: BinOp,
        rhs: Box<Expression>,
    },
    /// unary operation
    ///
    /// `op expr`
    Unary { op: UnOp, expr: Box<Expression> },
    /// Borrow operator
    ///
    /// `"&" "mut"? expression`
    Borrow(Mutability, Box<Expression>),
    /// function call expression
    ///
    /// `expr "(" ( expr ),* ")"`
    Call {
        callee: Box<Expression>,
        args: Vec<Expression>,
    },
    /// if else expression
    ///
    /// `"if" expression block [ "else" (if-expr | block-expr) ]`
    If(IfExpression),
    /// if then else expression
    ///
    /// `"if" expression "then" expression "else" expression`
    IfThenElse {
        cond: Box<Expression>,
        true_val: Box<Expression>,
        false_val: Box<Expression>,
    },
    /// block expression
    // TODO: make the grammar for block expr
    Block(Block),
    /// block with label
    BlockWithLabel {
        label: Spanned<String>,
        block: Block,
    },
    /// predicate loop expression
    ///
    /// `"while" expression block`
    PredicateLoop {
        label: Option<Spanned<String>>,
        cond: Box<Expression>,
        body: Block,
    },
    /// iterator loop expression
    ///
    /// `"for" ident "in" expression block`
    IteratorLoop {
        label: Option<Spanned<String>>,
        variable: String,
        iterator: Box<Expression>,
        body: Block,
        // NOTE: this is used to emit the diagnostic `feature_todo`.
        loc: Span,
    },
    /// infinite loop
    ///
    /// `"loop" block`
    InfiniteLoop {
        label: Option<Spanned<String>>,
        body: Block,
    },
    /// return expression
    ///
    /// `"return" expression?`
    Return { expr: Option<Box<Expression>> },
    /// break expression
    ///
    /// `"break" [ ":" ident ] expression?`
    Break {
        label: Option<String>,
        expr: Option<Box<Expression>>,
    },
    /// continue expression
    ///
    /// `"continue"`
    Continue { label: Option<String> },
    /// null expression
    ///
    /// `"null"`
    Null,
    /// field expression
    ///
    /// `expr "." ident`
    Field {
        expr: Box<Expression>,
        member: String,
    },
    /// orb expression
    ///
    /// `"orb"`
    Orb,
    //
    // definitions
    //
    /// function definition expression
    ///
    /// `"fun" "(" ( ident ":" expr ),* ")" [ "->" expr ] block`
    FunDefinition {
        args: Vec<Arg>,
        rettypeexpr: Option<Box<Expression>>,
        body: Block,
    },
    /// function declaration expression
    ///
    /// `"fun" "(" ( expr ),* ")" [ "->" expr ]`
    FunDeclaration {
        args: Vec<Expression>,
        rettypeexpr: Option<Box<Expression>>,
    },
    //
    // type expression
    //
    /// pointer type expression
    ///
    /// `"*" "mut"? expression`
    PointerType(Mutability, Box<Expression>),
    /// function pointer type
    ///
    /// `"*" "fun" "(" ( expr ),* ")" [ "->" expr ]`
    FunPtrType {
        args: Vec<Expression>,
        ret: Option<Box<Expression>>,
    },
}

#[derive(Debug, Clone)]
pub struct IfExpression {
    pub cond: Box<Expression>,
    pub body: Box<Block>,
    pub else_br: Option<Box<Else>>,
    pub loc: Span,
}

#[derive(Debug, Clone)]
pub enum Else {
    IfExpr(IfExpression),
    Block(Block),
}

#[derive(Debug, Clone)]
pub struct Arg {
    pub name: String,
    pub name_loc: Span,
    pub typeexpr: Expression,
    pub loc: Span,
}

/// The precedence table of Lun
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    // `None` is a special precedence value, it is used to exit out of the loop
    // when a non expression token is after an expression. It is not the
    // `HIGHEST_PRECEDENCE` for the same reason.
    #[doc(hidden)]
    __First__,
    // /!\ Attention /!\
    //
    // If you change the highest precedence in this enumeration change the
    // HIGHEST_PRECEDENCE constant
    //
    /// `a = b`
    Assignment,
    /// `a or b`
    LogicalOr,
    /// `a and b`
    LogicalAnd,
    /// `a < b ; a > b ; a <= b ; a >= b`
    Comparison,
    /// `a == b ; a != b`
    Equality,
    /// `a | b`
    BitwiseOr,
    /// `a ^ b`
    BitwiseXor,
    /// `a & b`
    BitwiseAnd,
    /// `a >> b ; a << b`
    Shift,
    /// `a + b ; a - b`
    Term,
    /// `a * b ; a / b ; a % b`
    Factor,
    /// `op expression`
    Unary,
    /// `expression "(" expression,* ")"`
    Call,
    /// `expression "." ident`
    MemberAccess,
    /// `intlit "true" "false" charlit strlit group`
    Primary,
    // Like `__First__` it is a special variant of `Precedence` that should
    // never be used.
    #[doc(hidden)]
    __Last__,
}

impl Precedence {
    /// Returns the [`Precedence`] following the one passed as arg.
    pub fn next(self) -> Precedence {
        match self {
            Self::__First__ => Self::Assignment,
            Self::Assignment => Self::LogicalOr,
            Self::LogicalOr => Self::LogicalAnd,
            Self::LogicalAnd => Self::Comparison,
            Self::Comparison => Self::Equality,
            Self::Equality => Self::BitwiseOr,
            Self::BitwiseOr => Self::BitwiseXor,
            Self::BitwiseXor => Self::BitwiseAnd,
            Self::BitwiseAnd => Self::Shift,
            Self::Shift => Self::Term,
            Self::Term => Self::Factor,
            Self::Factor => Self::Unary,
            Self::Unary => Self::Call,
            Self::Call => Self::MemberAccess,
            Self::MemberAccess => Self::Primary,
            Self::Primary => Self::__Last__,
            Self::__Last__ => unreachable!(),
        }
    }

    pub fn associativity(&self) -> Associativity {
        match self {
            Self::Assignment => Associativity::RightToLeft,
            Self::LogicalOr => Associativity::LeftToRight,
            Self::LogicalAnd => Associativity::LeftToRight,
            Self::Comparison => Associativity::LeftToRight,
            Self::Equality => Associativity::LeftToRight,
            Self::BitwiseOr => Associativity::LeftToRight,
            Self::BitwiseXor => Associativity::LeftToRight,
            Self::BitwiseAnd => Associativity::LeftToRight,
            Self::Shift => Associativity::LeftToRight,
            Self::Term => Associativity::LeftToRight,
            Self::Factor => Associativity::LeftToRight,
            Self::Unary => Associativity::RightToLeft,
            Self::Call => Associativity::LeftToRight,
            Self::MemberAccess => Associativity::LeftToRight,
            Self::Primary => Associativity::LeftToRight,
            Self::__Last__ | Self::__First__ => unreachable!(),
        }
    }
}

impl Precedence {
    fn from(value: &TokenType) -> Option<Precedence> {
        match value {
            Eq => Some(Precedence::Assignment),
            AndAnd => Some(Precedence::LogicalOr),
            OrOr => Some(Precedence::LogicalAnd),
            Lt | Gt | LtEq | GtEq => Some(Precedence::Comparison),
            EqEq | BangEq => Some(Precedence::Equality),
            Or => Some(Precedence::BitwiseOr),
            Caret => Some(Precedence::BitwiseXor),
            And => Some(Precedence::BitwiseAnd),
            LtLt | GtGt => Some(Precedence::Shift),
            Plus | Minus => Some(Precedence::Term),
            Star | Slash | Percent => Some(Precedence::Factor),
            LParen => Some(Precedence::Call),
            Dot => Some(Precedence::MemberAccess),
            DotStar => Some(Precedence::Primary),
            _ => None,
        }
    }
}

/// The highest precedence of [`Precedence`]
pub const HIGHEST_PRECEDENCE: Precedence = Precedence::Assignment;

/// Expression parsing
impl Parser {
    /// Parses a Lun Expression
    pub fn parse_expr(&mut self) -> IResult<Expression> {
        self.parse_expr_precedence(self.default_precedence())
    }

    /// Parses an expressions without restrictions, used when restrictions are
    /// reset like in parenthesis, block, calls etc. The restrictions are reset
    /// to the old restrictions after parsing the expression
    pub fn parse_expr_reset(&mut self) -> IResult<Expression> {
        self.with_rest(Restrictions::empty(), Parser::parse_expr)
    }

    /// Gets the default precedence for parsing expressions.
    pub fn default_precedence(&self) -> Precedence {
        if self.restrictions.contains(Restrictions::TYPEEXPR) {
            Precedence::LogicalOr
        } else {
            HIGHEST_PRECEDENCE
        }
    }

    /// Parses a type expression with the correct restrictions.
    pub fn parse_typeexpr(&mut self) -> IResult<Expression> {
        self.with_rest(Restrictions::TYPEEXPR, Parser::parse_expr)
    }

    /// Parses an expression given the following precedence.
    ///
    /// Please use [`Parser::parse_typeexpr`] or [`Parser::parse_expr`] for
    /// correct parsing with the correct restrictions.
    pub fn parse_expr_precedence(&mut self, precedence: Precedence) -> IResult<Expression> {
        let mut lhs = match &self.token.tt {
            Lit(..) => self.parse_lit_expr()?,
            KwTrue | KwFalse => self.parse_boollit_expr()?,
            LParen => self.parse_paren_expr()?,
            Ident(_)
                if !self.restrictions.contains(Restrictions::TYPEEXPR)
                    && self.is_labeled_expr() =>
            {
                match self.look_ahead(2, look_tt) {
                    KwLoop => self.parse_infinite_loop_expr()?,
                    KwWhile => self.parse_predicate_loop_expr()?,
                    KwFor => self.parse_iterator_loop_expr()?,
                    LCurly => self.parse_block_expr()?,
                    // SAFETY: we checked in the if of the match arm that it can only
                    // be a keyword and one of loop, while or for
                    _ => opt_unreachable!(),
                }
            }
            Ident(_) => self.parse_ident_expr()?,
            KwFun => self.parse_funkw_expr()?,
            KwIf => self.parse_if_else_expr(false)?,
            KwWhile => self.parse_predicate_loop_expr()?,
            KwFor => self.parse_iterator_loop_expr()?,
            KwLoop => self.parse_infinite_loop_expr()?,
            KwReturn => self.parse_return_expr()?,
            KwBreak => self.parse_break_expr()?,
            KwContinue => self.parse_continue_expr()?,
            KwNull => self.parse_null_expr()?,
            KwOrb => self.parse_orb_expr()?,
            LCurly => self.parse_block_expr()?,
            And => self.parse_borrow_expr()?,
            Star if self.look_ahead(1, |t| t.tt == TokenType::KwFun) => {
                self.parse_funptr_typeexpr()?
            }
            Star => self.parse_pointer_typeexpr()?,
            tt if UnOp::left_from_token(tt).is_some() => self.parse_unary_left_expr()?,
            _ => {
                self.bump();

                // TEST: no. 1
                return Err(ExpectedToken::new(["expression"], self.prev_token.clone()).into());
            }
        };

        loop {
            let Some(pr) = Precedence::from(&self.token.tt) else {
                // the next token isn't part of a post expression
                break;
            };

            if precedence > pr {
                break;
            }

            lhs = match &self.token.tt {
                LParen => self.parse_call_expr(Box::new(lhs))?,
                Dot => self.parse_field_expr(lhs)?,
                maybe_bin_op if BinOp::from_tt(maybe_bin_op).is_some() => {
                    self.parse_binary_expr(lhs)?
                }
                maybe_right_op if UnOp::right_from_token(maybe_right_op).is_some() => {
                    self.parse_unary_right_expr(lhs)?
                }
                _ => break,
            };
        }

        Ok(lhs)
    }

    /// Checks for `:`, `"while" | "for" | "loop" | "{"` tokens.
    pub fn is_labeled_expr(&self) -> bool {
        self.look_many_tt(1, |t| {
            matches!(t, [Colon, KwWhile | KwFor | KwLoop | LCurly])
        })
    }

    /// Parses a literal expression
    pub fn parse_lit_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        if let Some(lit) = self.eat_lit() {
            Ok(Expression {
                kind: ExprKind::Lit(lit),
                loc: self.token_loc(),
            })
        } else {
            self.bump();

            Err(ExpectedToken::new(["literal"], self.prev_token.clone()).into())
        }
    }

    /// Parses a boolean literal expression
    pub fn parse_boollit_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        if self.eat(ExpToken::KwTrue) {
            Ok(Expression {
                kind: ExprKind::BoolLit(true),
                loc: self.token_loc(),
            })
        } else if self.eat(ExpToken::KwFalse) {
            Ok(Expression {
                kind: ExprKind::BoolLit(false),
                loc: self.token_loc(),
            })
        } else {
            self.etd_and_bump()
        }
    }

    /// Parses a parenthesis expression
    pub fn parse_paren_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let lo = self.expect(ExpToken::LParen)?;

        // TEST: n/a
        let expr = self
            .parse_expr_reset()
            .emit_wval(self.x(), Expression::dummy);

        // TEST: yes
        self.expect_nae(ExpToken::RParen).emit(self.x());

        let hi = self.token_loc();

        Ok(Expression {
            kind: ExprKind::Paren(Box::new(expr)),
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses an identifier expression
    pub fn parse_ident_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let loc = self.expect(ExpToken::Ident)?;
        let id = self.as_ident();

        Ok(Expression {
            kind: ExprKind::Ident(id),
            loc,
        })
    }

    /// Parses binary expression, `expression op expression`
    pub fn parse_binary_expr(&mut self, lhs: Expression) -> IResult<Expression> {
        let (op, tt) = match BinOp::from_tt(&self.token.tt) {
            Some(op) => {
                self.bump();
                let tt = &self.prev_token.tt;

                (op, tt)
            }
            None => {
                // TEST: n/a
                return Err(ExpectedToken::new(["binary operator"], self.token.clone()).into());
            }
        };

        let Some(mut pr) = Precedence::from(tt) else {
            // SAFETY: we can't reach here because we already checked that our token is a
            // binary operator like those we want in this function
            opt_unreachable!()
        };

        if pr.associativity() == Associativity::LeftToRight {
            pr = pr.next();
        }

        let rhs = self
            .parse_expr_precedence(pr)
            .emit_wval(self.x(), Expression::dummy);
        let loc = Span::from_ends(lhs.loc.clone(), rhs.loc.clone());

        Ok(Expression {
            kind: ExprKind::Binary {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            },
            loc,
        })
    }

    /// Parses unary expression, `op expression`
    pub fn parse_unary_left_expr(&mut self) -> IResult<Expression> {
        let (op, lo) = if let Some(op) = UnOp::left_from_token(&self.token.tt) {
            self.bump();

            (op, self.token_loc())
        } else {
            return Err(ExpectedToken::new(["unary operator"], self.token.clone()).into());
        };

        let expr = self
            .parse_expr_precedence(Precedence::Unary)
            .emit_wval(self.x(), Expression::dummy);

        Ok(Expression {
            loc: Span::from_ends(lo, expr.loc.clone()),
            kind: ExprKind::Unary {
                op,
                expr: Box::new(expr),
            },
        })
    }

    /// Parses the call expression
    pub fn parse_call_expr(&mut self, called: Box<Expression>) -> IResult<Expression> {
        let lo = called.loc.clone();
        // TEST: n/a
        self.expect(ExpToken::LParen)?;

        let mut args = Vec::new();

        loop {
            if self.eat_no_expect(ExpToken::RParen) {
                break;
            }

            match self.parse_expr_reset() {
                Ok(arg) => {
                    args.push(arg);
                }
                Err(recovered) => {
                    if let Recovered::Unable(d) = recovered {
                        self.sink.emit(d);
                    }

                    self.recover_expr_in_paren_seq();
                }
            }

            // TEST: yes
            if self.eat(ExpToken::Comma) {
                // nothing it was expected..
            } else if self.eat(ExpToken::RParen) {
                // finished to parse the call expr
                break;
            } else {
                let diag = self.expected_diag();
                self.sink.emit(diag);

                // recover the parsing, not important if we skip a lot of tokens
                // and maybe until ).
                self.recover_expr_in_paren_seq();
            }
        }

        let hi = self.token_loc();

        Ok(Expression {
            kind: ExprKind::Call {
                callee: called,
                args,
            },
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Tries to recover the parsing of expression inside of a paren seq: two
    /// parenthesis with something inside it and commas between, like the parens
    /// of the call expression or the parens of the fundef/fundecl expression.
    ///
    /// After the recovery, [`Parser::token`] will be one of:
    /// - `Comma`
    /// - `RParen`
    /// - `Eof`
    pub fn recover_expr_in_paren_seq(&mut self) {
        let mut remaining_rparen = 0;

        while !(self.check_no_expect(ExpToken::Comma)
            || self.check_no_expect(ExpToken::RParen)
            || self.check_no_expect(ExpToken::Eof))
        {
            if self.check_no_expect(ExpToken::LParen) {
                remaining_rparen += 1;
            } else if self.check_no_expect(ExpToken::RParen) {
                if remaining_rparen == 0 {
                    // eat the )
                    self.bump();

                    break;
                } else {
                    remaining_rparen -= 1;
                }
            }

            self.bump();
        }
    }

    /// Parses the function definition / declaration expression
    pub fn parse_funkw_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let lo = self.expect(ExpToken::KwFun)?;

        // TEST: no. 1
        self.expect_nae(ExpToken::LParen)?;

        match (&self.token.tt, self.look_ahead(1, look_tt)) {
            (Ident(_), Colon) => {
                // function definition
                //
                // we currently know about the tokens:
                // KwFun, LParen, Ident, Colon, ...
                //                ^^^^^ self.token

                let mut args = Vec::new();

                loop {
                    if self.check(ExpToken::RParen) {
                        break;
                    }

                    // TEST: n/a
                    self.expect_nae(ExpToken::Ident).emit(self.x());
                    let lo_arg = self.token_loc();
                    let name = self.as_ident();

                    // TEST: n/a
                    self.expect_nae(ExpToken::Colon).emit(self.x());

                    match self.parse_typeexpr() {
                        Ok(t) => {
                            args.push(Arg {
                                name,
                                name_loc: lo_arg.clone(),
                                typeexpr: t.clone(),
                                loc: Span::from_ends(lo_arg, t.loc),
                            });
                        }
                        Err(recovered) => {
                            if let Recovered::Unable(d) = recovered {
                                self.sink.emit(d);
                            }

                            self.recover_expr_in_paren_seq();
                        }
                    }

                    // TEST: no. 2 and no. 3
                    if self.eat(ExpToken::Comma) {
                        // nothing it was expected..
                    } else if self.eat(ExpToken::RParen) {
                        // finished to parse the call expr
                        break;
                    } else {
                        return self.etd_and_bump();
                    }
                }

                let rettypeexpr = if self.eat_no_expect(ExpToken::MinusGt) {
                    match self.parse_typeexpr() {
                        Ok(t) => Some(Box::new(t)),
                        Err(recovered) => {
                            if let Recovered::Unable(d) = recovered {
                                self.sink.emit(d);
                            }

                            None
                        }
                    }
                } else {
                    None
                };

                let body = self
                    .with_rest(Restrictions::empty(), Parser::parse_block)
                    .emit_wval(self.x(), Block::dummy);
                let hi = body.loc.clone();

                Ok(Expression {
                    kind: ExprKind::FunDefinition {
                        args,
                        rettypeexpr,
                        body,
                    },
                    loc: Span::from_ends(lo, hi),
                })
            }
            (RParen, _) => {
                // ambiguous
                //
                // we currently know about the tokens:
                // KwFun, LParen, RParen, ...
                //                ^^^^^^ self.token

                // TEST: n/a
                let hi_paren = self.expect(ExpToken::RParen)?;

                let rettypeexpr = if self.eat_no_expect(ExpToken::MinusGt) {
                    match self.parse_typeexpr() {
                        Ok(t) => Some(Box::new(t)),
                        Err(recovered) => {
                            if let Recovered::Unable(d) = recovered {
                                self.sink.emit(d);
                            }

                            None
                        }
                    }
                } else {
                    None
                };

                if self.token.is_stmt_end() {
                    // function declaration

                    let hi = rettypeexpr
                        .as_ref()
                        .map(|typeexpr| typeexpr.loc.clone())
                        .unwrap_or(hi_paren);

                    Ok(Expression {
                        kind: ExprKind::FunDeclaration {
                            args: Vec::new(),
                            rettypeexpr,
                        },
                        loc: Span::from_ends(lo, hi),
                    })
                } else {
                    // function definition

                    let body = self
                        .with_rest(Restrictions::empty(), Parser::parse_block)
                        .emit_wval(self.x(), Block::dummy);
                    let hi = body.loc.clone();

                    Ok(Expression {
                        kind: ExprKind::FunDefinition {
                            args: Vec::new(),
                            rettypeexpr,
                            body,
                        },
                        loc: Span::from_ends(lo, hi),
                    })
                }
            }
            _ => {
                // function declaration

                let mut args = Vec::new();

                loop {
                    if self.eat_no_expect(ExpToken::RParen) {
                        break;
                    }

                    match self.parse_typeexpr() {
                        Ok(t) => {
                            args.push(t);
                        }
                        Err(recovered) => {
                            if let Recovered::Unable(d) = recovered {
                                self.sink.emit(d);
                            }

                            self.recover_expr_in_paren_seq();
                        }
                    }

                    // TEST: no. 4
                    if self.eat(ExpToken::Comma) {
                        // nothing it was expected..
                    } else if self.eat(ExpToken::RParen) {
                        // finished to parse the call expr
                        break;
                    } else {
                        return self.etd_and_bump();
                    }
                }
                // TEST: n/a
                let hi_paren = self.token.loc.clone();

                let rettypeexpr = if self.eat_no_expect(ExpToken::MinusGt) {
                    match self.parse_typeexpr() {
                        Ok(t) => Some(Box::new(t)),
                        Err(recovered) => {
                            if let Recovered::Unable(d) = recovered {
                                self.sink.emit(d);
                            }

                            None
                        }
                    }
                } else {
                    None
                };

                let hi = rettypeexpr
                    .as_ref()
                    .map(|typeexpr| typeexpr.loc.clone())
                    .unwrap_or(hi_paren);

                Ok(Expression {
                    kind: ExprKind::FunDeclaration { args, rettypeexpr },
                    loc: Span::from_ends(lo, hi),
                })
            }
        }
    }

    /// Parses the if-else expression
    pub fn parse_if_else_expr(&mut self, only_block: bool) -> IResult<Expression> {
        // TEST: n/a
        let lo = self.expect(ExpToken::KwIf)?;

        let cond = Box::new(
            self.parse_expr_reset()
                .emit_wval(self.x(), Expression::dummy),
        );

        if self.check(ExpToken::LCurly) {
            // if expr
            // "if" expression block [ "else" (if-expr | block-expr) ]
            let body = Box::new(self.with_rest(Restrictions::empty(), Parser::parse_block)?);

            let mut hi = body.loc.clone();

            let else_br = if self.eat_no_expect(ExpToken::KwElse) {
                let else_branch = if self.check(ExpToken::KwIf) {
                    // nested if with blocks
                    let Expression {
                        kind: ExprKind::If(if_expr),
                        loc: _,
                    } = self.parse_if_else_expr(true)?
                    else {
                        // SAFETY: parse_if_else_expr only produces like that one.
                        opt_unreachable!();
                    };
                    hi = if_expr.loc.clone();

                    Else::IfExpr(if_expr)
                } else if self.check(ExpToken::LCurly) {
                    // block
                    let block = self.with_rest(Restrictions::empty(), Parser::parse_block)?;

                    hi = block.loc.clone();

                    Else::Block(block)
                } else {
                    // TEST: no. 2
                    return self.etd_and_bump();
                };

                Some(Box::new(else_branch))
            } else {
                None
            };

            let loc = Span::from_ends(lo, hi);

            Ok(Expression {
                kind: ExprKind::If(IfExpression {
                    cond,
                    body,
                    else_br,
                    loc: loc.clone(),
                }),
                loc,
            })
        } else if !only_block {
            // if then else expr
            // "if" expression then expression "else" expression

            // TEST: n/a
            self.expect(ExpToken::KwThen)?;
            let true_val = Box::new(self.parse_expr_reset()?);
            // TEST: no. 1
            self.expect(ExpToken::KwElse)?;
            let false_val = Box::new(self.parse_expr_reset()?);

            let hi = false_val.loc.clone();

            Ok(Expression {
                kind: ExprKind::IfThenElse {
                    cond,
                    true_val,
                    false_val,
                },
                loc: Span::from_ends(lo, hi),
            })
        } else {
            // TEST: no. 3
            self.etd_and_bump()
        }
    }

    /// Parses the label of an expression that can be labeled if any.
    pub fn parse_label_in_expr(&mut self) -> IResult<Option<Spanned<String>>> {
        if self.eat_no_expect(ExpToken::Ident) {
            let id = self.as_ident();
            let loc = self.token_loc();

            // TEST: n/a
            self.expect(ExpToken::Colon)?;

            Ok(Some(Spanned { node: id, loc }))
        } else {
            Ok(None)
        }
    }

    /// Parses block expression
    pub fn parse_block_expr(&mut self) -> IResult<Expression> {
        let label = self.parse_label_in_expr()?;
        let block = self.with_rest(Restrictions::empty(), Parser::parse_block)?;

        if let Some(label) = label {
            let lo = label.loc.clone();
            let hi = block.loc.clone();

            Ok(Expression {
                kind: ExprKind::BlockWithLabel { label, block },
                loc: Span::from_ends(lo, hi),
            })
        } else {
            Ok(Expression {
                loc: block.loc.clone(),
                kind: ExprKind::Block(block),
            })
        }
    }

    /// Parses predicate loop expression
    pub fn parse_predicate_loop_expr(&mut self) -> IResult<Expression> {
        let label = self.parse_label_in_expr()?;

        // TEST: n/a
        let lo_while = self.expect(ExpToken::KwWhile)?;
        let lo = label.as_ref().map(|l| l.loc.clone()).unwrap_or(lo_while);

        let cond = Box::new(self.parse_expr().emit_wval(self.x(), Expression::dummy));
        let body = self
            .with_rest(Restrictions::empty(), Parser::parse_block)
            .emit_wval(self.x(), Block::dummy);

        let hi = body.loc.clone();

        Ok(Expression {
            kind: ExprKind::PredicateLoop { label, cond, body },
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses iterator loop expression
    pub fn parse_iterator_loop_expr(&mut self) -> IResult<Expression> {
        let label = self.parse_label_in_expr()?;

        // TEST: n/a
        let lo_for = self.expect(ExpToken::KwFor)?;
        let lo = label.as_ref().map(|l| l.loc.clone()).unwrap_or(lo_for);

        // TEST: no. 1
        self.expect(ExpToken::Ident).emit(self.x());
        let variable = self.as_ident();

        // TEST: no. 2
        self.expect(ExpToken::KwIn).emit(self.x());

        let iterator = Box::new(
            self.parse_expr_reset()
                .emit_wval(self.x(), Expression::dummy),
        );

        let body = self
            .with_rest(Restrictions::empty(), Parser::parse_block)
            .emit_wval(self.x(), Block::dummy);

        let hi = body.loc.clone();

        let loc = Span::from_ends(lo, hi);

        Ok(Expression {
            kind: ExprKind::IteratorLoop {
                label,
                variable,
                iterator,
                body,
                loc: loc.clone(),
            },
            loc,
        })
    }

    /// Parses infinite loop expression
    pub fn parse_infinite_loop_expr(&mut self) -> IResult<Expression> {
        let label = self.parse_label_in_expr()?;

        // TEST: n/a
        let lo_loop = self.expect(ExpToken::KwLoop)?;
        let lo = label.as_ref().map(|l| l.loc.clone()).unwrap_or(lo_loop);

        let block = self
            .with_rest(Restrictions::empty(), Parser::parse_block)
            .emit_wval(self.x(), Block::dummy);

        let hi = block.loc.clone();

        Ok(Expression {
            kind: ExprKind::InfiniteLoop { label, body: block },
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses return expression
    pub fn parse_return_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let lo = self.expect(ExpToken::KwReturn)?;
        let mut hi = lo.clone();

        let val = if self.token.is_stmt_end() {
            None
        } else {
            let expr = Box::new(self.parse_expr().emit_wval(self.x(), Expression::dummy));
            hi = expr.loc.clone();

            Some(expr)
        };

        Ok(Expression {
            kind: ExprKind::Return { expr: val },
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses break expression
    pub fn parse_break_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let lo = self.expect(ExpToken::KwBreak)?;

        let mut hi = lo.clone();

        let label = if self.eat_no_expect(ExpToken::Colon) {
            // TEST: no. 1
            hi = self
                .expect(ExpToken::Ident)
                .emit_wval(self.x(), || Span::ZERO);
            let label = self.as_ident();

            Some(label)
        } else {
            None
        };

        let expr = if self.token.is_stmt_end() {
            None
        } else {
            let expr = Box::new(self.parse_expr().emit_wval(self.x(), Expression::dummy));
            hi = expr.loc.clone();

            Some(expr)
        };

        Ok(Expression {
            kind: ExprKind::Break { label, expr },
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses continue expression
    pub fn parse_continue_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let lo = self.expect(ExpToken::KwContinue)?;
        let mut hi = lo.clone();

        let label = if self.eat_no_expect(ExpToken::Colon) {
            // TEST: no. 1
            hi = self
                .expect(ExpToken::Ident)
                .emit_wval(self.x(), || Span::ZERO);
            let label = self.as_ident();

            Some(label)
        } else {
            None
        };

        Ok(Expression {
            kind: ExprKind::Continue { label },
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses null expression
    pub fn parse_null_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let loc = self.expect(ExpToken::KwNull)?;

        Ok(Expression {
            kind: ExprKind::Null,
            loc,
        })
    }

    /// Parses orb expression
    pub fn parse_orb_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let loc = self.expect(ExpToken::KwOrb)?;

        Ok(Expression {
            kind: ExprKind::Orb,
            loc,
        })
    }

    /// Parses function pointer type
    pub fn parse_funptr_typeexpr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let lo = self.expect(ExpToken::Star)?;

        // TEST: n/a
        self.expect(ExpToken::KwFun)?;

        // TEST: no. 1
        self.expect_nae(ExpToken::LParen).emit(self.x());

        let mut args = Vec::new();

        loop {
            if self.eat_no_expect(ExpToken::RParen) {
                break;
            }

            match self.parse_typeexpr() {
                Ok(t) => {
                    args.push(t);
                }
                Err(recovered) => {
                    if let Recovered::Unable(d) = recovered {
                        self.sink.emit(d);
                    }

                    // recover parsing to a Comma, RParen or Eof.
                    self.recover_expr_in_paren_seq();
                }
            }

            // TEST: no. 2
            if self.eat(ExpToken::Comma) {
                // nothing it was expected..
            } else if self.eat(ExpToken::RParen) {
                // finished to parse the call expr
                break;
            } else {
                return self.etd_and_bump();
            }
        }

        // TEST: n/a
        let hi_paren = self.token_loc();

        let (hi, ret) = if self.eat_no_expect(ExpToken::MinusGt) {
            match self.parse_typeexpr() {
                Ok(t) => {
                    let typeexpr = Box::new(t);

                    (typeexpr.loc.clone(), Some(typeexpr))
                }
                Err(recovered) => {
                    if let Recovered::Unable(d) = recovered {
                        self.sink.emit(d);
                    }

                    (hi_paren, None)
                }
            }
        } else {
            (hi_paren, None)
        };

        Ok(Expression {
            kind: ExprKind::FunPtrType { args, ret },
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses pointer type expression
    pub fn parse_pointer_typeexpr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let lo = self.expect(ExpToken::Star)?;

        let mutability = self.parse_mutability();

        let typeexpr = Box::new(self.parse_typeexpr().emit_wval(self.x(), Expression::dummy));
        let hi = typeexpr.loc.clone();

        Ok(Expression {
            kind: ExprKind::PointerType(mutability, typeexpr),
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses unary right expression
    pub fn parse_unary_right_expr(&mut self, lhs: Expression) -> IResult<Expression> {
        let lo = lhs.loc.clone();

        let (op, hi) = if let Some(op) = UnOp::right_from_token(&self.token.tt) {
            self.bump();

            (op, self.token_loc())
        } else {
            return Err(ExpectedToken::new(["unary operator"], self.token.clone()).into());
        };

        Ok(Expression {
            kind: ExprKind::Unary {
                op,
                expr: Box::new(lhs),
            },
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses borrow expression
    pub fn parse_borrow_expr(&mut self) -> IResult<Expression> {
        // TEST: n/a
        let lo = self.expect(ExpToken::And)?;

        let mutability = self.parse_mutability();

        let val = Box::new(self.parse_expr().emit_wval(self.x(), Expression::dummy));

        let hi = val.loc.clone();

        Ok(Expression {
            kind: ExprKind::Borrow(mutability, val),
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses field expression
    pub fn parse_field_expr(&mut self, expr: Expression) -> IResult<Expression> {
        // TEST: n/a
        self.expect(ExpToken::Dot)?;

        // TEST: no. 1
        self.expect(ExpToken::Ident).emit(self.x());
        let hi = self.token_loc();
        let member = self.as_ident();

        let loc = Span::from_ends(expr.loc.clone(), hi);

        Ok(Expression {
            kind: ExprKind::Field {
                expr: Box::new(expr),
                member,
            },
            loc,
        })
    }
}
