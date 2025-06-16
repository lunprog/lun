//! Parsing of lun's expressions.

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
    pub expr: Expr,
    pub loc: Span,
}

impl AstNode for Expression {
    #[inline]
    #[track_caller]
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        parse_expr_precedence(parser, HIGHEST_PRECEDENCE)
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    /// integer literal expression
    ///
    /// integer
    IntLit(u64),
    /// boolean literal expression
    ///
    /// ("true" | "false")
    BoolLit(bool),
    /// string literal expression
    ///
    /// string
    StringLit(String),
    /// grouping expression (just parenthesis)
    ///
    /// "(" expr ")"
    Grouping(Box<Expression>),
    /// an identifier expression
    ///
    /// ident
    Ident(String),
    /// binary operation
    ///
    /// expr op expr
    Binary {
        lhs: Box<Expression>,
        op: BinOp,
        rhs: Box<Expression>,
    },
    /// unary operation
    ///
    /// op expr
    Unary { op: UnaryOp, expr: Box<Expression> },
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
    /// function call expression
    ///
    /// expr "(" ( expr ),* ")"
    FunCall {
        // TODO: rename this field something that looks like `function operand`
        // do the same for CkExpr::FunCall and (Ck)Stmt::FunCall
        called: Box<Expression>,
        args: Vec<Expression>,
    },
    /// function definition
    ///
    /// "fun" "(" ( ident ":" expr ),* ")" [ "->" expr ] block
    FunDefinition {
        args: Vec<Arg>,
        rettype: Option<Box<Expression>>,
        body: Block,
    },
}

#[derive(Debug, Clone)]
pub struct Arg {
    pub name: String,
    pub name_loc: Span,
    pub typ: Expression,
    pub loc: Span,
}

/// Parses an expression given the following precedence.
pub fn parse_expr_precedence(
    parser: &mut Parser,
    precedence: Precedence,
) -> Result<Expression, Diagnostic> {
    // TODO: parsing of range expressions, `expr..expr` and `expr..=expr`, and
    // maybe `..expr` and maybe `expr..` but not sure because the integer type
    // can go from -u64::MAX to i64::MAX
    let mut lhs = match parser.peek_tt() {
        Some(IntLit(_)) => parse!(@fn parser => parse_intlit_expr),
        Some(Kw(Keyword::True | Keyword::False)) => parse!(@fn parser => parse_boollit_expr),
        // Some(Char(_)) => parse!(@fn parser => parse_charlit_expr),
        Some(StringLit(_)) => parse!(@fn parser => parse_strlit_expr),
        Some(Punct(Punctuation::LParen)) => parse!(@fn parser => parse_grouping_expr),
        Some(Ident(_)) => parse!(@fn parser => parse_ident_expr),
        Some(Kw(Keyword::Fun)) => parse!(@fn parser => parse_fundef_expr),
        Some(tt) if UnaryOp::from_tt(tt.clone()).is_some() => {
            parse!(@fn parser => parse_unary_expr)
        }
        Some(_) => {
            // unwrap is safe because we already know the next has a token type
            let t = parser.peek_tok().unwrap().clone();
            // TODO: make the parser retry if he failed to parse lhs with a
            // loop, see parsing of statements also.
            return Err(ExpectedToken::new(
                [
                    IntLit(0),
                    Kw(Keyword::False),
                    Kw(Keyword::True),
                    StringLit(String::new()),
                    Punct(Punctuation::LParen),
                    Ident(String::new()),
                    Kw(Keyword::Not),
                    Punct(Punctuation::Minus),
                ],
                t.tt,
                Some("expression"),
                t.loc,
            )
            .into_diag());
        }
        None => {
            return Err(parser.eof_diag());
        }
    };

    loop {
        let Some(tt) = parser.peek_tt().cloned() else {
            break;
        };

        let Some(pr) = Precedence::from(tt) else {
            // the next token isn't a binary operator
            break;
        };

        if precedence > pr {
            break;
        }

        // we match a token here, because, in the future there will be
        // binary operators that are Keyword, like Logical And.
        lhs = match parser.peek_tt() {
            Some(Punct(Punctuation::LParen)) => {
                parse!(@fn parser => parse_funcall_expr, Box::new(lhs))
            }
            Some(maybe_bin_op) if BinOp::from_tt(maybe_bin_op.clone()).is_some() => {
                parse!(@fn parser => parse_binary_expr, lhs)
            }
            _ => break,
        }
    }

    Ok(lhs)
}

/// Parse an integer literal expression
pub fn parse_intlit_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (i, loc) = expect_token!(parser => [IntLit(i), *i], "integer literal");

    Ok(Expression {
        expr: Expr::IntLit(i),
        loc,
    })
}

/// Parse a boolean literal expression
pub fn parse_boollit_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (b, loc) = expect_token!(parser => [Kw(Keyword::True), true; Kw(Keyword::False), false], "bool literal");

    Ok(Expression {
        expr: Expr::BoolLit(b),
        loc,
    })
}

/// Parse a string literal expression
pub fn parse_strlit_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (str, loc) = expect_token!(parser => [StringLit(s), s.clone()], "integer literal");

    Ok(Expression {
        expr: Expr::StringLit(str),
        loc,
    })
}

/// Parse a grouping expression
pub fn parse_grouping_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let ((), lo) = expect_token!(parser => [Punct(Punctuation::LParen), ()], [Punctuation::LParen]);
    let expr = parse!(box: parser => Expression);
    let ((), hi) = expect_token!(parser => [Punct(Punctuation::RParen), ()], [Punctuation::RParen]);

    Ok(Expression {
        expr: Expr::Grouping(expr),
        loc: Span::from_ends(lo, hi),
    })
}

/// Parse an identifier expression
pub fn parse_ident_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (id, loc) = expect_token!(parser => [Ident(s), s.clone()], "integer literal");

    Ok(Expression {
        expr: Expr::Ident(id),
        loc,
    })
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
    /// `=`
    Assignement,
    /// `or`
    Or,
    /// `and`
    And,
    /// `==  !=`
    Equality,
    /// `<  >  <=  >= `
    Comparison,
    /// `+ -`
    Term,
    /// `* /`
    Factor,
    /// `op expression`
    Unary,
    /// `expression ( expression,* )`
    Call,
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
            Self::__First__ => Self::Assignement,
            Self::Assignement => Self::Or,
            Self::Or => Self::And,
            Self::And => Self::Equality,
            Self::Equality => Self::Comparison,
            Self::Comparison => Self::Term,
            Self::Term => Self::Factor,
            Self::Factor => Self::Unary,
            Self::Unary => Self::Call,
            Self::Call => Self::Primary,
            Self::Primary => Self::__Last__,
            Self::__Last__ => unreachable!(),
        }
    }

    pub fn associativity(&self) -> Associativity {
        match self {
            Self::Assignement => Associativity::RightToLeft,
            Self::Or => Associativity::LeftToRight,
            Self::And => Associativity::LeftToRight,
            Self::Equality => Associativity::LeftToRight,
            Self::Comparison => Associativity::LeftToRight,
            Self::Term => Associativity::LeftToRight,
            Self::Factor => Associativity::LeftToRight,
            Self::Unary => Associativity::RightToLeft,
            Self::Call => Associativity::LeftToRight,
            Self::Primary => Associativity::LeftToRight,
            Self::__Last__ | Self::__First__ => unreachable!(),
        }
    }
}

impl Precedence {
    fn from(value: TokenType) -> Option<Precedence> {
        use TokenType::Punct;
        match value {
            Punct(Punctuation::Equal) => Some(Precedence::Assignement),
            Punct(Punctuation::Equal2 | Punctuation::BangEqual) => Some(Precedence::Equality),
            Punct(
                Punctuation::LArrow
                | Punctuation::RArrow
                | Punctuation::LArrowEqual
                | Punctuation::RArrowEqual,
            ) => Some(Precedence::Comparison),
            Punct(Punctuation::Plus | Punctuation::Minus) => Some(Precedence::Term),
            Punct(Punctuation::Star | Punctuation::Slash) => Some(Precedence::Factor),
            Punct(Punctuation::LParen) => Some(Precedence::Call),
            _ => None,
        }
    }
}

/// The higest precedence of [`Precedence`]
pub const HIGHEST_PRECEDENCE: Precedence = Precedence::Assignement;

#[derive(Debug, Clone)]
pub enum BinOp {
    /// addition
    Add,
    /// substraction
    Sub,
    /// multiplication
    Mul,
    /// division
    Div,
    /// less than
    CompLT,
    /// less than or equal
    CompLE,
    /// greater than
    CompGT,
    /// greater than or equal
    CompGE,
    /// equal
    CompEq,
    /// not equal
    CompNe,
    /// assignement
    Assignement,
}

impl BinOp {
    pub fn from_punct(punct: Punctuation) -> Option<BinOp> {
        use BinOp as BOp;
        use Punctuation as Punct;
        Some(match punct {
            Punct::Equal => BOp::Assignement,
            Punct::Star => BOp::Mul,
            Punct::Slash => BOp::Div,
            Punct::Plus => BOp::Add,
            Punct::Minus => BOp::Sub,
            Punct::LArrow => BOp::CompLT,
            Punct::RArrow => BOp::CompGT,
            Punct::LArrowEqual => BOp::CompLE,
            Punct::RArrowEqual => BOp::CompGE,
            Punct::Equal2 => BOp::CompEq,
            Punct::BangEqual => BOp::CompNe,
            _ => return None,
        })
    }

    pub fn from_tt(tt: TokenType) -> Option<BinOp> {
        match tt {
            Punct(p) => Self::from_punct(p),
            _ => None,
        }
    }

    /// Is the binary operation rational? < <= > >= == !=
    pub fn is_relational(&self) -> bool {
        matches!(
            self,
            BinOp::CompLT
                | BinOp::CompLE
                | BinOp::CompGT
                | BinOp::CompGE
                | BinOp::CompEq
                | BinOp::CompNe
        )
    }

    pub fn is_logical(&self) -> bool {
        // TODO: implement logical operators like `"not" expr`, `expr "and"
        // expr`, `expr "or" expr`, `expr "xor" expr`
        false
    }
}

/// Parse binary expression, `expression op expression`
pub fn parse_binary_expr(parser: &mut Parser, lhs: Expression) -> Result<Expression, Diagnostic> {
    let (op, tok) = match parser.peek_tok() {
        // TODO: here we compute twice the binary op its a little dumb, find a solution to that problem.
        Some(Token { tt: op, .. }) if BinOp::from_tt(op.clone()).is_some() => {
            let op = op.clone();
            parser.pop();
            (BinOp::from_tt(op.clone()).unwrap(), op)
        }
        Some(tok) => {
            let t = tok.clone();
            return Err(
                ExpectedToken::new("binary operator", t.tt, Some("expression"), t.loc).into_diag(),
            );
        }
        None => return Err(parser.eof_diag()),
    };

    let Some(mut pr) = Precedence::from(tok.clone()) else {
        // we can't reach here because we already checked that our token is a
        // binary operator like those we want in this function
        unreachable!()
    };

    if pr.associativity() == Associativity::LeftToRight {
        pr = pr.next();
    }

    let rhs = parse!(@fn parser => parse_expr_precedence, pr);
    let loc = Span::from_ends(lhs.loc.clone(), rhs.loc.clone());

    Ok(Expression {
        expr: Expr::Binary {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        },
        loc,
    })
}

/// Unary Operators
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    // LEFT UNARY OPERATOR
    /// `"-" expression`
    Negation,
    /// `not expression`
    Not,
}

impl UnaryOp {
    pub fn from_tt(tt: TokenType) -> Option<UnaryOp> {
        match tt {
            Punct(Punctuation::Minus) => Some(UnaryOp::Negation),
            Kw(Keyword::Not) => Some(UnaryOp::Not),
            _ => None,
        }
    }
}

/// Parse unary expression, `op expression`
pub fn parse_unary_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (op, lo) = expect_token!(parser => [
        Punct(Punctuation::Minus), UnaryOp::Negation;
        Kw(Keyword::Not), UnaryOp::Not;
    ], "minus operator or keyword not");

    let expr = parse!(box: @fn parser => parse_expr_precedence, Precedence::Unary);

    Ok(Expression {
        loc: Span::from_ends(lo, expr.loc.clone()),
        expr: Expr::Unary { op, expr },
    })
}

/// parses the call expression
pub fn parse_funcall_expr(
    parser: &mut Parser,
    called: Box<Expression>,
) -> Result<Expression, Diagnostic> {
    let lo = called.loc.clone();
    expect_token!(parser => [Punct(Punctuation::LParen), ()], Punctuation::LParen);

    let mut args = Vec::new();

    loop {
        if let Some(Punct(Punctuation::RParen)) = parser.peek_tt() {
            break;
        }

        args.push(parse!(parser => Expression));

        expect_token!(parser => [Punct(Punctuation::Comma), (); Punct(Punctuation::RParen), (), in break], [Punctuation::Colon, Punctuation::LParen]);
    }

    let ((), hi) = expect_token!(parser => [Punct(Punctuation::RParen), ()], Punctuation::RParen);

    Ok(Expression {
        expr: Expr::FunCall { called, args },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses the function definition expression
pub fn parse_fundef_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Fun), ()], Kw(Keyword::Fun));

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
        Some(parse!(box: parser => Expression))
    } else {
        None
    };

    let body = parse!(parser => Block);
    let hi = body.loc.clone();

    Ok(Expression {
        expr: Expr::FunDefinition {
            args,
            rettype,
            body,
        },
        loc: Span::from_ends(lo, hi),
    })
}
