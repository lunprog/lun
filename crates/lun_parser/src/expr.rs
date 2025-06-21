//! Parsing of lun's expressions.

use std::fmt::Display;

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

impl Expression {
    /// Is the expression `ExpressionWithBlock`?
    pub fn is_expr_with_block(&self) -> bool {
        matches!(
            self.expr,
            Expr::If(_) | Expr::Block(_) | Expr::While { .. } | Expr::For { .. }
        )
    }
}

/// parses a type expression with a precedence of Or
///
/// a "type expression" is just an expression that resolves to the atomic type
/// `comptime type`
pub fn parse_type_expression(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    parse_expr_precedence(parser, Precedence::LogicalOr)
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
    /// function definition expression
    ///
    /// "fun" "(" ( ident ":" expr ),* ")" [ "->" expr ] block
    FunDefinition {
        args: Vec<Arg>,
        rettype: Option<Box<Expression>>,
        body: Block,
    },
    /// if else expression
    ///
    /// "if" expression block [ "else" (if-expr | block-expr) ]
    If(IfExpression),
    /// if then else expression
    ///
    /// "if" expression "then" expression "else" expression
    IfThenElse {
        cond: Box<Expression>,
        true_val: Box<Expression>,
        false_val: Box<Expression>,
    },
    /// block expression
    // TODO: make the grammar for block expr
    Block(Block),
    /// while expression
    ///
    /// "while" expression block
    While { cond: Box<Expression>, body: Block },
    /// for expression
    ///
    /// "for" ident "in" expression block
    For {
        /// the variable that holds the value of the iterator
        variable: String,
        iterator: Box<Expression>,
        body: Block,
    },
    /// return expression
    ///
    /// "return" expression?
    Return { val: Option<Box<Expression>> },
    /// break expression
    ///
    /// "break" expression?
    Break { val: Option<Box<Expression>> },
    /// continue expression
    ///
    /// "continue"
    Continue,
    /// null expression
    ///
    /// "null"
    Null,
    /// pointer type expression
    ///
    /// "*" "mut"? expression
    PointerType { mutable: bool, typ: Box<Expression> },
}

#[derive(Debug, Clone)]
pub struct IfExpression {
    pub cond: Box<Expression>,
    pub body: Box<Block>,
    pub else_branch: Option<Box<Else>>,
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
    pub typ: Expression,
    pub loc: Span,
}

/// Parses an expression given the following precedence.
pub fn parse_expr_precedence(
    parser: &mut Parser,
    precedence: Precedence,
) -> Result<Expression, Diagnostic> {
    // TODO: parsing of range expressions, `expr..<expr` and `expr..=expr`, and
    // maybe `..<expr`, `..=expr` and maybe `expr..`
    let mut lhs = match parser.peek_tt() {
        Some(IntLit(_)) => parse!(@fn parser => parse_intlit_expr),
        Some(Kw(Keyword::True | Keyword::False)) => parse!(@fn parser => parse_boollit_expr),
        // Some(Char(_)) => parse!(@fn parser => parse_charlit_expr),
        Some(StringLit(_)) => parse!(@fn parser => parse_strlit_expr),
        Some(Punct(Punctuation::LParen)) => parse!(@fn parser => parse_grouping_expr),
        Some(Ident(_)) => parse!(@fn parser => parse_ident_expr),
        Some(Kw(Keyword::Fun)) => parse!(@fn parser => parse_fundef_expr),
        Some(Kw(Keyword::If)) => parse!(@fn parser => parse_if_else_expr, false),
        Some(Kw(Keyword::While)) => parse!(@fn parser => parse_while_expr),
        Some(Kw(Keyword::For)) => parse!(@fn parser => parse_for_expr),
        Some(Kw(Keyword::Return)) => parse!(@fn parser => parse_return_expr),
        Some(Kw(Keyword::Break)) => parse!(@fn parser => parse_break_expr),
        Some(Kw(Keyword::Continue)) => parse!(@fn parser => parse_continue_expr),
        Some(Kw(Keyword::Null)) => parse!(@fn parser => parse_null_expr),
        Some(Punct(Punctuation::LBrace)) => parse!(@fn parser => parse_block_expr),
        Some(Punct(Punctuation::Star)) => parse!(@fn parser => parse_pointer_type_expr),
        Some(tt) if UnaryOp::left_from_token(tt.clone()).is_some() => {
            parse!(@fn parser => parse_unary_left_expr)
        }
        Some(_) => {
            // unwrap is safe because we already know the next has a token type
            let t = parser.peek_tok().unwrap().clone();
            // TODO: make the parser retry if he failed to parse lhs with a
            // loop, see parsing of statements also.
            return Err(ExpectedToken::new("expression", t.tt, None::<String>, t.loc).into_diag());
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
            // the next token isn't part of a post expression
            break;
        };

        if precedence > pr {
            break;
        }

        lhs = match parser.peek_tt() {
            Some(Punct(Punctuation::LParen)) => {
                parse!(@fn parser => parse_funcall_expr, Box::new(lhs))
            }
            Some(maybe_bin_op) if BinOp::from_tt(maybe_bin_op.clone()).is_some() => {
                parse!(@fn parser => parse_binary_expr, lhs)
            }
            Some(maybe_right_op) if UnaryOp::right_from_token(maybe_right_op.clone()).is_some() => {
                parse!(@fn parser => parse_unary_right_expr, lhs)
            }
            _ => break,
        };
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
    /// `a = b`
    Assignement,
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
    /// both call and unary right precende:
    ///
    /// `expression "(" expression,* ")"`
    ///
    /// or
    ///
    /// `expression op`
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
            Self::Assignement => Self::LogicalOr,
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
            Self::Call => Self::Primary,
            Self::Primary => Self::__Last__,
            Self::__Last__ => unreachable!(),
        }
    }

    pub fn associativity(&self) -> Associativity {
        match self {
            Self::Assignement => Associativity::RightToLeft,
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
            Kw(Keyword::Or) => Some(Precedence::LogicalOr),
            Kw(Keyword::And) => Some(Precedence::LogicalAnd),
            Punct(
                Punctuation::Lt | Punctuation::Gt | Punctuation::LtEqual | Punctuation::GtEqual,
            ) => Some(Precedence::Comparison),
            Punct(Punctuation::Equal2 | Punctuation::BangEqual) => Some(Precedence::Equality),
            Punct(Punctuation::Pipe) => Some(Precedence::BitwiseOr),
            Punct(Punctuation::Carret) => Some(Precedence::BitwiseXor),
            Punct(Punctuation::Ampsand) => Some(Precedence::BitwiseAnd),
            Punct(Punctuation::Lt2 | Punctuation::Gt2) => Some(Precedence::Shift),
            Punct(Punctuation::Plus | Punctuation::Minus) => Some(Precedence::Term),
            Punct(Punctuation::Star | Punctuation::Slash | Punctuation::Percent) => {
                Some(Precedence::Factor)
            }
            Punct(Punctuation::LParen) => Some(Precedence::Call),
            Punct(Punctuation::DotStar) => Some(Precedence::Primary),
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
    /// remainder
    Rem,
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
    /// and
    LogicalAnd,
    /// or
    LogicalOr,
    /// &
    BitwiseAnd,
    /// ^
    BitwiseXor,
    /// |
    BitwiseOr,
    /// shift right, >>
    Shr,
    /// shift left, <<
    Shl,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Rem => "%",
            Self::CompLT => "<",
            Self::CompLE => "<=",
            Self::CompGT => ">",
            Self::CompGE => ">=",
            Self::CompEq => "==",
            Self::CompNe => "!=",
            Self::Assignement => "=",
            Self::LogicalAnd => "and",
            Self::LogicalOr => "or",
            Self::BitwiseAnd => "&",
            Self::BitwiseXor => "^",
            Self::BitwiseOr => "|",
            Self::Shr => ">>",
            Self::Shl => "<<",
        };

        f.write_str(str)
    }
}

impl BinOp {
    pub fn from_punct(punct: Punctuation) -> Option<BinOp> {
        use BinOp as BOp;
        use Punctuation as Punct;

        Some(match punct {
            Punct::Equal => BOp::Assignement,
            Punct::Star => BOp::Mul,
            Punct::Slash => BOp::Div,
            Punct::Percent => BOp::Rem,
            Punct::Plus => BOp::Add,
            Punct::Minus => BOp::Sub,
            Punct::Lt => BOp::CompLT,
            Punct::Gt => BOp::CompGT,
            Punct::LtEqual => BOp::CompLE,
            Punct::GtEqual => BOp::CompGE,
            Punct::Equal2 => BOp::CompEq,
            Punct::BangEqual => BOp::CompNe,
            Punct::Ampsand => BOp::BitwiseAnd,
            Punct::Carret => BOp::BitwiseXor,
            Punct::Pipe => BOp::BitwiseOr,
            Punct::Lt2 => BOp::Shl,
            Punct::Gt2 => BOp::Shr,
            _ => return None,
        })
    }

    pub fn from_tt(tt: TokenType) -> Option<BinOp> {
        match tt {
            Punct(p) => Self::from_punct(p),
            Kw(Keyword::And) => Some(BinOp::LogicalAnd),
            Kw(Keyword::Or) => Some(BinOp::LogicalOr),
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
        matches!(self, Self::LogicalAnd | Self::LogicalOr)
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
    // left unary operator
    /// `- expression`
    Negation,
    /// `! expression`
    Not,
    /// `& expression`
    AddressOf,
    // right unary operator
    /// `expression.*`
    Dereference,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Self::Negation => "-",
            Self::Not => "!",
            Self::AddressOf => "&",
            Self::Dereference => ".*",
        };

        f.write_str(str)
    }
}

impl UnaryOp {
    /// get the unary operation for left side unary operation
    ///
    /// eg:
    /// `-a` `!a` `&a`
    pub fn left_from_token(tt: TokenType) -> Option<UnaryOp> {
        match tt {
            Punct(Punctuation::Minus) => Some(UnaryOp::Negation),
            Punct(Punctuation::Bang) => Some(UnaryOp::Not),
            Punct(Punctuation::Ampsand) => Some(UnaryOp::AddressOf),
            _ => None,
        }
    }

    /// get the unary operation for right side unary operation
    ///
    /// eg:
    /// `a.*`
    pub fn right_from_token(tt: TokenType) -> Option<UnaryOp> {
        match tt {
            Punct(Punctuation::DotStar) => Some(UnaryOp::Dereference),
            _ => None,
        }
    }
}

/// Parse unary expression, `op expression`
pub fn parse_unary_left_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (op, lo) = if let Some(Token { tt, loc }) = parser.peek_tok() {
        if let Some(op) = UnaryOp::left_from_token(tt.clone()) {
            let loc = loc.clone();
            parser.pop();
            (op, loc)
        } else {
            let t = parser.peek_tok().unwrap().clone();
            return Err(
                ExpectedToken::new("unary operator", t.tt, Some("expression"), t.loc).into_diag(),
            );
        }
    } else {
        return Err(parser.eof_diag());
    };

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

        let typ = parse!(@fn parser => parse_type_expression);

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
        Some(parse!(box: @fn parser => parse_type_expression))
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

/// parses the if-else expression
pub fn parse_if_else_expr(parser: &mut Parser, only_block: bool) -> Result<Expression, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::If), ()], Kw(Keyword::If));

    let cond = parse!(box: parser => Expression);

    if let Some(TokenType::Punct(Punctuation::LBrace)) = parser.peek_tt() {
        // if expr
        // "if" expression block [ "else" (if-expr | block-expr) ]
        let body = parse!(box: parser => Block);

        let mut hi = body.loc.clone();

        let else_branch = if let Some(Kw(Keyword::Else)) = parser.peek_tt() {
            parser.pop();

            let else_branch = match parser.peek_tt() {
                Some(Kw(Keyword::If)) => {
                    let Expression {
                        expr: Expr::If(if_expr),
                        loc: _,
                    } = parse!(@fn parser => parse_if_else_expr, true)
                    else {
                        unreachable!();
                    };
                    hi = if_expr.loc.clone();

                    Else::IfExpr(if_expr)
                }
                Some(Punct(Punctuation::LBrace)) => {
                    // block
                    let block = parse!(parser => Block);

                    hi = block.loc.clone();

                    Else::Block(block)
                }
                Some(_) => {
                    let t = parser.peek_tok().unwrap();

                    return Err(ExpectedToken::new(
                        [Punct(Punctuation::LBrace), Kw(Keyword::If)],
                        t.tt.clone(),
                        Some("if expression"),
                        t.loc.clone(),
                    )
                    .into_diag());
                }
                None => return Err(parser.eof_diag()),
            };

            Some(Box::new(else_branch))
        } else {
            None
        };

        let loc = Span::from_ends(lo, hi);

        Ok(Expression {
            expr: Expr::If(IfExpression {
                cond,
                body,
                else_branch,
                loc: loc.clone(),
            }),
            loc,
        })
    } else if !only_block {
        // if then else expr
        // "if" expression then expression "else" expression

        expect_token!(parser => [Kw(Keyword::Then), ()], Kw(Keyword::Then));
        let true_val = parse!(box: parser => Expression);
        expect_token!(parser => [Kw(Keyword::Else), ()], Kw(Keyword::Else));
        let false_val = parse!(box: parser => Expression);

        let hi = false_val.loc.clone();

        Ok(Expression {
            expr: Expr::IfThenElse {
                cond,
                true_val,
                false_val,
            },
            loc: Span::from_ends(lo, hi),
        })
    } else {
        let t = parser.peek_tok().unwrap();

        Err(ExpectedToken::new(
            [Punct(Punctuation::LBrace)],
            t.tt.clone(),
            Some("if expression"),
            t.loc.clone(),
        )
        .into_diag())
    }
}

/// parses block expression
pub fn parse_block_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let block = parse!(parser => Block);
    let loc = block.loc.clone();

    Ok(Expression {
        expr: Expr::Block(block),
        loc,
    })
}

/// parses while expression
pub fn parse_while_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::While), ()], Kw(Keyword::While));

    let cond = parse!(box: parser => Expression);
    let body = parse!(parser => Block);

    let hi = body.loc.clone();

    Ok(Expression {
        expr: Expr::While { cond, body },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses for expression
pub fn parse_for_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::For), ()], Kw(Keyword::For));

    let (variable, _) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    expect_token!(parser => [Kw(Keyword::In), ()], Kw(Keyword::In));

    let iterator = parse!(box: parser => Expression);

    let body = parse!(parser => Block);

    let hi = body.loc.clone();

    Ok(Expression {
        expr: Expr::For {
            variable,
            iterator,
            body,
        },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses return expression
pub fn parse_return_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Return), ()], Kw(Keyword::Return));
    let mut hi = lo.clone();

    let val = if parser.is_stmt_end() {
        None
    } else {
        let expr = parse!(box: parser => Expression);
        hi = expr.loc.clone();

        Some(expr)
    };

    Ok(Expression {
        expr: Expr::Return { val },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses break expression
pub fn parse_break_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Break), ()], Kw(Keyword::Break));
    let mut hi = lo.clone();

    let val = if parser.is_stmt_end() {
        None
    } else {
        let expr = parse!(box: parser => Expression);
        hi = expr.loc.clone();

        Some(expr)
    };

    Ok(Expression {
        expr: Expr::Break { val },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses continue expression
pub fn parse_continue_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (_, loc) = expect_token!(parser => [Kw(Keyword::Continue), ()], Kw(Keyword::Continue));

    Ok(Expression {
        expr: Expr::Continue,
        loc,
    })
}

/// parses null expression
pub fn parse_null_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (_, loc) = expect_token!(parser => [Kw(Keyword::Null), ()], Kw(Keyword::Null));

    Ok(Expression {
        expr: Expr::Null,
        loc,
    })
}

/// parses pointer type expression
pub fn parse_pointer_type_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (_, lo) = expect_token!(parser => [Punct(Punctuation::Star), ()], Punctuation::Star);

    let mutable = if let Some(Kw(Keyword::Mut)) = parser.peek_tt() {
        parser.pop();
        true
    } else {
        false
    };

    let typ = parse!(box: @fn parser => parse_type_expression);
    let hi = typ.loc.clone();

    Ok(Expression {
        expr: Expr::PointerType { mutable, typ },
        loc: Span::from_ends(lo, hi),
    })
}

pub fn parse_unary_right_expr(
    parser: &mut Parser,
    lhs: Expression,
) -> Result<Expression, Diagnostic> {
    let lo = lhs.loc.clone();

    let (op, hi) = if let Some(Token { tt, loc }) = parser.peek_tok() {
        if let Some(op) = UnaryOp::right_from_token(tt.clone()) {
            let loc = loc.clone();
            parser.pop();
            (op, loc)
        } else {
            let t = parser.peek_tok().unwrap().clone();
            return Err(
                ExpectedToken::new("unary operator", t.tt, Some("expression"), t.loc).into_diag(),
            );
        }
    } else {
        return Err(parser.eof_diag());
    };

    Ok(Expression {
        expr: Expr::Unary {
            op,
            expr: Box::new(lhs),
        },
        loc: Span::from_ends(lo, hi),
    })
}
