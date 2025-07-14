//! Parsing of lun's definitions.

use crate::expr::parse_type_expression;

use super::*;

/// Visibility
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum Vis {
    #[default]
    Private,
    Public,
}

/// Lun program.
#[derive(Debug, Clone)]
pub struct Program {
    pub defs: Vec<Item>,
}

impl AstNode for Program {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let mut defs = Vec::new();

        loop {
            if let None | Some(TokenType::EOF) = parser.peek_tt() {
                break;
            }

            defs.push(parse!(parser => Item));
        }

        Ok(Program { defs })
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    /// Global constant.
    ///
    /// ident ":" expression? ":" exprWithBlock
    /// ident ":" expression? ":" exprWithoutBlock ";"
    GlobalConst {
        name: String,
        name_loc: Span,
        typ: Option<Expression>,
        value: Expression,
        loc: Span,
    },
    /// Global variable.
    ///
    /// ident ":" expression? "=" expr ";"
    GlobalVar {
        name: String,
        name_loc: Span,
        typ: Option<Expression>,
        value: Expression,
        loc: Span,
    },
}

impl AstNode for Item {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let (name, lo) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punctuation::Colon);

        let typ = match parser.peek_tt() {
            Some(Punct(Punctuation::Colon | Punctuation::Equal)) => None,
            _ => Some(parse!(@fn parser => parse_type_expression)),
        };

        let (is_const, _) = expect_token!(
            parser => [
                Punct(Punctuation::Colon), true;
                Punct(Punctuation::Equal), false;
            ],
            [Punctuation::Colon, Punctuation::Equal]
        );

        let value = parse!(parser => Expression);

        let hi = if !value.is_expr_with_block() || !is_const {
            expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punctuation::Semicolon).1
        } else {
            value.loc.clone()
        };

        let loc = Span::from_ends(lo.clone(), hi);

        if is_const {
            Ok(Item::GlobalConst {
                name,
                name_loc: lo,
                typ,
                value,
                loc,
            })
        } else {
            Ok(Item::GlobalVar {
                name,
                name_loc: lo,
                typ,
                value,
                loc,
            })
        }
    }
}
