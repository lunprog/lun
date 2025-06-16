//! Parsing of lun's definitions.

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
    pub defs: Vec<Definition>,
}

impl AstNode for Program {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let mut defs = Vec::new();

        loop {
            if let None | Some(TokenType::EOF) = parser.peek_tt() {
                break;
            }

            defs.push(parse!(parser => Definition));
        }

        Ok(Program { defs })
    }
}

/// Lun program.
///
///    vis ident ":" type ":" expr
#[derive(Debug, Clone)]
pub struct Definition {
    pub vis: Vis,
    pub name: String,
    pub name_loc: Span,
    pub typ: Option<Expression>,
    pub value: Expression,
    pub loc: Span,
}

impl AstNode for Definition {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let (vis, vis_loc) = if let Some(Kw(Keyword::Pub)) = parser.peek_tt() {
            let loc = parser.pop().unwrap().loc;
            (Vis::Public, Some(loc))
        } else {
            (Vis::Private, None)
        };

        let (name, name_loc) =
            expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));
        let lo = vis_loc.unwrap_or(name_loc.clone());

        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punctuation::Colon);

        let typ = if let Some(Punct(Punctuation::Colon)) = parser.peek_tt() {
            None
        } else {
            Some(parse!(parser => Expression))
        };

        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punctuation::Colon);

        let value = parse!(parser => Expression);

        let hi = value.loc.clone();

        Ok(Definition {
            vis,
            name,
            name_loc,
            typ,
            value,
            loc: Span::from_ends(lo, hi),
        })
    }
}
