//! Parsing of lun's directives.

use std::fmt::Display;

use crate::item::Item;

use super::*;

/// Directive in an item
#[derive(Debug, Clone)]
pub enum ItemDirective {
    /// "#" "mod" ident ";"
    Mod { name: String, loc: Span },
    /// "#" "use" path [ "as" ident ] ";"
    Use {
        path: QualifiedPath,
        alias: Option<String>,
        loc: Span,
    },
}

pub fn parse_mod_directive(parser: &mut Parser) -> Result<Item, Diagnostic> {
    let (_, lo) =
        expect_token!(parser => [Punct(Punctuation::Hashtag), ()], Punct(Punctuation::Hashtag));

    expect_token!(parser => [Ident(id), id.clone(), if id.as_str() == "mod"], Ident(String::new()));

    let (name, _) = expect_token!(parser => [Ident(s), s.clone()], "integer literal");

    let (_, hi) =
        expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punct(Punctuation::Semicolon));

    Ok(Item::Directive(ItemDirective::Mod {
        name,
        loc: Span::from_ends(lo, hi),
    }))
}

pub fn parse_use_directive(parser: &mut Parser) -> Result<Item, Diagnostic> {
    let (_, lo) =
        expect_token!(parser => [Punct(Punctuation::Hashtag), ()], Punct(Punctuation::Hashtag));

    expect_token!(parser => [Ident(id), id.clone(), if id.as_str() == "use"], Ident(String::new()));

    let path = parse!(parser => QualifiedPath);

    let alias = if let Some(Kw(Keyword::As)) = parser.peek_tt() {
        parser.pop();
        let alias = expect_token!(noloc: parser => [Ident(id), id.clone()], Ident(String::new()));

        Some(alias)
    } else {
        None
    };

    let (_, hi) =
        expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punct(Punctuation::Semicolon));

    Ok(Item::Directive(ItemDirective::Use {
        path,
        alias,
        loc: Span::from_ends(lo, hi),
    }))
}

#[derive(Debug, Clone)]
pub struct EffectivePath(Vec<String>);

impl EffectivePath {
    /// Creates a new empty effective path
    pub const fn new() -> EffectivePath {
        EffectivePath(Vec::new())
    }

    /// Creates a new effective path with just a single member
    pub fn with_root_member(root_member: impl ToString) -> EffectivePath {
        EffectivePath(vec![root_member.to_string()])
    }

    /// Creates a new effective path from a vector
    pub fn from_vec(vec: Vec<String>) -> EffectivePath {
        assert!(!vec.is_empty());
        EffectivePath(vec)
    }

    /// Returns the amount of members in the path eg:
    ///
    /// `orb`             -> 1
    /// `orb.main`        -> 2
    /// `std.panic.Panic` -> 3
    /// etc..
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Is the path empty?
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice of the underlying path
    pub fn as_slice(&self) -> &[String] {
        &self.0
    }

    /// Returns a mutable reference to the last member of the effective path
    ///
    /// # Example
    ///
    /// `orb`        -> mut ref to `orb`
    /// `orb.driver` -> mut ref to `driver`
    /// *etc..*
    pub fn last_mut(&mut self) -> Option<&mut String> {
        self.0.last_mut()
    }

    /// Returns a reference to the last member of the effective path
    pub fn last(&self) -> Option<&String> {
        self.0.last()
    }

    /// Push a new member to the path
    pub fn push(&mut self, member: String) {
        self.0.push(member)
    }

    /// Pops the last member of the path and returns it
    pub fn pop(&mut self) -> Option<String> {
        self.0.pop()
    }
}

impl<S: ToString> FromIterator<S> for EffectivePath {
    /// Creates a new effective path from an iterator
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        EffectivePath(iter.into_iter().map(|m| m.to_string()).collect())
    }
}

impl Default for EffectivePath {
    fn default() -> Self {
        EffectivePath::new()
    }
}

impl Display for EffectivePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.is_empty() {
            write!(f, "{}", self.as_slice().join("."))
        } else {
            write!(f, "∅")
        }
    }
}

/// ident { "." ident }
#[derive(Debug, Clone)]
pub struct QualifiedPath {
    pub path: EffectivePath,
    pub loc: Span,
}

impl AstNode for QualifiedPath {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let mut path = Vec::new();
        let (id, lo) = expect_token!(parser => [Ident(id), id.clone(); Kw(Keyword::Orb), String::from("orb")], Ident(String::new()));
        path.push(id);

        let mut hi = lo.clone();
        while let Some(Punct(Punctuation::Dot)) = parser.peek_tt() {
            parser.pop();

            let (id, h) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));
            hi = h;
            path.push(id);
        }

        Ok(QualifiedPath {
            path: EffectivePath::from_vec(path),
            loc: Span::from_ends(lo, hi),
        })
    }
}
