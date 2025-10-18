//! Parsing of lun's directives.

use lunc_ast::symbol::EffectivePath;
use lunc_diag::ResultExt;
use lunc_utils::default;

use super::*;

/// Directive in an item
#[derive(Debug, Clone)]
pub enum Directive {
    /// `"#" "mod" ident ";"`
    Mod { name: String, loc: Span },
    /// `"#" "import" path [ "as" ident ] ";"`
    Import {
        path: SpannedPath,
        alias: Option<String>,
        loc: Span,
    },
}

impl Directive {
    /// Name of the [`Directive::Mod`].
    pub const MOD_NAME: &str = "mod";

    /// Name of the [`Directive::Import`].
    pub const IMPORT_NAME: &str = "import";

    /// List of every supported directives name.
    pub const DIRECTIVES: &[&str] = &[
        // all the directives V
        Directive::MOD_NAME,
        Directive::IMPORT_NAME,
    ];
}

/// Spanned [EffectivePath].
pub type SpannedPath = Spanned<EffectivePath>;

/// Directive parsing
impl Parser {
    /// Parse a [`SpannedPath`].
    pub fn parse_spanned_path(&mut self) -> IResult<SpannedPath> {
        let mut path = Vec::new();

        // TEST: no. 1
        if self.eat(ExpToken::Ident) {
            path.push(self.as_ident());
        } else if self.eat(ExpToken::KwOrb) {
            path.push("orb".to_string())
        } else {
            return self.etd_and_bump();
        }

        let lo = self.token_loc();

        let mut hi = lo.clone();
        while self.eat_no_expect(ExpToken::Dot) {
            // TEST: no. 2
            hi = self.expect(ExpToken::Ident)?;
            path.push(self.as_ident());
        }

        Ok(SpannedPath {
            node: EffectivePath::from_vec(path),
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parse an import directive.
    pub fn parse_import_directive(&mut self) -> IResult<Directive> {
        // TEST: n/a
        let lo = self.expect(ExpToken::Pound)?;

        // TEST: n/a
        self.expect(ExpToken::Ident)?;
        debug_assert_eq!(self.as_ident().as_str(), "import");

        let path = self.parse_spanned_path().emit_wval(self.x(), default);

        let alias = if self.eat(ExpToken::KwAs) {
            // TEST: no. 1
            self.expect(ExpToken::Ident)?;

            Some(self.as_ident())
        } else {
            None
        };

        // TEST: no. 2
        let hi = self.expect(ExpToken::Semi)?;

        Ok(Directive::Import {
            path,
            alias,
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parses a mod directive
    pub fn parse_mod_directive(&mut self) -> IResult<Directive> {
        // TEST: n/a
        let lo = self.expect(ExpToken::Pound)?;

        // TEST: n/a
        self.expect(ExpToken::Ident)?;
        debug_assert_eq!(self.as_ident().as_str(), "mod");

        // TEST: no. 1
        self.expect(ExpToken::Ident)?;
        let name = self.as_ident();

        // TEST: no. 2
        let hi = self.expect(ExpToken::Semi)?;

        Ok(Directive::Mod {
            name,
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Recovers the parsing, tries to parse `#` and then bumps the parser.
    pub fn recover_directive(&mut self) -> IResult<()> {
        // expect `#`
        self.expect(ExpToken::Pound)?;

        // bump the parser
        self.expect(ExpToken::Ident)?;

        Ok(())
    }
}
