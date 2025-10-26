//! Parsing of lun's directives.

use lunc_ast::{Path, PathSegment};
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
pub type SpannedPath = Spanned<Path>;

/// Directive parsing
impl Parser {
    /// Parse a [`SpannedPath`].
    pub fn parse_spanned_path(&mut self) -> IResult<SpannedPath> {
        let mut path = Path::new();

        // TEST: no. 1
        if self.eat(ExpToken::Ident) {
            path.push(self.as_ident());
        } else if self.eat(ExpToken::KwOrb) {
            path.push_seg(PathSegment::Orb);
        } else {
            return self.etd_and_bump();
        }

        let lo = self.token_loc();

        let mut hi = lo.clone();
        while self.eat_no_expect(ExpToken::ColonColon) {
            // TEST: no. 2
            hi = self.expect(ExpToken::Ident).emit_wval(self.x(), default);
            path.push(self.as_ident());
        }

        Ok(SpannedPath {
            node: path,
            loc: Span::from_ends(lo, hi),
        })
    }

    /// Parse an import directive.
    pub fn parse_import_directive(&mut self) -> IResult<Directive> {
        // TEST: n/a
        let lo = self.expect(ExpToken::Pound)?;

        // TEST: n/a
        self.expect_weak_kw(WeakKw::Import)?;

        let path = self.parse_spanned_path().emit_wval(self.x(), default);

        let alias = if self.eat_no_expect(ExpToken::KwAs) {
            // NOTE: more resilience here would be too complicated and useless
            // TEST: no. 1
            self.expect(ExpToken::Ident)?;

            Some(self.as_ident())
        } else {
            None
        };

        // TEST: no. 2
        self.expect_nae(ExpToken::Semi).emit(self.x());

        let hi = self.token_loc();

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
        self.expect_weak_kw(WeakKw::Mod)?;

        // TEST: no. 1
        self.expect_nae(ExpToken::Ident)?;
        let name = self.as_ident();

        // TEST: no. 2
        self.expect_nae(ExpToken::Semi)?;

        let hi = self.token_loc();

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
