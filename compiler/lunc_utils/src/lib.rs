//! Common useful types, functions and traits across the Lun Compiler.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::{
    fmt::{self, Debug, Display, Write},
    ops::{Add, Range},
    sync::Arc,
};

use clap::ValueEnum;

use crate::{symbol::EffectivePath, token::Keyword};

pub mod idtype;
pub mod pretty;
pub mod symbol;
pub mod token;

pub mod target {
    pub use target_lexicon::*;

    /// Supported targets
    pub const SUPPORTED_TARGETS: [Triple; 1] = [X86_64_LINUX_GNU];

    /// `x86_64-unknown-linux-gnu` target
    pub const X86_64_LINUX_GNU: Triple = Triple {
        architecture: Architecture::X86_64,
        vendor: Vendor::Unknown,
        operating_system: OperatingSystem::Linux,
        environment: Environment::Gnu,
        binary_format: BinaryFormat::Elf,
    };
}
use target_lexicon::Triple;

/// Location of something in a file.
///
/// # Note
///
/// the `lo` and `hi` field expect and byte index into the underlying string,
/// not the nth character. They are byte indices to be more efficient
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
    /// file id, to know which file we are referring to.
    pub fid: FileId,
}

impl Span {
    /// Zero location to the root module
    pub const ZERO: Span = Span {
        lo: 0,
        hi: 0,
        fid: FileId::ROOT_MODULE,
    };

    #[inline(always)]
    pub const fn from_ends(lo: Span, hi: Span) -> Span {
        // NOTE: we are implementing debug_assert_eq manually because it doesn't
        // work at compile time
        if cfg!(debug_assertions) && lo.fid.0 != hi.fid.0 {
            panic!("expected the file ids of both lo and hi spans to be the same.")
        }

        Span {
            lo: lo.lo,
            hi: hi.hi,
            fid: lo.fid,
        }
    }

    pub fn slice_str<'str>(&self, s: &'str str) -> &'str str {
        &s[Range::<usize>::from(self.clone())]
    }
}

impl Add for Span {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        assert_eq!(self.fid, rhs.fid);
        Span {
            lo: self.lo.min(rhs.lo),
            hi: self.hi.max(rhs.hi),
            fid: self.fid,
        }
    }
}

#[inline(always)]
pub fn span(lo: impl Into<usize>, hi: impl Into<usize>, fid: FileId) -> Span {
    Span {
        lo: lo.into(),
        hi: hi.into(),
        fid,
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}..{} (fid = {})",
            self.lo,
            self.hi,
            self.fid.as_usize()
        )
    }
}

impl From<Span> for Range<usize> {
    fn from(value: Span) -> Self {
        value.lo..value.hi
    }
}

impl<I: Into<usize>, J: Into<usize>> From<(I, J, FileId)> for Span {
    fn from((lo, hi, fid): (I, J, FileId)) -> Self {
        span(lo, hi, fid)
    }
}

/// A file id, used to represent, which file we are talking about
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId(u32);

impl FileId {
    /// Note this, file id always refers to the root of the `orb`
    pub const ROOT_MODULE: FileId = FileId(0);

    /// Creates a new FileId, note that it does not register it self to the sink
    pub fn new(num: impl Into<u32>) -> FileId {
        FileId(num.into())
    }

    /// Converts the file id to a usize
    pub fn as_usize(self) -> usize {
        self.0 as usize
    }

    /// Is the file id, the one to the root module?
    pub fn is_root(&self) -> bool {
        *self == Self::ROOT_MODULE
    }
}

/// returns an `s` if `num` is equal to one.
///
/// use it like that:
/// ```
/// # use lunc_utils::pluralize;
/// let number = 123; // let's imagine `number` is the result of a function
/// let idk = format!("you have {number} dollar{}", pluralize(number));
/// ```
pub fn pluralize<I>(num: I) -> &'static str
where
    I: PartialEq + From<u8>,
{
    if num == I::from(1u8) { "" } else { "s" }
}

/// It's [`list_fmt_with_word`] where word = "or"
pub fn list_fmt(list: &[impl Display]) -> String {
    list_fmt_with_word(list, "or")
}

/// format the list of things with a specified word at the end.
///
/// # Examples
///
/// ```
/// # use lunc_utils::list_fmt_with_word;
/// #
/// assert_eq!(list_fmt_with_word(&[1], ""), "1".to_string());
/// assert_eq!(list_fmt_with_word(&['a', 'b'], "or"), "a or b".to_string());
/// assert_eq!(list_fmt_with_word(&['a', 'b'], "and"), "a and b".to_string());
/// assert_eq!(list_fmt_with_word(&['a', 'b', 'c', 'd', 'e'], "or"), "a, b, c, d or e".to_string());
/// assert_eq!(list_fmt_with_word(&['a', 'b', 'c', 'd', 'e'], "and"), "a, b, c, d and e".to_string());
/// ```
pub fn list_fmt_with_word(list: &[impl Display], word: &str) -> String {
    if list.len() == 1 {
        return list[0].to_string();
    }
    let mut res = String::new();

    for (idx, token) in list.iter().enumerate() {
        if idx == list.len() - 2 {
            write!(res, "{token} ")
        } else if idx == list.len() - 1 {
            write!(res, "{word} {token}")
        } else {
            write!(res, "{token}, ")
        }
        .unwrap();
    }
    res
}

/// Formats a list with commas between
pub fn join_display<T: Display>(items: &[T]) -> String {
    items
        .iter()
        .map(|item| item.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

/// Compute the number of "digits" needed to represent `n` in the given radix (`RADIX`).
///
/// This function supports exactly four radices: 2 (binary), 8 (octal), 10 (decimal), and 16 (hexadecimal).
/// Any other `RADIX` will produce a compile-time error.
///
/// # Parameters
///
/// - `n`: The non-negative integer (`u128`) whose digit-length is computed.
/// - `RADIX`: A const generic specifying the base/radix. Must be one of 2, 8, 10, or 16.
///
/// # Returns
///
/// The count of "digits" (or characters) needed to express `n` in the specified base:
///
/// - **Binary (2)**: number of bits = position of highest set bit + 1 (e.g., 0b10110 = 5 digits).
/// - **Octal (8)**: `ceil(bit_length / 3)` since each octal digit encodes 3 bits.
/// - **Hex (16)**: `ceil(bit_length / 4)` since each hex digit encodes 4 bits.
/// - **Decimal (10)**: uses an unrolled `match` over constant ranges for maximum speed.
///
/// # Panics
///
/// If instantiated with any `RADIX` other than 2, 8, 10, or 16, this will fail
/// at compile time with a type-check error.
///
/// # Complexity
///
/// - **Binary/Octal/Hex**: O(1) bit-operations and arithmetic.
/// - **Decimal**: O(1) range comparisons via a large `match` (constant-time w.r.t. input).
///
/// # Examples
///
/// Basic usage in decimal:
/// ```rust
/// # use lunc_utils::fast_digit_length;
/// let n = 42u128;
/// assert_eq!(fast_digit_length::<10>(n), 2);
/// ```
///
/// Binary bit-length:
/// ```rust
/// # use lunc_utils::fast_digit_length;
/// assert_eq!(fast_digit_length::<2>(0b101101), 6);
/// ```
///
/// Octal digits:
/// ```rust
/// # use lunc_utils::fast_digit_length;
/// assert_eq!(fast_digit_length::<8>(0o755), 3);
/// ```
///
/// Hexadecimal digits:
/// ```rust
/// # use lunc_utils::fast_digit_length;
/// assert_eq!(fast_digit_length::<16>(0xdead_beef), 8);
/// ```
pub fn fast_digit_length<const RADIX: u32>(n: u128) -> u32 {
    // Compile‑time check: only these four radices are allowed.
    // The trick below will fail to compile if this assertion can’t be
    // proven true at compile time for your RADIX.
    const {
        assert!(RADIX == 2 || RADIX == 8 || RADIX == 10 || RADIX == 16);
    };

    // Helper for bit‑length: for n>0, 128 - leading_zeros, else 1.
    #[inline]
    fn bit_length(n: u128) -> u32 {
        if n == 0 { 1 } else { 128 - n.leading_zeros() }
    }

    // Dispatch on the const RADIX. Each branch is evaluated at compile time,
    // and the others are dropped completely.
    if RADIX == 2 {
        // binary: one bit per digit
        bit_length(n)
    } else if RADIX == 8 {
        // octal: 3 bits per digit → ceil(bitlen/3)
        let bits = bit_length(n);
        bits.div_ceil(3)
    } else if RADIX == 16 {
        // hex: 4 bits per digit → ceil(bitlen/4)
        let bits = bit_length(n);
        bits.div_ceil(4)
    } else {
        // decimal: unrolled range match, up to 39 digits for u128
        match n {
            0..=9                      => 1,
            10..=99                    => 2,
            100..=999                  => 3,
            1_000..=9_999              => 4,
            10_000..=99_999            => 5,
            100_000..=999_999          => 6,
            1_000_000..=9_999_999      => 7,
            10_000_000..=99_999_999    => 8,
            100_000_000..=999_999_999  => 9,
            1_000_000_000..=9_999_999_999 => 10,
            10_000_000_000..=99_999_999_999 => 11,
            100_000_000_000..=999_999_999_999 => 12,
            1_000_000_000_000..=9_999_999_999_999 => 13,
            10_000_000_000_000..=99_999_999_999_999 => 14,
            100_000_000_000_000..=999_999_999_999_999 => 15,
            1_000_000_000_000_000..=9_999_999_999_999_999 => 16,
            10_000_000_000_000_000..=99_999_999_999_999_999 => 17,
            100_000_000_000_000_000..=999_999_999_999_999_999 => 18,
            1_000_000_000_000_000_000..=9_999_999_999_999_999_999 => 19,
            10_000_000_000_000_000_000..=99_999_999_999_999_999_999 => 20,
            100_000_000_000_000_000_000..=999_999_999_999_999_999_999 => 21,
            1_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999 => 22,
            10_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999 => 23,
            100_000_000_000_000_000_000_000..=999_999_999_999_999_999_999_999 => 24,
            1_000_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999_999 => 25,
            10_000_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999_999 => 26,
            100_000_000_000_000_000_000_000_000..=999_999_999_999_999_999_999_999_999 => 27,
            1_000_000_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999_999_999 => 28,
            10_000_000_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999_999_999 => 29,
            100_000_000_000_000_000_000_000_000_000..=999_999_999_999_999_999_999_999_999_999 => 30,
            1_000_000_000_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999_999_999_999 => 31,
            10_000_000_000_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999_999_999_999 => 32,
            100_000_000_000_000_000_000_000_000_000_000..=999_999_999_999_999_999_999_999_999_999_999 => 33,
            1_000_000_000_000_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999_999_999_999_999 => 34,
            10_000_000_000_000_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999_999_999_999_999 => 35,
            100_000_000_000_000_000_000_000_000_000_000_000..=999_999_999_999_999_999_999_999_999_999_999_999 => 36,
            1_000_000_000_000_000_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999_999_999_999_999_999 => 37,
            10_000_000_000_000_000_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999_999_999_999_999_999 => 38,
            _ /* up to u128::MAX */   => 39,
        }
    }
}

/// Lowers down a node from a high representation, like AST and lowers it down
/// to a new representation, DSIR in the case of AST.
pub trait FromHigher: Sized {
    /// The type of the node that is the higher representation of [`Self`].
    type Higher;

    /// Takes a high node and lowers it to a low node.
    fn lower(node: Self::Higher) -> Self;
}

impl<T: FromHigher> FromHigher for Vec<T> {
    type Higher = Vec<T::Higher>;

    fn lower(nodes: Self::Higher) -> Self {
        nodes.into_iter().map(lower).collect()
    }
}

impl<T: FromHigher> FromHigher for Option<T> {
    type Higher = Option<T::Higher>;

    fn lower(node: Self::Higher) -> Self {
        node.map(lower)
    }
}

impl<T: FromHigher> FromHigher for Box<T> {
    type Higher = Box<T::Higher>;

    fn lower(node: Self::Higher) -> Self {
        Box::new(T::lower(*node))
    }
}

/// Lowers down a node of a higher representation to a node of a lower
/// representation, see [`FromHigher`]
pub fn lower<T: FromHigher>(node: T::Higher) -> T {
    T::lower(node)
}

/// Computes the Levenshtein distance between two strings `a` and `b`.
///
/// This distance is the minimum number of single-character edits
/// (insertions, deletions, or substitutions) required to change `a` into `b`.
///
/// # Examples
/// ```
/// # use lunc_utils::levenshtein_distance;
/// assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
/// assert_eq!(levenshtein_distance("apple", "aple"), 1);
/// ```
pub fn levenshtein_distance(a: &str, b: &str) -> usize {
    if a == b {
        // short circuiting - the strings are identical
        return 0;
    }

    let (n, m) = (a.len(), b.len());

    if n == 0 {
        // short circuiting - string a is empty
        return m;
    }
    if m == 0 {
        // short circuiting - string b is empty
        return n;
    }

    let a = a.as_bytes();
    let b = b.as_bytes();

    let mut dp = vec![vec![0; m + 1]; n + 1];

    for (i, item) in dp.iter_mut().enumerate().take(n + 1) {
        item[0] = i;
    }
    for j in 0..=m {
        dp[0][j] = j;
    }

    for i in 1..=n {
        for j in 1..=m {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            let deletion = dp[i - 1][j] + 1;
            let insertion = dp[i][j - 1] + 1;
            let substitution = dp[i - 1][j - 1] + cost;

            dp[i][j] = deletion.min(insertion).min(substitution);
        }
    }

    dp[n][m]
}

/// Default distance allowed for suggestions.
pub const DEFAULT_MAX_LEVENSHTEIN_DISTANCE: usize = 3;

/// Suggests the closest match from a dictionary to a given input word,
/// using the Levenshtein distance. Returns `Some(suggestion)` if the
/// closest word is within `max_dist` edits, or `None` otherwise.
///
/// # Arguments
///
/// * `word` - The input word to check for corrections.
/// * `dictionary` - A list of known valid words.
/// * `max_dist` - The maximum edit distance allowed for a suggestion.
///
/// # Examples
/// ```
/// # use lunc_utils::suggest;
/// let fruits = ["apple", "banana"];
/// assert_eq!(suggest("aple", &fruits, 2), Some("apple"));
/// assert_eq!(suggest("zzzzz", &fruits, 2), None);
/// ```
pub fn suggest<'a>(word: &str, dictionary: &'a [&str], max_dist: usize) -> Option<&'a str> {
    let word = word.to_lowercase();
    let mut best_match = None;
    let mut best_distance = max_dist + 1;

    for &candidate in dictionary {
        let dist = levenshtein_distance(&word, &candidate.to_lowercase());
        if dist < best_distance {
            best_distance = dist;
            best_match = Some(candidate);
        }
    }

    if best_distance <= max_dist {
        best_match
    } else {
        None
    }
}

/// Return `true` if a number is a power of 2.
pub fn is_pow2(x: u32) -> bool {
    x != 0 && (x & (x - 1)) == 0
}

/// This macro expands to [`unreachable_unchecked`] in release mode, or in the
/// [`unreachable`] macro in debug mode.
///
/// # Safety
///
/// This function is not safer than [`unreachable_unchecked`].
///
/// [`unreachable_unchecked`]: std::hint::unreachable_unchecked
/// [`unreachable`]: std::unreachable
#[cfg(debug_assertions)]
#[macro_export]
macro_rules! opt_unreachable {
    ( $( $tt:tt )* ) => {
        std::unreachable!( $( $tt )* )
    };
}

/// This macro expands to [`unreachable_unchecked`] in release mode, or in the
/// [`unreachable`] macro in debug mode.
///
/// # Safety
///
/// This function is not safer than [`unreachable_unchecked`].
///
/// [`unreachable_unchecked`]: std::hint::unreachable_unchecked
/// [`unreachable`]: std::unreachable
#[cfg(not(debug_assertions))]
#[macro_export]
macro_rules! opt_unreachable {
    ( $( $tt:tt )* ) => {
        unsafe { std::hint::unreachable_unchecked() }
    };
}

/// Is this string identifier compatible?
pub fn is_identifier(id: &str) -> bool {
    // identifiers only support ascii for now
    if !id.is_ascii() {
        return false;
    }

    // identifiers cannot have a whitespace
    if id.contains(char::is_whitespace) {
        return false;
    }

    // identifiers always start with a letter
    if !id.chars().next().unwrap().is_alphabetic() {
        return false;
    }

    // identifier cannot be a keyword
    if Keyword::ALL_KEYWORDS.contains(&id) {
        return false;
    }

    true
}

/// Build options
#[derive(Debug, Clone)]
pub struct BuildOptions {
    inner: Arc<BuildOptionsInternal>,
}

impl BuildOptions {
    /// Create a new build options
    pub fn new(orb_name: impl ToString, orb_type: OrbType, target: Triple) -> BuildOptions {
        BuildOptions {
            inner: Arc::new(BuildOptionsInternal {
                orb_name: orb_name.to_string(),
                orb_type,
                target,
            }),
        }
    }

    /// Get the orb name
    pub fn orb_name(&self) -> &str {
        &self.inner.orb_name
    }

    /// Get the orb type
    pub fn orb_type(&self) -> OrbType {
        self.inner.orb_type
    }

    /// Get the target triplet
    pub fn target(&self) -> &Triple {
        &self.inner.target
    }
}

#[derive(Debug, Clone)]
pub struct BuildOptionsInternal {
    orb_name: String,
    orb_type: OrbType,
    target: Triple,
}

/// Mangles an effective path into a realname.
///
/// An effective path `std.mem.transmute` is mangled like so:
///
/// ## 1. The prefix `_L`
///
/// We append a prefix to the result, it's always `_L` and the `L` is for `Lun`.
///
/// result = `_L`
///
/// ## 2. For each member
///
/// We append the length of a member in decimal form is taking and the member
/// like so
///
/// ### For `std`
///
/// result = `_L3std`
///
/// ### For `mem`
///
/// result = `_L3std3mem`
///
/// ### For `transmute`
///
/// result = `_L3std3mem9transmute`
///
/// ### If we had another long member, like `hello_world_im_so_long`
///
/// we just append `22hello_world_im_so_long` to the result.
///
/// ## 3. Finished
///
/// This is super simple mangling.
pub fn mangle(path: &EffectivePath) -> String {
    let mut result = String::from("_L");

    for member in path.members() {
        let mangled = format!("{}{member}", member.len());

        result.push_str(&mangled);
    }

    result
}

/// Type of Orb.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, ValueEnum)]
pub enum OrbType {
    /// Binary
    Bin,
    /// Lun lib
    Llib,
}

impl Display for OrbType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bin => write!(f, "bin"),
            Self::Llib => write!(f, "lib"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pluralize() {
        assert_eq!("s", pluralize(2));
        assert_eq!("", pluralize(1i16));
        assert_eq!("s", pluralize(0));
        assert_eq!("s", pluralize(123usize));
        assert_eq!("s", pluralize(456u128));
        assert_eq!("s", pluralize(789i128));
    }

    /// Exhaustive test for smaller range (u8) to validate algorithm correctness.
    #[test]
    fn exhaustive_24bit_range() {
        for n in 0u128..=(1 << 24) {
            for &radix in &[2u32, 8, 10, 16] {
                let computed = match radix {
                    2 => fast_digit_length::<2>(n),
                    8 => fast_digit_length::<8>(n),
                    10 => fast_digit_length::<10>(n),
                    16 => fast_digit_length::<16>(n),
                    _ => unreachable!(),
                };
                let repr_len = match radix {
                    2 => format!("{n:b}").len(),
                    8 => format!("{n:o}").len(),
                    10 => n.to_string().len(),
                    16 => format!("{n:x}").len(),
                    _ => unreachable!(),
                };
                assert_eq!(
                    computed as usize, repr_len,
                    "mismatch for n={n} radix={radix}",
                );
            }
        }
    }

    /// Randomized test for large u128 values.
    #[test]
    fn random_sampled_u128_range() {
        use std::time::{SystemTime, UNIX_EPOCH};

        // Use a very simple seed based on system time.
        let seed = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut x = seed;
        for _ in 0..10_000 {
            // Simple linear congruential generator
            x = x.wrapping_mul(6364136223846793005).wrapping_add(1);
            let n = x as u128 ^ ((x as u128) << 64);

            for &radix in &[2u32, 8, 10, 16] {
                let computed = match radix {
                    2 => fast_digit_length::<2>(n),
                    8 => fast_digit_length::<8>(n),
                    10 => fast_digit_length::<10>(n),
                    16 => fast_digit_length::<16>(n),
                    _ => unreachable!(),
                };
                let repr_len = match radix {
                    2 => format!("{n:b}").len(),
                    8 => format!("{n:o}").len(),
                    10 => n.to_string().len(),
                    16 => format!("{n:x}").len(),
                    _ => unreachable!(),
                };
                assert_eq!(
                    computed as usize, repr_len,
                    "mismatch for n={n} radix={radix}",
                );
            }
        }
    }

    #[test]
    fn levenshtein_empty() {
        assert_eq!(levenshtein_distance("", ""), 0);
        assert_eq!(levenshtein_distance("", "abc"), 3);
        assert_eq!(levenshtein_distance("abc", ""), 3);
    }

    #[test]
    fn levenshtein_equal() {
        assert_eq!(levenshtein_distance("rust", "rust"), 0);
    }

    #[test]
    fn levenshtein_substitution() {
        assert_eq!(levenshtein_distance("kitten", "sitten"), 1);
        assert_eq!(levenshtein_distance("flaw", "lawn"), 2);
    }

    #[test]
    fn levenshtein_insertion_deletion() {
        assert_eq!(levenshtein_distance("apple", "aple"), 1);
        assert_eq!(levenshtein_distance("aple", "apple"), 1);
    }

    #[test]
    fn levenshtein_mixed() {
        assert_eq!(levenshtein_distance("gumbo", "gambol"), 2);
    }

    #[test]
    fn suggest_exact() {
        let fruits = ["apple", "banana", "orange"];
        assert_eq!(suggest("apple", &fruits, 2), Some("apple"));
    }

    #[test]
    fn suggest_typo() {
        let fruits = ["apple", "banana", "orange"];
        assert_eq!(suggest("aple", &fruits, 2), Some("apple"));
        assert_eq!(suggest("ornge", &fruits, 2), Some("orange"));
    }

    #[test]
    fn suggest_no_match() {
        let fruits = ["apple", "banana", "orange"];
        assert_eq!(suggest("xyz", &fruits, 1), None);
    }

    #[test]
    fn suggest_multiple_candidates() {
        let words = ["cat", "bat", "rat"];
        // all at distance 1; should pick the first encountered ("cat")
        assert_eq!(suggest("cot", &words, 1), Some("cat"));
    }

    #[test]
    fn identifiers_checks_test() {
        assert!(is_identifier("hello"));
        assert!(!is_identifier("ça"));
        assert!(!is_identifier("Hello, World!"));
        assert!(!is_identifier("orb"));
    }
}
