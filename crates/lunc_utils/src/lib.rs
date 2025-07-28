//! Common useful types, functions and traits across the Lun Compiler.

use std::{
    fmt::{Debug, Display, Write},
    ops::{Add, Range},
};

pub mod pretty;
pub mod symbol;
pub mod target;
pub mod token;

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
/// let number = 123; // let's imagine `number` is the result of a function
/// let idk = format!("you have {number} dollar{}", lunc_utils::pluralize(number));
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

/// This macro expands to [`unreachable_unchecked`] in release mode, or in the
/// [`unreachable`] macro in debug mode.
///
/// # Safety
///
/// This function is not safer than [`unreachable_unchecked`].
///
/// [`unreachable_unchecked`]: std::hint::unreachable_unchecked
/// [`unreachable`]: std::unreachable
#[macro_export]
macro_rules! opt_unrecheable {
    ( $( $tt:tt )* ) => {
        if cfg!(debug_assertions) {
            std::unreachable!( $( $tt )* )
        } else {
            unsafe { std::hint::unreachable_unchecked() }
        }
    };
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
}
