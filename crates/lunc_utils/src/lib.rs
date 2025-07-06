use std::{
    fmt::{Display, Write},
    ops::Range,
};

pub mod target;
pub mod token;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
}

impl Span {
    /// Zero location.
    pub const ZERO: Span = Span { lo: 0, hi: 0 };

    #[inline(always)]
    pub const fn from_ends(lo: Span, hi: Span) -> Span {
        Span {
            lo: lo.lo,
            hi: hi.hi,
        }
    }
}

#[inline(always)]
pub fn span(lo: impl Into<usize>, hi: impl Into<usize>) -> Span {
    Span {
        lo: lo.into(),
        hi: hi.into(),
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.lo, self.hi)
    }
}

impl From<Span> for Range<usize> {
    fn from(value: Span) -> Self {
        value.lo..value.hi
    }
}

impl<I: Into<usize>, J: Into<usize>> From<(I, J)> for Span {
    fn from((lo, hi): (I, J)) -> Self {
        span(lo, hi)
    }
}

/// Write a u64 in little endian format at the end of the Vec, and returns the
/// offset where it was written
pub fn write_dword(bytes: &mut Vec<u8>, dword: u64) -> usize {
    let offset = bytes.len();

    let qword_bytes = dword.to_le_bytes();
    bytes.extend_from_slice(&qword_bytes);

    offset
}

/// Write a u32 in little endian format at the end of the Vec, and returns the
/// offset where it was written
pub fn write_word(bytes: &mut Vec<u8>, word: u32) -> usize {
    let offset = bytes.len();

    let dword_bytes = word.to_le_bytes();
    bytes.extend_from_slice(&dword_bytes);

    offset
}

/// Write a 24bit value, (byte+word) in little endian format at the end of the
/// Vec, and returns the offset where it was written
pub fn write_b_word(bytes: &mut Vec<u8>, b_word: u32) -> usize {
    if b_word > 0x00FF_FFFF {
        panic!("a byte+word must fit in 24bits")
    }
    let offset = bytes.len();

    let bword_bytes = [
        (b_word & 0xFF) as u8,
        ((b_word >> 8) & 0xFF) as u8,
        ((b_word >> 16) & 0xFF) as u8,
    ];
    bytes.extend_from_slice(&bword_bytes);

    offset
}

/// Write a u16 in little endian format at the end of the Vec, and returns the
/// offset where it was written
pub fn write_half(bytes: &mut Vec<u8>, half: u16) -> usize {
    let offset = bytes.len();

    let word_bytes = half.to_le_bytes();
    bytes.extend_from_slice(&word_bytes);

    offset
}

/// Reads a 64 bit little-endian u64 from the Slice at the given offset.
/// Panics if there are not enough bytes to read a full u64.
pub fn read_dword(bytes: &[u8], offset: usize) -> u64 {
    let end = offset + 8;
    let dword = &bytes[offset..end];
    u64::from_le_bytes(dword.try_into().expect("Slice should be 8 bytes long"))
}

/// Reads a 32 bit little-endian u32 from the Slice at the given offset.
/// Panics if there are not enough bytes to read a full u32.
pub fn read_word(bytes: &[u8], offset: usize) -> u32 {
    let end = offset + 4;
    let word = &bytes[offset..end];
    u32::from_le_bytes(word.try_into().expect("Slice should be 4 bytes long"))
}

/// Reads a 24 bit little-endian byte+word from the Slice at the given offset.
/// Panics if there are not enough bytes to read a full byte+word.
///
/// This function is guaranteed to return a u32 that fits in 24 bits.
pub fn read_b_word(bytes: &[u8], offset: usize) -> u32 {
    let end = offset + 3;
    let b_word = &bytes[offset..end];

    (b_word[0] as u32) | ((b_word[1] as u32) << 8) | ((b_word[2] as u32) << 16)
}

/// Reads a 16 bit little-endian u16 from the Slice at the given offset.
/// Panics if there are not enough bytes to read a full u16.
pub fn read_half(bytes: &[u8], offset: usize) -> u16 {
    let end = offset + 2;
    let half = &bytes[offset..end];
    u16::from_le_bytes(half.try_into().expect("Slice should be 2 bytes long"))
}

/// Reads a 64 bit little-endian u64 from the Slice at the given offset.
/// Panics if there are not enough bytes to read a full u64.
pub fn read_many(bytes: &[u8], offset: usize, size: usize) -> &[u8] {
    let end = offset + size;
    &bytes[offset..end]
}

/// returns an `s` if `num` is equal to one.
///
/// use it like that:
/// ```
/// let number = 123; // let's imagine `number` is the result of a function
/// let idk = format!("you have {number} dollar{}", lun_utils::pluralize(number));
/// ```
pub fn pluralize<I>(num: I) -> &'static str
where
    I: PartialEq + From<u8>,
{
    if num == I::from(1u8) { "" } else { "s" }
}

pub fn list_fmt(list: &[impl Display]) -> String {
    if list.len() == 1 {
        return list[0].to_string();
    }
    let mut res = String::new();

    for (idx, token) in list.iter().enumerate() {
        if idx == list.len() - 2 {
            write!(res, "{token} ")
        } else if idx == list.len() - 1 {
            write!(res, "or {token}")
        } else {
            write!(res, "{token}, ")
        }
        .unwrap();
    }
    res
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
}
