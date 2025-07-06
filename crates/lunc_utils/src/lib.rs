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
    /// file id, to know which file we are refering to.
    pub fid: FileId,
}

impl Span {
    /// Zero location to the root file
    pub const ZERO: Span = Span {
        lo: 0,
        hi: 0,
        fid: FileId::ZERO,
    };

    #[inline(always)]
    pub const fn from_ends(lo: Span, hi: Span) -> Span {
        // NOTE: we are implementing debug_assert_eq manualy because it doesn't
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
        write!(f, "{}..{}", self.lo, self.hi)
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileId(u32);

impl FileId {
    /// Note this, file id always refers to the root of the `orb`
    pub const ZERO: FileId = FileId(0);

    pub fn new(num: impl Into<u32>) -> FileId {
        FileId(num.into())
    }

    pub fn as_usize(self) -> usize {
        self.0 as usize
    }
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
