//! Generate pairs of integers.
//!
//! This crate implements [an algorithm](https://people.eecs.berkeley.edu/~wkahan/Math55/pairs.pdf) described by Prof. W. Kahan to enumerate pairs of positive integers.
//!
//! # Correctness
//!
//! The results returned by this crate are correct for all values of `n` up to `2^52`.
//! Results for values of `n` greater than that may be incorrect, due to floating point imprecision.
//!
//! # Usage
//!
//! ```
//! use kahan_pairs::pairs;
//!
//! let mut pairs = pairs();
//!
//! assert_eq!(pairs.next(), Some((1, 1)));
//! assert_eq!(pairs.next(), Some((1, 2)));
//! assert_eq!(pairs.next(), Some((2, 1)));
//! assert_eq!(pairs.next(), Some((1, 3)));
//! assert_eq!(pairs.next(), Some((2, 2)));
//! ```
//!
//! Starting from 0 instead of 1:
//!
//! ```
//! use kahan_pairs::pairs_0;
//!
//! let mut pairs = pairs_0();
//!
//! assert_eq!(pairs.next(), Some((0, 0)));
//! assert_eq!(pairs.next(), Some((0, 1)));
//! assert_eq!(pairs.next(), Some((1, 0)));
//! assert_eq!(pairs.next(), Some((0, 2)));
//! assert_eq!(pairs.next(), Some((1, 1)));
//! ```
//!
//! Calculate for any `n`:
//!
//! ```
//! use kahan_pairs::nth_pair;
//!
//! assert_eq!(nth_pair(100), (9, 6));
//! assert_eq!(nth_pair(99_999), (318, 130));
//!
//! use kahan_pairs::nth_pair_0;
//!
//! assert_eq!(nth_pair_0(105), (13, 0));
//! assert_eq!(nth_pair_0(99_999), (317, 129));
//! ```

use std::{iter::FusedIterator, num::NonZeroU64, ops::RangeFrom};

/// Return an iterator that enumerates every unique pair of positive integers, excluding 0
///
/// # Usage
///
/// ```
/// use kahan_pairs::pairs;
///
/// let mut pairs = pairs();
///
/// assert_eq!(pairs.next(), Some((1, 1)));
/// assert_eq!(pairs.next(), Some((1, 2)));
/// assert_eq!(pairs.next(), Some((2, 1)));
/// assert_eq!(pairs.next(), Some((1, 3)));
/// assert_eq!(pairs.next(), Some((2, 2)));
/// ```
#[inline(always)]
pub fn pairs() -> Pairs {
    Pairs::new()
}

/// Return an iterator that enumerates every unique pair of positive integers, including 0
///
/// # Usage
///
/// ```
/// use kahan_pairs::pairs_0;
///
/// let mut pairs = pairs_0();
///
/// assert_eq!(pairs.next(), Some((0, 0)));
/// assert_eq!(pairs.next(), Some((0, 1)));
/// assert_eq!(pairs.next(), Some((1, 0)));
/// assert_eq!(pairs.next(), Some((0, 2)));
/// assert_eq!(pairs.next(), Some((1, 1)));
/// ```
#[inline(always)]
pub fn pairs_0() -> Pairs0 {
    Pairs0::new()
}

/// Return the `n`th pair of positive integers, according to the crate's namesake algorithm
///
/// # Panics
///
/// Panics if `n == 0`:
///
/// ```should_panic
/// use kahan_pairs::nth_pair;
///
/// let _ = nth_pair(0);
/// ```
///
/// # Usage
///
/// ```
/// use kahan_pairs::nth_pair;
///
/// assert_eq!(nth_pair(100), (9, 6));
/// assert_eq!(nth_pair(99_999), (318, 130));
/// ```
#[inline(always)]
pub fn nth_pair(n: u64) -> (u64, u64) {
    assert_ne!(n, 0, "The algorithm is undefined for n == 0");
    p(n)
}

/// Return the `n`th pair of positive integers, according to the crate's namesake algorithm, or `None` if `n == 0`
///
/// # Usage
///
/// ```
/// use kahan_pairs::try_nth_pair;
///
/// assert_eq!(try_nth_pair(0), None);
/// assert_eq!(try_nth_pair(100), Some((9, 6)));
/// assert_eq!(try_nth_pair(99_999), Some((318, 130)));
/// ```
#[inline(always)]
pub fn try_nth_pair(n: u64) -> Option<(u64, u64)> {
    (n != 0).then(|| p(n))
}

/// Infallibly return the `n`th pair of positive integers, according to the crate's namesake algorithm
///
/// # Usage
///
/// ```
/// use std::num::NonZeroU64;
/// use kahan_pairs::get_nth_pair;
///
/// assert_eq!(get_nth_pair(NonZeroU64::new(100).unwrap()), (9, 6));
/// assert_eq!(get_nth_pair(NonZeroU64::new(99_999).unwrap()), (318, 130));
/// ```
#[inline(always)]
pub fn get_nth_pair(n: NonZeroU64) -> (u64, u64) {
    p(n.get())
}

/// Return the `n`th pair of positive integers, according to a version of the crate's namesake algorithm that includes 0 in the output
///
/// # Panics
///
/// Panics if `n == 0`
///
/// ```should_panic
/// use kahan_pairs::nth_pair_0;
///
/// let _ = nth_pair_0(0);
/// ```
///
/// # Usage
///
/// ```
/// use kahan_pairs::nth_pair_0;
///
/// assert_eq!(nth_pair_0(105), (13, 0));
/// assert_eq!(nth_pair_0(99_999), (317, 129));
/// ```
#[inline(always)]
pub fn nth_pair_0(n: u64) -> (u64, u64) {
    assert_ne!(n, 0, "The algorithm is undefined for n == 0");
    p_0(n)
}

/// Return the `n`th pair of positive integers, according to a version of the crate's namesake algorithm that includes 0 in the output, or `None` if `n == 0`
///
/// # Usage
///
/// ```
/// use kahan_pairs::try_nth_pair_0;
///
/// assert_eq!(try_nth_pair_0(0), None);
/// assert_eq!(try_nth_pair_0(105), Some((13, 0)));
/// assert_eq!(try_nth_pair_0(99_999), Some((317, 129)));
/// ```
#[inline(always)]
pub fn try_nth_pair_0(n: u64) -> Option<(u64, u64)> {
    (n != 0).then(|| p_0(n))
}

/// Infallibly return the `n`th pair of positive integers, according to a version of the crate's namesake algorithm that includes 0 in the output
///
/// # Usage
///
/// ```
/// use std::num::NonZeroU64;
/// use kahan_pairs::get_nth_pair_0;
///
/// assert_eq!(get_nth_pair_0(NonZeroU64::new(105).unwrap()), (13, 0));
/// assert_eq!(get_nth_pair_0(NonZeroU64::new(99_999).unwrap()), (317, 129));
/// ```
#[inline(always)]
pub fn get_nth_pair_0(n: NonZeroU64) -> (u64, u64) {
    p_0(n.get())
}

/// An iterator over every unique pair of positive integers, excluding 0
#[derive(Debug, Clone)]
pub struct Pairs {
    iter: RangeFrom<u64>,
}

impl Pairs {
    #[inline(always)]
    fn new() -> Self {
        Self { iter: 1.. }
    }
}

impl Iterator for Pairs {
    type Item = (u64, u64);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(p)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth(n).map(p)
    }
}

impl FusedIterator for Pairs {}

/// An iterator over every unique pair of positive integers, including 0
#[derive(Debug, Clone)]
pub struct Pairs0 {
    iter: RangeFrom<u64>,
}

impl Pairs0 {
    #[inline(always)]
    fn new() -> Self {
        Self { iter: 1.. }
    }
}

impl Iterator for Pairs0 {
    type Item = (u64, u64);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(p_0)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth(n).map(p_0)
    }
}

impl FusedIterator for Pairs0 {}

/// L(k) := integer part of (1/2 + √(2k-1))
#[inline(always)]
fn l(k: u64) -> u64 {
    // This function involves converting `k` to an f64 and back again,
    // and the largest integer that f64 can exactly represent is 2^53,
    // so if `k` is larger than that, this function may return incorrect results
    let square = (k * 2) - 1;
    let root = (square as f64).sqrt();
    let result = root + 0.5;
    result.trunc() as u64
}

/// M(k) := k - (((L(k) - 1) * L(k)) / 2)
#[inline(always)]
fn m(k: u64) -> u64 {
    let l = l(k);
    k - (((l - 1) * l) / 2)
}

/// P(k) := ( M(k), (1 + L(k)) - M(k) )
#[inline(always)]
fn p(k: u64) -> (u64, u64) {
    let m = m(k);
    (m, (1 + l(k)) - m)
}

/// Like [`p`] but modified to include 0 in the returned pairs
#[inline(always)]
fn p_0(k: u64) -> (u64, u64) {
    let m = m(k);
    (m - 1, l(k) - m)
}
