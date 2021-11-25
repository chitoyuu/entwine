//! Slice-like type for tracking indices along with sorts.

use core::borrow::Borrow;
use core::cell::Cell;
use core::hash::Hash;
use core::mem;
use core::ops::{Bound, Range, RangeBounds};
use core::ptr;

use crate::raw::{ElementCtor, EntwineCore, Ptr, PtrMut, Ref, RefMut, Value};
use crate::{RefMutT, RefT};

/// Slice-like type for tracking indices along with sorts. Semantically a `[bool]`.
///
/// This type is only available with the `alloc` feature.
///
/// # Example
///
/// ```rust
/// # use entwine::Entwine;
/// # use entwine::index::TrackIndex;
/// let mut xs = [5, 7, -2, 4, 9, 0, 3];
///
/// // This creates an imaginary slice tracking the index of "9", that can be
/// // entwined with real ones.
/// let mut idx = TrackIndex::new(4, xs.len());
///
/// (&mut xs[..], &mut idx).sort_unstable_by(|(l, _), (r, _)| l.cmp(r));
///
/// // "9" is now moved to the last place
/// assert_eq!([-2, 0, 3, 4, 5, 7, 9], xs);
/// assert_eq!(Some(6), idx.get());
/// ```
pub struct TrackIndex<I = Cell<usize>> {
    idx: I,
    range: Range<usize>,
}

impl TrackIndex<Cell<usize>> {
    /// Creates a new [`TrackIndex`] using the given starting locations.
    ///
    /// # Panics
    ///
    /// If `idx >= len`.
    pub fn new(idx: usize, len: usize) -> Self {
        assert!(idx < len);

        TrackIndex {
            idx: Cell::new(idx),
            range: 0..len,
        }
    }

    /// Get the current index of the element being tracked, or `None` if the tracked
    /// index is lost.
    ///
    /// Semantically, this is the last index a `true` value has been written to, unless
    /// it has since been cleared.
    pub fn get(&self) -> Option<usize> {
        let idx = self.idx.get();
        (idx != usize::MAX).then(|| idx)
    }
}

unsafe impl<I> EntwineCore for TrackIndex<I>
where
    I: Borrow<Cell<usize>>,
{
    type ElementCtor = IndexElementCtor;

    type RangeMut<'a>
    where
        Self: 'a,
    = TrackIndex<&'a Cell<usize>>;

    fn len(&self) -> usize {
        self.range.len()
    }

    fn range_mut<R: RangeBounds<usize>>(&mut self, range: R) -> Option<Self::RangeMut<'_>> {
        let start = match range.start_bound() {
            Bound::Unbounded => self.range.start,
            Bound::Included(s) => self.range.start.saturating_add(*s),
            Bound::Excluded(s) => self.range.start.saturating_add(*s).saturating_add(1),
        };

        let end = match range.end_bound() {
            Bound::Unbounded => self.range.end,
            Bound::Included(s) => self.range.start.saturating_add(*s).saturating_add(1),
            Bound::Excluded(s) => self.range.start.saturating_add(*s),
        };

        if start > end || end > self.range.end {
            None
        } else {
            Some(TrackIndex {
                idx: self.idx.borrow(),
                range: start..end,
            })
        }
    }

    fn split_at_mut(&mut self, mid: usize) -> (Self::RangeMut<'_>, Self::RangeMut<'_>) {
        assert!(mid < self.range.len());

        let mid = mid + self.range.start;

        let idx = self.idx.borrow();

        let mut left_range = self.range.clone();
        left_range.end = mid;

        let mut right_range = self.range.clone();
        right_range.start = mid;

        let left = TrackIndex {
            idx,
            range: left_range,
        };

        let right = TrackIndex {
            idx,
            range: right_range,
        };

        (left, right)
    }

    fn reverse(&mut self) {
        let idx = self.idx.borrow();
        if self.range.contains(&idx.get()) {
            let delta = idx.get() - self.range.start;
            idx.set(self.range.end - delta - 1);
        }
    }

    unsafe fn get_unchecked(&self, idx: usize) -> RefT<'_, Self> {
        IndexRef(RefKind::Imaginary {
            idx: self.idx.borrow(),
            cur: self.range.start.saturating_add(idx),
        })
    }

    unsafe fn get_unchecked_mut(&mut self, idx: usize) -> RefMutT<'_, Self> {
        IndexRefMut(RefKind::Imaginary {
            idx: self.idx.borrow(),
            cur: self.range.start.saturating_add(idx),
        })
    }
}

#[doc(hidden)]
pub struct IndexElementCtor {
    _private: (),
}

impl ElementCtor for IndexElementCtor {
    type Value = bool;

    type Ref<'a>
    where
        Self: 'a,
    = IndexRef<'a>;

    type RefMut<'a>
    where
        Self: 'a,
    = IndexRefMut<'a>;

    type Ptr = IndexPtr;
    type PtrMut = IndexPtrMut;
}

unsafe impl Value<IndexElementCtor> for bool {
    fn is_zero_sized() -> bool {
        false
    }

    fn as_ref(&self) -> IndexRef<'_> {
        IndexRef(RefKind::Real(self))
    }

    fn as_mut(&mut self) -> IndexRefMut<'_> {
        IndexRefMut(RefKind::Real(self))
    }
}

#[derive(Clone, Copy)]
enum RefKind<R, I> {
    Real(R),
    Imaginary { idx: I, cur: usize },
}

macro_rules! coerce_ref_kind {
    ($src:expr, $ty:ident) => {
        match $src {
            RefKind::Real(b) => $ty(RefKind::Real(*b)),
            RefKind::Imaginary { idx, cur } => $ty(RefKind::Imaginary {
                idx: *idx,
                cur: *cur,
            }),
        }
    };
}

/// Reference to a tracking slot, semantically a `&bool`.
#[derive(Clone, Copy)]
pub struct IndexRef<'a>(RefKind<&'a bool, &'a Cell<usize>>);

unsafe impl<'a> Ref<'a, IndexElementCtor> for IndexRef<'a> {
    fn reborrow<'r>(self) -> IndexRef<'r>
    where
        'a: 'r,
    {
        self
    }

    fn to_ptr(&self) -> IndexPtr {
        coerce_ref_kind!(&self.0, IndexPtr)
    }
}

/// Reference to a tracking slot, semantically a `&mut bool`.
pub struct IndexRefMut<'a>(RefKind<&'a mut bool, &'a Cell<usize>>);

unsafe impl<'a> RefMut<'a, IndexElementCtor> for IndexRefMut<'a> {
    fn reborrow_mut<'r>(self) -> IndexRefMut<'r>
    where
        'a: 'r,
    {
        self
    }

    fn to_ref(&self) -> IndexRef<'_> {
        coerce_ref_kind!(&self.0, IndexRef)
    }

    fn to_mut_ptr(&mut self) -> IndexPtrMut {
        coerce_ref_kind!(&mut self.0, IndexPtrMut)
    }
}

/// Pointer to a tracking slot, semantically a `*const bool`.
#[derive(Clone, Copy)]
pub struct IndexPtr(RefKind<*const bool, *const Cell<usize>>);

impl PartialEq for IndexPtr {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (RefKind::Real(l), RefKind::Real(r)) => ptr::eq(l, r),
            (
                RefKind::Imaginary {
                    idx: l_idx,
                    cur: l_cur,
                },
                RefKind::Imaginary {
                    idx: r_idx,
                    cur: r_cur,
                },
            ) => ptr::eq(l_idx, r_idx) && l_cur == r_cur,
            _ => false,
        }
    }
}
impl Eq for IndexPtr {}
impl Hash for IndexPtr {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        match &self.0 {
            RefKind::Real(l) => l.hash(state),
            RefKind::Imaginary { idx, cur } => {
                idx.hash(state);
                cur.hash(state);
            }
        }
    }
}

unsafe impl Ptr<IndexElementCtor> for IndexPtr {
    unsafe fn deref<'r>(&self) -> IndexRef<'r> {
        match self.0 {
            RefKind::Real(b) => IndexRef(RefKind::Real(&*b)),
            RefKind::Imaginary { idx, cur } => IndexRef(RefKind::Imaginary { idx: &*idx, cur }),
        }
    }

    fn null() -> Self {
        IndexPtr(RefKind::Real(ptr::null()))
    }

    unsafe fn add(&self, count: usize) -> Self {
        match self.0 {
            RefKind::Real(b) => IndexPtr(RefKind::Real(b.add(count))),
            RefKind::Imaginary { idx, cur } => IndexPtr(RefKind::Imaginary {
                idx,
                cur: cur.saturating_add(count),
            }),
        }
    }

    unsafe fn offset(&self, count: isize) -> Self {
        match self.0 {
            RefKind::Real(b) => IndexPtr(RefKind::Real(b.offset(count))),
            RefKind::Imaginary { idx, cur } => IndexPtr(RefKind::Imaginary {
                idx,
                cur: if count > 0 {
                    cur.saturating_add(count as usize)
                } else {
                    cur.checked_sub((-count) as usize).unwrap()
                },
            }),
        }
    }

    fn width(l: &Self, r: &Self) -> usize {
        match (&l.0, &r.0) {
            (RefKind::Real(l), RefKind::Real(r)) => {
                (*r as usize - *l as usize) / mem::size_of::<bool>()
            }
            (RefKind::Imaginary { cur: l_cur, .. }, RefKind::Imaginary { cur: r_cur, .. }) => {
                r_cur - l_cur
            }
            _ => panic!("invalid operands"),
        }
    }

    unsafe fn read(src: &Self) -> bool {
        match src.0 {
            RefKind::Real(b) => ptr::read(b),
            RefKind::Imaginary { idx, cur } => (&*idx).get() == cur,
        }
    }
}

/// Pointer to a tracking slot, semantically a `*mut bool`.
#[derive(Clone, Copy)]
pub struct IndexPtrMut(RefKind<*mut bool, *const Cell<usize>>);

impl PartialEq for IndexPtrMut {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (RefKind::Real(l), RefKind::Real(r)) => ptr::eq(l, r),
            (
                RefKind::Imaginary {
                    idx: l_idx,
                    cur: l_cur,
                },
                RefKind::Imaginary {
                    idx: r_idx,
                    cur: r_cur,
                },
            ) => ptr::eq(l_idx, r_idx) && l_cur == r_cur,
            _ => false,
        }
    }
}
impl Eq for IndexPtrMut {}
impl Hash for IndexPtrMut {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        match &self.0 {
            RefKind::Real(l) => l.hash(state),
            RefKind::Imaginary { idx, cur } => {
                idx.hash(state);
                cur.hash(state);
            }
        }
    }
}

unsafe impl PtrMut<IndexElementCtor> for IndexPtrMut {
    unsafe fn deref_mut<'r>(&self) -> IndexRefMut<'r> {
        match self.0 {
            RefKind::Real(b) => IndexRefMut(RefKind::Real(&mut *b)),
            RefKind::Imaginary { idx, cur } => IndexRefMut(RefKind::Imaginary { idx: &*idx, cur }),
        }
    }

    unsafe fn to_const(&self) -> IndexPtr {
        coerce_ref_kind!(&self.0, IndexPtr)
    }

    fn null_mut() -> Self {
        IndexPtrMut(RefKind::Real(ptr::null_mut()))
    }

    unsafe fn add(&self, count: usize) -> Self {
        match self.0 {
            RefKind::Real(b) => IndexPtrMut(RefKind::Real(b.add(count))),
            RefKind::Imaginary { idx, cur } => IndexPtrMut(RefKind::Imaginary {
                idx,
                cur: cur.saturating_add(count),
            }),
        }
    }

    unsafe fn offset(&self, count: isize) -> Self {
        match self.0 {
            RefKind::Real(b) => IndexPtrMut(RefKind::Real(b.offset(count))),
            RefKind::Imaginary { idx, cur } => IndexPtrMut(RefKind::Imaginary {
                idx,
                cur: if count > 0 {
                    cur.saturating_add(count as usize)
                } else {
                    cur.checked_sub((-count) as usize).unwrap()
                },
            }),
        }
    }

    fn width(l: &Self, r: &Self) -> usize {
        match (&l.0, &r.0) {
            (RefKind::Real(l), RefKind::Real(r)) => {
                (*r as usize - *l as usize) / mem::size_of::<bool>()
            }
            (RefKind::Imaginary { cur: l_cur, .. }, RefKind::Imaginary { cur: r_cur, .. }) => {
                r_cur - l_cur
            }
            _ => panic!("invalid operands"),
        }
    }

    unsafe fn copy_nonoverlapping(src: &IndexPtr, dst: &Self, n: usize) {
        match (src.0, dst.0) {
            (RefKind::Real(l), RefKind::Real(r)) => ptr::copy_nonoverlapping(l, r, n),
            (
                RefKind::Imaginary {
                    idx: l_idx,
                    cur: l_cur,
                },
                RefKind::Imaginary {
                    idx: r_idx,
                    cur: r_cur,
                },
            ) if ptr::eq(l_idx, r_idx) => {
                let idx = &*l_idx;
                let cur_idx = idx.get();
                if cur_idx >= l_cur && cur_idx < l_cur + n {
                    idx.set(cur_idx - l_cur + r_cur);
                } else if cur_idx >= r_cur && cur_idx < r_cur + n {
                    idx.set(usize::MAX);
                }
            }
            _ => {
                let mut src = *src;
                let mut dst = *dst;

                for _ in 0..n {
                    let v = Ptr::read(&src);
                    PtrMut::write(&dst, v);
                    src = src.add(1);
                    dst = dst.add(1);
                }
            }
        }
    }

    unsafe fn swap(a: &Self, b: &Self) {
        match (a.0, b.0) {
            (RefKind::Real(l), RefKind::Real(r)) => ptr::swap(l, r),
            (
                RefKind::Imaginary {
                    idx: l_idx,
                    cur: l_cur,
                },
                RefKind::Imaginary {
                    idx: r_idx,
                    cur: r_cur,
                },
            ) if ptr::eq(l_idx, r_idx) => {
                let idx = &*l_idx;
                let cur_idx = idx.get();
                if cur_idx == l_cur {
                    idx.set(r_cur);
                } else if cur_idx == r_cur {
                    idx.set(l_cur);
                }
            }
            _ => {
                let l_value = Ptr::read(&a.to_const());
                let r_value = Ptr::read(&b.to_const());
                PtrMut::write(a, r_value);
                PtrMut::write(b, l_value);
            }
        }
    }

    unsafe fn write(dst: &Self, src: bool) {
        match dst.0 {
            RefKind::Real(b) => ptr::write(b, src),
            RefKind::Imaginary { idx, cur } => {
                let idx = &*idx;
                if src {
                    idx.set(cur);
                } else if idx.get() == cur {
                    idx.set(usize::MAX);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    use crate::Entwine;

    #[test]
    fn it_works() {
        let mut xs = [5, 7, -2, 4, 9, 0, 3];
        let mut idx = TrackIndex::new(4, xs.len());

        (&mut xs[..], &mut idx).sort_unstable_by(|(l, _), (r, _)| l.cmp(r));

        assert_eq!([-2, 0, 3, 4, 5, 7, 9], xs);
        assert_eq!(Some(6), idx.get());
    }

    #[test]
    fn random_sort() {
        #[cfg(not(feature = "extended_random_tests"))]
        const R: usize = 1;
        #[cfg(feature = "extended_random_tests")]
        const R: usize = 128;
        #[cfg(not(feature = "extended_random_tests"))]
        const N: usize = 256;
        #[cfg(feature = "extended_random_tests")]
        const N: usize = 4096;

        let mut rng = rand::thread_rng();

        let mut u16s = [0u16; N];

        for _ in 0..R {
            rng.fill(&mut u16s[..]);

            let idx_to_track = rng.gen_range(0..N);
            let tracked_value = u16s[idx_to_track];

            let mut track_index = TrackIndex::new(idx_to_track, N);

            (&mut u16s[..], &mut track_index).sort_unstable_by(|(a, _), (b, _)| a.cmp(b));

            let idx = track_index.get().unwrap();
            assert_eq!(tracked_value, u16s[idx]);
        }
    }
}
