//! Low-level traits and operations
//!
//! This module contains low-level traits that are generally `unsafe` to implement,
//! upon which the safe [`Entwine`](super::Entwine) interface is built. Users generally
//! do not need to import or implement these traits directly.

#![allow(clippy::missing_safety_doc)]

use core::hash::Hash;
use core::ops::RangeBounds;

use crate::{RefMutT, RefT};

/// Basic slice operations.
pub unsafe trait EntwineCore {
    /// Constructor of types related to elements.
    type ElementCtor: ElementCtor;

    /// Mutable view type into a range.
    type RangeMut<'a>: EntwineCore<ElementCtor = Self::ElementCtor>
    where
        Self: 'a;

    /// Returns the number of elements in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = [1, 2, 3];
    /// assert_eq!(a.len(), 3);
    /// ```
    fn len(&self) -> usize;

    /// Returns `true` if the slice has a length of 0.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = [1, 2, 3];
    /// assert!(!a.is_empty());
    /// ```
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn range_mut<R: RangeBounds<usize>>(&mut self, range: R) -> Option<Self::RangeMut<'_>>;

    /// Splits the slice into a slice of `N`-element arrays,
    /// starting at the beginning of the slice,
    /// and a remainder slice with length strictly less than `N`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(slice_as_chunks)]
    /// let v = &mut [0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// let (chunks, remainder) = v.as_chunks_mut();
    /// remainder[0] = 9;
    /// for chunk in chunks {
    ///     *chunk = [count; 2];
    ///     count += 1;
    /// }
    /// assert_eq!(v, &[1, 1, 2, 2, 9]);
    /// ```
    fn split_at_mut(&mut self, mid: usize) -> (Self::RangeMut<'_>, Self::RangeMut<'_>);

    /// Reverses the order of elements in the slice, in place.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = [1, 2, 3];
    /// v.reverse();
    /// assert!(v == [3, 2, 1]);
    /// ```
    fn reverse(&mut self);

    /// Returns a reference to an element, without doing bounds checking.
    ///
    /// For a safe alternative see [`Entwine::get`].
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used.
    ///
    /// [`Entwine::get`]: crate::Entwine::get
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// let x = &[1, 2, 4];
    ///
    /// unsafe {
    ///     assert_eq!(x.get_unchecked(1), &2);
    /// }
    /// ```
    unsafe fn get_unchecked(&self, idx: usize) -> RefT<'_, Self>;

    /// Returns a mutable reference to an element, without doing bounds checking.
    ///
    /// For a safe alternative see [`Entwine::get_mut`].
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used.
    ///
    /// [`Entwine::get_mut`]: crate::Entwine::get_mut
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// let x = &mut [1, 2, 4];
    ///
    /// unsafe {
    ///     let elem = x.get_unchecked_mut(1);
    ///     *elem = 13;
    /// }
    /// assert_eq!(x, &[1, 13, 4]);
    /// ```
    unsafe fn get_unchecked_mut(&mut self, idx: usize) -> RefMutT<'_, Self>;
}

unsafe impl<'e, E> EntwineCore for &'e mut E
where
    E: EntwineCore + ?Sized,
{
    type ElementCtor = E::ElementCtor;

    type RangeMut<'a>
    where
        Self: 'a,
    = E::RangeMut<'a>;

    fn len(&self) -> usize {
        E::len(self)
    }

    fn range_mut<R: RangeBounds<usize>>(&mut self, range: R) -> Option<Self::RangeMut<'_>> {
        E::range_mut(self, range)
    }

    fn split_at_mut(&mut self, mid: usize) -> (Self::RangeMut<'_>, Self::RangeMut<'_>) {
        E::split_at_mut(self, mid)
    }

    fn reverse(&mut self) {
        E::reverse(self)
    }

    unsafe fn get_unchecked(&self, idx: usize) -> RefT<'_, Self> {
        E::get_unchecked(self, idx)
    }

    unsafe fn get_unchecked_mut(&mut self, idx: usize) -> RefMutT<'_, Self> {
        E::get_unchecked_mut(self, idx)
    }

    fn is_empty(&self) -> bool {
        E::is_empty(self)
    }
}

/// Constructor of types related to elements.
pub trait ElementCtor: Sized {
    type Value: Value<Self>;

    type Ref<'a>: Ref<'a, Self>
    where
        Self: 'a;

    type RefMut<'a>: RefMut<'a, Self>
    where
        Self: 'a;

    type Ptr: Ptr<Self>;
    type PtrMut: PtrMut<Self>;
}

/// Owned element values, like `T`.
pub unsafe trait Value<T: ElementCtor> {
    fn is_zero_sized() -> bool;
    fn as_ref(&self) -> T::Ref<'_>;
    fn as_mut(&mut self) -> T::RefMut<'_>;
}

/// References to elements, like `&T`.
pub unsafe trait Ref<'a, T: ElementCtor>: Clone {
    fn reborrow<'r>(self) -> T::Ref<'r>
    where
        'a: 'r;
    fn to_ptr(&self) -> T::Ptr;
}

/// Mutable references to elements, like `&mut T`.
pub unsafe trait RefMut<'a, T: ElementCtor> {
    fn reborrow_mut<'r>(self) -> T::RefMut<'r>
    where
        'a: 'r;
    fn to_ref(&self) -> T::Ref<'_>;
    fn to_mut_ptr(&mut self) -> T::PtrMut;
}

/// Raw pointers to elements, like `*const T`.
pub unsafe trait Ptr<T: ElementCtor>: Eq + Hash + Clone {
    unsafe fn deref<'r>(&self) -> T::Ref<'r>;

    fn null() -> Self;

    unsafe fn add(&self, count: usize) -> Self;
    unsafe fn offset(&self, count: isize) -> Self;

    // Returns the number of elements between pointers `l` (inclusive) and `r` (exclusive).
    fn width(l: &Self, r: &Self) -> usize;

    unsafe fn read(src: &Self) -> T::Value;
}

/// Raw mutable pointers to elements, like `*mut T`.
pub unsafe trait PtrMut<T: ElementCtor>: Eq + Hash + Clone {
    unsafe fn deref_mut<'r>(&self) -> T::RefMut<'r>;
    unsafe fn to_const(&self) -> T::Ptr;

    fn null_mut() -> Self;

    unsafe fn add(&self, count: usize) -> Self;
    unsafe fn offset(&self, count: isize) -> Self;

    // Returns the number of elements between pointers `l` (inclusive) and `r` (exclusive).
    fn width(l: &Self, r: &Self) -> usize;

    unsafe fn write(dst: &Self, src: T::Value);
    unsafe fn copy_nonoverlapping(src: &T::Ptr, dst: &Self, n: usize);
    unsafe fn swap(a: &Self, b: &Self);
}
