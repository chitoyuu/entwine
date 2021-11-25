#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(generic_associated_types))]
#![doc = include_str!("../README.md")]

use core::cmp::Ordering;

use raw::{ElementCtor, EntwineCore, PtrMut, RefMut};

pub mod index;
pub mod raw;

mod slice_impl;
mod sort;
mod zip_impl;

/// Type alias for the analogous type to `&T` relative to `[T]`.
pub type RefT<'a, E> = <<E as EntwineCore>::ElementCtor as ElementCtor>::Ref<'a>;
/// Type alias for the analogous type to `&mut T` relative to `[T]`.
pub type RefMutT<'a, E> = <<E as EntwineCore>::ElementCtor as ElementCtor>::RefMut<'a>;
/// Type alias for the analogous type to `*const T` relative to `[T]`.
pub type PtrT<E> = <<E as EntwineCore>::ElementCtor as ElementCtor>::Ptr;
/// Type alias for the analogous type to `*mut T` relative to `[T]`.
pub type PtrMutT<E> = <<E as EntwineCore>::ElementCtor as ElementCtor>::PtrMut;

/// Trait for generic slice-like behavior.
///
/// See crate-level docs for examples.
pub trait Entwine: EntwineCore {
    /// Returns a reference to an element or `None` if the
    /// index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// let v = [10, 40, 30];
    /// assert_eq!(Some(&40), v.get(1));
    /// assert_eq!(None, v.get(3));
    /// assert_eq!(None, v.get(0..4));
    /// ```
    fn get(&self, n: usize) -> Option<RefT<'_, Self>> {
        (n < self.len()).then(|| unsafe { self.get_unchecked(n) })
    }

    /// Returns a mutable reference to an element or `None` if the
    /// index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = &mut [0, 1, 2];
    ///
    /// if let Some(elem) = x.get_mut(1) {
    ///     *elem = 42;
    /// }
    /// assert_eq!(x, &[0, 42, 2]);
    /// ```
    fn get_mut(&mut self, n: usize) -> Option<RefMutT<'_, Self>> {
        (n < self.len()).then(|| unsafe { self.get_unchecked_mut(n) })
    }

    /// Returns an unsafe mutable pointer to the slice's buffer.
    ///
    /// The caller must ensure that the slice outlives the pointer this
    /// function returns, or else it will end up pointing to garbage.
    ///
    /// Modifying the container referenced by this slice may cause its buffer
    /// to be reallocated, which would also make any pointers to it invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = &mut [1, 2, 4];
    /// let x_ptr = x.as_mut_ptr();
    ///
    /// unsafe {
    ///     for i in 0..x.len() {
    ///         *x_ptr.add(i) += 2;
    ///     }
    /// }
    /// assert_eq!(x, &[3, 4, 6]);
    /// ```
    fn as_mut_ptr(&mut self) -> PtrMutT<Self> {
        unsafe { self.get_unchecked_mut(0).to_mut_ptr() }
    }

    /// Swaps two elements in the slice.
    ///
    /// # Arguments
    ///
    /// * a - The index of the first element
    /// * b - The index of the second element
    ///
    /// # Panics
    ///
    /// Panics if `a` or `b` are out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = ["a", "b", "c", "d"];
    /// v.swap(1, 3);
    /// assert!(v == ["a", "d", "c", "b"]);
    /// ```
    fn swap(&mut self, a: usize, b: usize) {
        let len = self.len();
        assert!(a < len && b < len);

        unsafe {
            let pa = self.get_unchecked_mut(a).to_mut_ptr();
            let pb = self.get_unchecked_mut(b).to_mut_ptr();
            PtrMut::swap(&pa, &pb);
        }
    }

    /// Sorts the slice, but might not preserve the order of equal elements.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place
    /// (i.e., does not allocate), and *O*(*n* \* log(*n*)) worst-case.
    ///
    /// # Current implementation
    ///
    /// The current algorithm is based on [pattern-defeating quicksort][pdqsort] by Orson Peters,
    /// which combines the fast average case of randomized quicksort with the fast worst case of
    /// heapsort, while achieving linear time on slices with certain patterns. It uses some
    /// randomization to avoid degenerate cases, but with a fixed seed to always provide
    /// deterministic behavior.
    ///
    /// It is typically faster than stable sorting, except in a few special cases, e.g., when the
    /// slice consists of several concatenated sorted sequences.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = [-5, 4, 1, -3, 2];
    ///
    /// v.sort_unstable();
    /// assert!(v == [-5, -3, 1, 2, 4]);
    /// ```
    ///
    /// [pdqsort]: https://github.com/orlp/pdqsort
    fn sort_unstable(&mut self)
    where
        for<'a, 'b> RefT<'a, Self>: PartialOrd<RefT<'b, Self>>,
    {
        sort::quicksort(self, |a, b| a.lt(b));
    }

    /// Sorts the slice with a comparator function, but might not preserve the order of equal
    /// elements.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place
    /// (i.e., does not allocate), and *O*(*n* \* log(*n*)) worst-case.
    ///
    /// The comparator function must define a total ordering for the elements in the slice. If
    /// the ordering is not total, the order of the elements is unspecified. An order is a
    /// total order if it is (for all `a`, `b` and `c`):
    ///
    /// * total and antisymmetric: exactly one of `a < b`, `a == b` or `a > b` is true, and
    /// * transitive, `a < b` and `b < c` implies `a < c`. The same must hold for both `==` and `>`.
    ///
    /// For example, while [`f64`] doesn't implement [`Ord`] because `NaN != NaN`, we can use
    /// `partial_cmp` as our sort function when we know the slice doesn't contain a `NaN`.
    ///
    /// ```
    /// let mut floats = [5f64, 4.0, 1.0, 3.0, 2.0];
    /// floats.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
    /// assert_eq!(floats, [1.0, 2.0, 3.0, 4.0, 5.0]);
    /// ```
    ///
    /// # Current implementation
    ///
    /// The current algorithm is based on [pattern-defeating quicksort][pdqsort] by Orson Peters,
    /// which combines the fast average case of randomized quicksort with the fast worst case of
    /// heapsort, while achieving linear time on slices with certain patterns. It uses some
    /// randomization to avoid degenerate cases, but with a fixed seed to always provide
    /// deterministic behavior.
    ///
    /// It is typically faster than stable sorting, except in a few special cases, e.g., when the
    /// slice consists of several concatenated sorted sequences.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = [5, 4, 1, 3, 2];
    /// v.sort_unstable_by(|a, b| a.cmp(b));
    /// assert!(v == [1, 2, 3, 4, 5]);
    ///
    /// // reverse sorting
    /// v.sort_unstable_by(|a, b| b.cmp(a));
    /// assert!(v == [5, 4, 3, 2, 1]);
    /// ```
    ///
    /// [pdqsort]: https://github.com/orlp/pdqsort
    fn sort_unstable_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&RefT<'_, Self>, &RefT<'_, Self>) -> Ordering,
    {
        sort::quicksort(self, |a, b| compare(a, b) == Ordering::Less);
    }

    /// Sorts the slice with a key extraction function, but might not preserve the order of equal
    /// elements.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place
    /// (i.e., does not allocate), and *O*(m \* *n* \* log(*n*)) worst-case, where the key function is
    /// *O*(*m*).
    ///
    /// # Current implementation
    ///
    /// The current algorithm is based on [pattern-defeating quicksort][pdqsort] by Orson Peters,
    /// which combines the fast average case of randomized quicksort with the fast worst case of
    /// heapsort, while achieving linear time on slices with certain patterns. It uses some
    /// randomization to avoid degenerate cases, but with a fixed seed to always provide
    /// deterministic behavior.
    ///
    /// Due to its key calling strategy, [`sort_unstable_by_key`](#method.sort_unstable_by_key)
    /// is likely to be slower than [`sort_by_cached_key`](#method.sort_by_cached_key) in
    /// cases where the key function is expensive.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = [-5i32, 4, 1, -3, 2];
    ///
    /// v.sort_unstable_by_key(|k| k.abs());
    /// assert!(v == [1, 2, -3, 4, -5]);
    /// ```
    ///
    /// [pdqsort]: https://github.com/orlp/pdqsort
    fn sort_unstable_by_key<K, F>(&mut self, mut f: F)
    where
        F: FnMut(&RefT<'_, Self>) -> K,
        K: Ord,
    {
        sort::quicksort(self, |a, b| f(a).lt(&f(b)));
    }
}

impl<E: EntwineCore + ?Sized> Entwine for E {}
