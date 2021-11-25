use core::marker::PhantomData;
use core::mem;
use core::ops::RangeBounds;
use core::ptr;

use crate::raw::{ElementCtor, EntwineCore, Ptr, PtrMut, Ref, RefMut, Value};
use crate::{RefMutT, RefT};

unsafe impl<T> EntwineCore for [T] {
    type ElementCtor = SliceElementCtor<T>;

    type RangeMut<'a>
    where
        Self: 'a,
    = &'a mut [T];

    #[inline]
    fn len(&self) -> usize {
        <[T]>::len(self)
    }

    #[inline]
    fn range_mut<R: RangeBounds<usize>>(&mut self, range: R) -> Option<&mut Self> {
        let start = range.start_bound().cloned();
        let end = range.end_bound().cloned();
        self.get_mut((start, end))
    }

    #[inline]
    fn split_at_mut(&mut self, mid: usize) -> (&mut Self, &mut Self) {
        <[T]>::split_at_mut(self, mid)
    }

    #[inline]
    fn reverse(&mut self) {
        <[T]>::reverse(self)
    }

    #[inline]
    unsafe fn get_unchecked(&self, idx: usize) -> RefT<'_, Self> {
        <[T]>::get_unchecked(self, idx)
    }

    #[inline]
    unsafe fn get_unchecked_mut(&mut self, idx: usize) -> RefMutT<'_, Self> {
        <[T]>::get_unchecked_mut(self, idx)
    }
}

pub struct SliceElementCtor<T> {
    _marker: PhantomData<T>,
}

impl<T> ElementCtor for SliceElementCtor<T> {
    type Value = T;

    type Ref<'a>
    where
        Self: 'a,
    = &'a T;

    type RefMut<'a>
    where
        Self: 'a,
    = &'a mut T;

    type Ptr = *const T;
    type PtrMut = *mut T;
}

unsafe impl<T> Value<SliceElementCtor<T>> for T {
    #[inline]
    fn is_zero_sized() -> bool {
        mem::size_of::<T>() == 0
    }

    #[inline]
    fn as_ref(&self) -> &'_ T {
        self
    }

    #[inline]
    fn as_mut(&mut self) -> &'_ mut T {
        self
    }
}

unsafe impl<'a, T> Ref<'a, SliceElementCtor<T>> for &'a T {
    #[inline]
    fn to_ptr(&self) -> *const T {
        *self
    }

    #[inline]
    fn reborrow<'r>(self) -> &'r T
    where
        'a: 'r,
    {
        self
    }
}

unsafe impl<'a, T> RefMut<'a, SliceElementCtor<T>> for &'a mut T {
    #[inline]
    fn to_ref(&self) -> &'_ T {
        self
    }

    #[inline]
    fn to_mut_ptr(&mut self) -> *mut T {
        *self
    }

    #[inline]
    fn reborrow_mut<'r>(self) -> &'r mut T
    where
        'a: 'r,
    {
        self
    }
}

unsafe impl<T> Ptr<SliceElementCtor<T>> for *const T {
    #[inline]
    unsafe fn deref<'r>(&self) -> &'r T {
        &**self
    }

    #[inline]
    unsafe fn read(src: &Self) -> T {
        ptr::read(*src)
    }

    #[inline]
    unsafe fn add(&self, count: usize) -> Self {
        <*const T>::add(*self, count)
    }

    #[inline]
    unsafe fn offset(&self, count: isize) -> Self {
        <*const T>::offset(*self, count)
    }

    #[inline]
    fn width(l: &Self, r: &Self) -> usize {
        assert!(mem::size_of::<T>() > 0);
        (*r as usize - *l as usize) / mem::size_of::<T>()
    }

    #[inline]
    fn null() -> Self {
        ptr::null()
    }
}

unsafe impl<T> PtrMut<SliceElementCtor<T>> for *mut T {
    #[inline]
    unsafe fn deref_mut<'r>(&self) -> &'r mut T {
        &mut **self
    }

    #[inline]
    unsafe fn to_const(&self) -> *const T {
        *self
    }

    #[inline]
    unsafe fn write(dst: &Self, src: T) {
        ptr::write(*dst, src)
    }

    #[inline]
    unsafe fn add(&self, count: usize) -> Self {
        <*mut T>::add(*self, count)
    }

    #[inline]
    unsafe fn offset(&self, count: isize) -> Self {
        <*mut T>::offset(*self, count)
    }

    #[inline]
    fn width(l: &Self, r: &Self) -> usize {
        assert!(mem::size_of::<T>() > 0);
        (*r as usize - *l as usize) / mem::size_of::<T>()
    }

    #[inline]
    unsafe fn copy_nonoverlapping(src: &*const T, dst: &Self, n: usize) {
        ptr::copy_nonoverlapping(*src, *dst, n)
    }

    #[inline]
    fn null_mut() -> Self {
        ptr::null_mut()
    }

    #[inline]
    unsafe fn swap(a: &Self, b: &Self) {
        ptr::swap(*a, *b)
    }
}

#[cfg(test)]
mod tests {
    use crate::Entwine;

    use rand::Rng;

    #[test]
    fn random_sort() {
        #[cfg(not(feature = "extended_random_tests"))]
        const R: usize = 1;
        #[cfg(feature = "extended_random_tests")]
        const R: usize = 128;
        #[cfg(not(feature = "extended_random_tests"))]
        const N: usize = 1024;
        #[cfg(feature = "extended_random_tests")]
        const N: usize = 4096;

        let mut rng = rand::thread_rng();

        let mut u16s = [0u16; N];

        for _ in 0..R {
            rng.fill(u16s.as_mut());

            (&mut u16s[..],).sort_unstable_by(|a, b| a.cmp(b));

            let mut last = u16s[0];
            for &i in &u16s[1..] {
                if i < last {
                    panic!("slice is not sorted: {:?}", &u16s);
                }
                last = i;
            }
        }
    }
}
