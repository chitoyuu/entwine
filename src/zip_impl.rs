use core::marker::PhantomData;
use core::ops::RangeBounds;

use paste::paste;

use crate::raw::{ElementCtor, EntwineCore, Ptr, PtrMut, Ref, RefMut, Value};
use crate::{RefMutT, RefT};

pub struct ZipElementCtor<T> {
    _marker: PhantomData<T>,
}

macro_rules! impl_tuple {
    (
        $($t:ident),* $(,)?
    ) => {
        unsafe impl<'r, $($t,)*> EntwineCore for ($($t,)*)
        where
            $($t: EntwineCore,)*
        {
            type ElementCtor = ZipElementCtor<($($t::ElementCtor,)*)>;
            type RangeMut<'a> where Self:'a = ($($t::RangeMut<'a>,)*);

            fn len(&self) -> usize {
                let ($($t,)*) = self;
                [$($t.len(),)*].into_iter().min().unwrap_or(0)
            }

            fn is_empty(&self) -> bool {
                let ($($t,)*) = self;
                $($t.is_empty())||*
            }

            fn range_mut<R: RangeBounds<usize>>(&mut self, range: R) -> Option<Self::RangeMut<'_>> {
                let start = range.start_bound().cloned();
                let end = range.end_bound().cloned();

                let ($($t,)*) = self;
                $(
                    let $t = $t.range_mut((start, end))?;
                )*
                Some(($($t,)*))
            }

            fn split_at_mut(&mut self, mid: usize) -> (Self::RangeMut<'_>, Self::RangeMut<'_>) {
                let ($($t,)*) = self;
                $(
                    let $t = $t.split_at_mut(mid);
                )*
                let left = ($($t.0,)*);
                let right = ($($t.1,)*);
                (left, right)
            }

            fn reverse(&mut self) {
                let len = self.len();
                let ($($t,)*) = self;
                $(
                    $t.range_mut(..len).unwrap().reverse();
                )*
            }

            unsafe fn get_unchecked(&self, idx: usize) -> RefT<'_, Self> {
                let ($($t,)*) = self;
                ($($t.get_unchecked(idx),)*)
            }

            unsafe fn get_unchecked_mut(&mut self, idx: usize) -> RefMutT<'_, Self> {
                let ($($t,)*) = self;
                ($($t.get_unchecked_mut(idx),)*)
            }
        }

        impl<'r, $($t,)*> ElementCtor for ZipElementCtor<($($t,)*)>
        where
            $($t: ElementCtor,)*
        {
            type Value = ($($t::Value,)*);

            type Ref<'a>
            where
                Self: 'a,
            = ($($t::Ref<'a>,)*);

            type RefMut<'a>
            where
                Self: 'a,
            = ($($t::RefMut<'a>,)*);

            type Ptr = ($($t::Ptr,)*);
            type PtrMut = ($($t::PtrMut,)*);
        }

        unsafe impl<'r, $($t,)*> Value<ZipElementCtor<($($t,)*)>> for ($($t::Value,)*)
        where
            $($t: ElementCtor,)*
        {
            fn is_zero_sized() -> bool {
                $($t::Value::is_zero_sized())&&*
            }

            fn as_ref(&self) -> ($($t::Ref<'_>,)*) {
                let ($($t,)*) = self;
                ($($t.as_ref(),)*)
            }

            fn as_mut(&mut self) -> ($($t::RefMut<'_>,)*) {
                let ($($t,)*) = self;
                ($($t.as_mut(),)*)
            }
        }

        unsafe impl<'a, 'r, $($t,)*> Ref<'a, ZipElementCtor<($($t,)*)>> for ($($t::Ref<'a>,)*)
        where
            $($t: ElementCtor,)*
        {
            fn to_ptr(&self) -> ($($t::Ptr,)*) {
                let ($($t,)*) = self;
                ($($t.to_ptr(),)*)
            }

            fn reborrow<'l>(self) -> ($($t::Ref<'l>,)*) where 'a: 'l {
                let ($($t,)*) = self;
                ($($t.reborrow(),)*)
            }
        }

        unsafe impl<'a, 'r, $($t,)*> RefMut<'a, ZipElementCtor<($($t,)*)>> for ($($t::RefMut<'a>,)*)
        where
            $($t: ElementCtor,)*
        {
            fn to_ref(&self) -> ($($t::Ref<'_>,)*) {
                let ($($t,)*) = self;
                ($($t.to_ref(),)*)
            }

            fn to_mut_ptr(&mut self) -> ($($t::PtrMut,)*) {
                let ($($t,)*) = self;
                ($($t.to_mut_ptr(),)*)
            }

            fn reborrow_mut<'l>(self) -> ($($t::RefMut<'l>,)*) where 'a: 'l {
                let ($($t,)*) = self;
                ($($t.reborrow_mut(),)*)
            }
        }

        unsafe impl<'r, $($t,)*> Ptr<ZipElementCtor<($($t,)*)>> for ($($t::Ptr,)*)
        where
            $($t: ElementCtor,)*
        {
            unsafe fn deref<'l>(&self) -> ($($t::Ref<'l>,)*) {
                let ($($t,)*) = self;
                ($($t.deref(),)*)
            }

            fn null() -> Self {
                ($($t::Ptr::null(),)*)
            }

            unsafe fn read(src: &Self) -> ($($t::Value,)*) {
                let ($($t,)*) = src;
                ($(Ptr::read($t),)*)
            }

            unsafe fn add(&self, count: usize) -> Self {
                let ($($t,)*) = self;
                ($($t.add(count),)*)
            }

            unsafe fn offset(&self, count: isize) -> Self {
                let ($($t,)*) = self;
                ($($t.offset(count),)*)
            }

            fn width(l: &Self, r: &Self) -> usize {
                // SAFETY: Zipped pointers are always in sync
                Ptr::width(&l.0, &r.0)
            }
        }

        unsafe impl<'r, $($t,)*> PtrMut<ZipElementCtor<($($t,)*)>> for ($($t::PtrMut,)*)
        where
            $($t: ElementCtor,)*
        {
            unsafe fn deref_mut<'l>(&self) -> ($($t::RefMut<'l>,)*) {
                let ($($t,)*) = self;
                ($($t.deref_mut(),)*)
            }

            unsafe fn to_const(&self) -> ($($t::Ptr,)*) {
                let ($($t,)*) = self;
                ($($t.to_const(),)*)
            }

            fn null_mut() -> Self {
                ($($t::PtrMut::null_mut(),)*)
            }

            unsafe fn copy_nonoverlapping(src: &($($t::Ptr,)*), dst: &Self, n: usize) {
                paste! {
                    let ($([<src_ $t>],)*) = src;
                    let ($([<dst_ $t>],)*) = dst;
                    $(
                        PtrMut::copy_nonoverlapping([<src_ $t>], [<dst_ $t>], n);
                    )*
                }
            }

            unsafe fn swap(a: &Self, b: &Self) {
                paste! {
                    let ($([<a_ $t>],)*) = a;
                    let ($([<b_ $t>],)*) = b;
                    $(
                        PtrMut::swap([<a_ $t>], [<b_ $t>]);
                    )*
                }
            }

            unsafe fn add(&self, count: usize) -> Self {
                let ($($t,)*) = self;
                ($($t.add(count),)*)
            }

            unsafe fn offset(&self, count: isize) -> Self {
                let ($($t,)*) = self;
                ($($t.offset(count),)*)
            }

            fn width(l: &Self, r: &Self) -> usize {
                // SAFETY: Zipped pointers are always in sync
                PtrMut::width(&l.0, &r.0)
            }

            unsafe fn write(dst: &Self, src: ($($t::Value,)*)) {
                paste! {
                    let ($([<dst_ $t>],)*) = dst;
                    let ($([<src_ $t>],)*) = src;
                    $(
                        PtrMut::write([<dst_ $t>], [<src_ $t>]);
                    )*
                }
            }
        }
    }
}

#[allow(non_snake_case)]
mod impl_tuples {
    use super::*;

    impl_tuple!(A);
    impl_tuple!(A, B);
    impl_tuple!(A, B, C);
    impl_tuple!(A, B, C, D);
    impl_tuple!(A, B, C, D, E);
    impl_tuple!(A, B, C, D, E, F);
    impl_tuple!(A, B, C, D, E, F, G);
    impl_tuple!(A, B, C, D, E, F, G, H);
    impl_tuple!(A, B, C, D, E, F, G, H, I);
    impl_tuple!(A, B, C, D, E, F, G, H, I, J);
    impl_tuple!(A, B, C, D, E, F, G, H, I, J, K);
    impl_tuple!(A, B, C, D, E, F, G, H, I, J, K, L);
}

#[cfg(test)]
mod tests {
    use crate::Entwine;

    #[test]
    fn it_works() {
        let mut a = [6, -3, 2, 7, 0, -42];
        let mut b = [1, 2, 3, 4, 5];
        let mut c = ["a", "b", "c", "d", "e", "f", "g", "h"];

        (&mut a[..], &mut b[..], &mut c[..]).sort_unstable_by(|(l, _, _), (r, _, _)| l.cmp(r));

        assert_eq!([-3, 0, 2, 6, 7, -42], a);
        assert_eq!([2, 5, 3, 1, 4], b);
        assert_eq!(["b", "e", "c", "a", "d", "f", "g", "h"], c);
    }
}
