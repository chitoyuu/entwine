# entwine

This crate provides the `Entwine` trait that provides a generic interface of slice-like behavior, allowing multiple slices to be operated on at the same time.

Note that this is an experiment, and as it is right now there is no evidence of a performance advantage over more naive approaches. Unless you *have* to do the manipulations in-place, it's probably not a good idea to use this.

## Examples

### Sorting multiple slices at once

```rust
use entwine::Entwine;

let mut a = [6, -3, 2, 7, 0, -42];
let mut b = [1, 2, 3, 4, 5];
let mut c = ["a", "b", "c", "d", "e", "f", "g", "h"];

// Sort all three slices at once by comparing the elements in the first.
//
// `Entwine` handles slices of different lengths by exposing only the range
// shared by all input slices.
(&mut a[..], &mut b[..], &mut c[..])
    .sort_unstable_by(|(l, _, _), (r, _, _)| l.cmp(r));

// Elements in `b` and `c` are sorted along with elements in `a`.
assert_eq!([-3, 0, 2, 6, 7, -42], a);
assert_eq!([2, 5, 3, 1, 4], b);
assert_eq!(["b", "e", "c", "a", "d", "f", "g", "h"], c);
```

### Tracking the index of an element across sorts

```rust
use entwine::Entwine;
use entwine::index::TrackIndex;

let mut xs = [5, 7, -2, 4, 9, 0, 3];

// This creates an imaginary slice tracking the index of "9", that can be
// entwined with real ones.
let mut idx = TrackIndex::new(4, xs.len());

(&mut xs[..], &mut idx).sort_unstable_by(|(l, _), (r, _)| l.cmp(r));

// "9" is now moved to the last place
assert_eq!([-2, 0, 3, 4, 5, 7, 9], xs);
assert_eq!(Some(6), idx.get());
```

## Performance

Unfortunately, it turned out that when dealing with primitive `Copy` types, the performance is around 0.5x of the naive approach of allocating a temporary vector, even with LTO. This makes sense in hindsight, since pointers become much wider and harder to deal with when multiples of them are packed together.

The situation may change, though, with non-`Copy` or even non-`Clone` types, when the manipulation have to be performed in-place. Allocating an index vector, sorting, and then swapping elements around according to the indices might not be as well-optimizable for the computer as primitive data, but any conclusions remain to be seen for now.

The benchmark can be run with `cargo bench --features=nightly`.

## Feature flags

- `nightly` - Adds `feature(generic_associated_types)` to the top of the crate, which would allow the crate to compile on a nightly compiler. **Required** as of Nov. 2021.
- `std` - **Enabled by default.** Enables features that require the full standard library. Currently does nothing.

## License

Dual-licensed under Apache 2.0 and MIT terms.

This crate contains substantial amounts of code adapted from the standard library of Rust. For full authorship information, see the version control history of <https://github.com/rust-lang/rust> or <https://thanks.rust-lang.org>