#![feature(is_sorted)]

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::Rng;

fn bench_naive<const N: usize>(c: &mut Criterion) {
    let name = format!("naive sort of {}x 4-tuples", N);

    c.bench_function(&name, |b| {
        let mut rng = rand::thread_rng();

        let mut u32s = [0u32; N];
        rng.fill(u32s.as_mut());

        let mut u8s = [0u8; N];
        rng.fill(u8s.as_mut());

        let mut bools = [false; N];
        rng.fill(bools.as_mut());

        let mut i16s = [0i16; N];
        rng.fill(i16s.as_mut());

        b.iter(|| {
            let mut tuples = Vec::with_capacity(N);

            tuples.extend(
                u32s.into_iter()
                    .zip(u8s)
                    .zip(bools)
                    .zip(i16s)
                    .map(|(((a, b), c), d)| (a, b, c, d)),
            );

            tuples.sort_unstable_by(|(l, _, _, _), (r, _, _, _)| l.cmp(r));

            let mut u32s = [0u32; N];
            let mut u8s = [0u8; N];
            let mut bools = [false; N];
            let mut i16s = [0i16; N];

            for (n, (a, b, c, d)) in tuples.into_iter().enumerate() {
                u32s[n] = a;
                u8s[n] = b;
                bools[n] = c;
                i16s[n] = d;
            }

            black_box(u32s[N / 2]);
        })
    });
}

fn bench_entwined<const N: usize>(c: &mut Criterion) {
    let name = format!("entwined sort of {}x 4-tuples", N);

    c.bench_function(&name, |b| {
        let mut rng = rand::thread_rng();

        let mut u32s = [0u32; N];
        rng.fill(u32s.as_mut());

        let mut u8s = [0u8; N];
        rng.fill(u8s.as_mut());

        let mut bools = [false; N];
        rng.fill(bools.as_mut());

        let mut i16s = [0i16; N];
        rng.fill(i16s.as_mut());

        b.iter(|| {
            use entwine::Entwine;

            let mut u32s = u32s;
            let mut u8s = u8s;
            let mut bools = bools;
            let mut i16s = i16s;

            (&mut u32s[..], &mut u8s[..], &mut bools[..], &mut i16s[..])
                .sort_unstable_by(|(l, _, _, _), (r, _, _, _)| l.cmp(r));

            black_box(u32s[N / 2]);
        })
    });
}

fn criterion_benchmark(c: &mut Criterion) {
    bench_naive::<64>(c);
    bench_naive::<256>(c);
    bench_naive::<1024>(c);
    bench_naive::<4096>(c);
    bench_naive::<65536>(c);

    bench_entwined::<64>(c);
    bench_entwined::<256>(c);
    bench_entwined::<1024>(c);
    bench_entwined::<4096>(c);
    bench_entwined::<65536>(c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
