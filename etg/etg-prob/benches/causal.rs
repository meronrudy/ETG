use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput, black_box};
use etg_core::{Event, Euclid1D, boost};
use etg_prob::{EventDist, causal_prob};
use rand::Rng;

fn bench_causal_prob(c: &mut Criterion) {
    let geom = Euclid1D;
    let c0 = 1.0;
    let mut group = c.benchmark_group("causal_prob");
    for &n in &[1_000usize, 10_000, 100_000] {
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            let mut rng = rand::thread_rng();
            let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });
            let mut e2 = EventDist::new(move || {
                let l = rng.gen_range(-5.0..5.0);
                let t = 2.0 + rng.gen_range(-1.0..1.0);
                Event { l, t }
            });
            b.iter(|| {
                let p = causal_prob(&geom, c0, &mut e1, &mut e2, n);
                black_box(p);
            })
        });
    }
    group.finish();
}

fn bench_boost(c: &mut Criterion) {
    let c0 = 1.0;
    let v = 0.6;
    let mut rng = rand::thread_rng();
    c.bench_function("boost_1e6", |b| {
        b.iter(|| {
            let mut acc = 0.0;
            for _ in 0..1_000 {
                let dt = rng.gen_range(-5.0..5.0);
                let dx = rng.gen_range(0.0..5.0);
                let (dtp, dxp) = boost(c0, v, dt, dx);
                acc += dtp + dxp;
            }
            black_box(acc);
        })
    });
}

criterion_group!(benches, bench_causal_prob, bench_boost);
criterion_main!(benches);