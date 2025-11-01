// Allow doc-style comments in proptest blocks once (avoid duplicate attributes)
#![allow(unused_doc_comments)]
use etg_core::{Scalar, s2, boost};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use proptest::prelude::*;

/// Simple quantile helper: nearest-rank on sorted data.
fn quantile(mut xs: Vec<Scalar>, q: Scalar) -> Scalar {
    assert!((0.0..=1.0).contains(&q));
    xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = xs.len();
    if n == 0 { return f64::NAN; }
    let idx = ((n - 1) as Scalar * q).round() as usize;
    xs[idx]
}

/// Sample s^2 values before/after a boost from random (dt, dx) draws.
fn sample_s2s(c: Scalar, v: Scalar, seed: u64, n: usize) -> (Vec<Scalar>, Vec<Scalar>) {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut pre = Vec::with_capacity(n);
    let mut post = Vec::with_capacity(n);
    for _ in 0..n {
        let t1 = rng.gen_range(-5.0_f64..5.0_f64);
        let t2 = rng.gen_range(-5.0_f64..5.0_f64);
        let l1 = rng.gen_range(-5.0_f64..5.0_f64);
        let l2 = rng.gen_range(-5.0_f64..5.0_f64);

        let dt = t2 - t1;
        let dx = (l2 - l1).abs();
        let (dtp, dxp) = boost(c, v, dt, dx);

        let s = s2(c, dt, dx);
        let sp = s2(c, dtp, dxp);
        pre.push(s);
        post.push(sp);
    }
    (pre, post)
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 32, .. ProptestConfig::default()
    })]

    /// Numeric invariance: s^2(c, dt, dx) == s^2(c, dt', dx') for 1D boosts with |v| < c.
    #[test]
    fn boost_preserves_s2_random(
        l1 in -5.0f64..5.0, l2 in -5.0f64..5.0,
        t1 in -5.0f64..5.0, t2 in -5.0f64..5.0,
        v in -0.9f64..0.9f64
    ) {
        let c = 1.0;
        let dt = t2 - t1;
        let dx = (l2 - l1).abs();
        let (dtp, dxp) = boost(c, v, dt, dx);
        let d = s2(c, dt, dx);
        let dp = s2(c, dtp, dxp);
        prop_assert!((d - dp).abs() < 1e-9, "s2 invariance broken: d={d}, dp={dp}");
    }

    /// Distributional invariance (quantiles): since equality holds pointwise, sampled quantiles match.
    #[test]
    fn boost_preserves_s2_quantiles(seed in any::<u64>(), v in -0.9f64..0.9f64) {
        let c = 1.0;
        let n = 1024;
        let (pre, post) = sample_s2s(c, v, seed, n);

        let qs = [0.1, 0.5, 0.9];
        for &q in &qs {
            let a = quantile(pre.clone(), q);
            let b = quantile(post.clone(), q);
            prop_assert!((a - b).abs() < 1e-9, "quantile mismatch at q={q}: {a} vs {b}");
        }
    }
}

/// Local test-only geometry: scaled 1D distance.
mod scaled_geom {
    use etg_core::{MetricSpace, Scalar};

    pub struct Scaled1D {
        pub s: Scalar,
    }

    impl MetricSpace<f64> for Scaled1D {
        #[inline]
        fn dist(&self, a: &f64, b: &f64) -> Scalar {
            self.s * (a - b).abs()
        }
    }
}

use etg_core::Event;
use etg_prob::{EventDist, empirical_s2_invariance};
use scaled_geom::Scaled1D;

/// Property test: empirical mean delta of s^2 under boost is ~0 across scaled geometries.
proptest! {
    #![proptest_config(ProptestConfig {
        cases: 16, .. ProptestConfig::default()
    })]

    #[test]
    fn empirical_mean_delta_zero_across_scaled_geoms(seed1 in any::<u64>(), seed2 in any::<u64>(), scale in 0.1f64..3.0f64, v in -0.9f64..0.9f64) {
        let geom = Scaled1D { s: scale };
        let c = 1.0;

        let mut rng1 = StdRng::seed_from_u64(seed1);
        let mut rng2 = StdRng::seed_from_u64(seed2);

        // E1 and E2 random events with reproducible seeds
        let mut e1 = EventDist::new(move || {
            let l = rng1.gen_range(-5.0_f64..5.0_f64);
            let t = rng1.gen_range(-5.0_f64..5.0_f64);
            Event { l, t }
        });
        let mut e2 = EventDist::new(move || {
            let l = rng2.gen_range(-5.0_f64..5.0_f64);
            let t = rng2.gen_range(-5.0_f64..5.0_f64);
            Event { l, t }
        });

        let mean = empirical_s2_invariance(&geom, c, v, &mut e1, &mut e2, 2_000);
        prop_assert!(mean.abs() < 1e-8, "mean delta too large: {mean}");
    }
}