# etg-prob

Probabilistic ETG (P-ETG) layered over etg-core.

Highlights
- EventDist: closure-backed event distribution for quick sampling.
- SeededEventDist: reproducible distribution using StdRng and a seed.
- interval_sample: draw a pair of events and compute s² via the core metric.
- causal_prob: Monte-Carlo estimator using etg-core's causally_allows.
- causal_prob_with_ci: estimator with Wald-style confidence interval.
- causal_prob_adaptive: adaptive sampling to meet a target CI half-width.
- empirical_s2_invariance: empirical mean s² delta under a fixed boost (~0).
- empirical_s2_delta_stats: Welford mean/variance of s² deltas under boost.

Crate relationships
- Depends on etg-core for types, metric, s², boost, and causal predicate.
- RNG and probabilistic utilities are isolated here (rand dependency).
- No changes to etg-core are required to use P-ETG.

Quick start

Add to workspace members if not already present, then in code:

```rust
use etg_core::{Event, Euclid1D};
use etg_prob::{EventDist, causal_prob};

fn main() {
    let geom = Euclid1D;
    let c = 1.0;

    // E1: deterministic at (0,0)
    let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });

    // E2: l uniform in [-5,5], t peaked around 2 ± 1
    let mut rng = rand::thread_rng();
    let mut e2 = EventDist::new(move || {
        let l = rng.gen_range(-5.0..5.0);
        let t = 2.0 + rng.gen_range(-1.0..1.0);
        Event { l, t }
    });

    // Estimate P(E1 → E2)
    let p = causal_prob(&geom, c, &mut e1, &mut e2, 50_000);
    println!("Estimated causal probability: {p}");
}
```

Reproducible CI-friendly estimates with CIs

```rust
use etg_core::{Event, Euclid1D};
use etg_prob::{EventDist, SeededEventDist, causal_prob_with_ci};
use rand::rngs::StdRng;

fn main() {
    let geom = Euclid1D;
    let c = 1.0;

    let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });

    // E2: reproducible sampler using a fixed seed
    let mut e2 = SeededEventDist::new_seeded(42, |rng: &mut StdRng| {
        let t = if rng.gen_bool(0.5) { 3.0 } else { 1.0 };
        Event { l: 2.0_f64, t }
    });

    // 95% Wald CI (z ≈ 1.96)
    let (p, lo, hi) = causal_prob_with_ci(&geom, c, &mut e1, &mut e2, 20_000, 1.96);
    println!("p={p}, 95% CI=({lo},{hi})");
}
```

Adaptive Monte-Carlo

```rust
use etg_core::{Event, Euclid1D};
use etg_prob::{EventDist, causal_prob_adaptive};

fn main() {
    let geom = Euclid1D;
    let c = 1.0;

    let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });
    let mut e2 = EventDist::new(|| Event { l: 2.0_f64, t: 3.0 }); // always causal at c=1

    // Target half-width eps=1e-3 with z=1.96, cap at 100k samples
    let (p, n) = causal_prob_adaptive(&geom, c, &mut e1, &mut e2, 100_000, 1e-3, 1.96);
    println!("p={p} after n={n}");
}
```

Invariance utilities

```rust
use etg_core::{Event, Euclid1D};
use etg_prob::{EventDist, empirical_s2_invariance, empirical_s2_delta_stats};

fn main() {
    let geom = Euclid1D;
    let c = 1.0;
    let v = 0.6;

    let mut rng1 = rand::thread_rng();
    let mut rng2 = rand::thread_rng();

    let mut e1 = EventDist::new(move || {
        let l = rng1.gen_range(-0.5..0.5);
        let t = rng1.gen_range(-0.5..0.5);
        Event { l, t }
    });
    let mut e2 = EventDist::new(move || {
        let l = rng2.gen_range(-5.0..5.0);
        let t = rng2.gen_range(-5.0..5.0);
        Event { l, t }
    });

    // Mean s² delta ~ 0
    let mean = empirical_s2_invariance(&geom, c, v, &mut e1, &mut e2, 50_000);
    println!("mean s² delta ≈ {mean}");

    // Mean/variance of s² deltas via Welford
    let (m, var) = empirical_s2_delta_stats(&geom, c, v, &mut e1, &mut e2, 50_000);
    println!("mean={m}, var={var}");
}
```

Benchmarks
- Criterion benches included in `benches/causal.rs`.
- Typical invocation:
  - `cargo bench -p etg-prob` (do not run in CI unless desired).

Testing
- Unit tests: `tests/prob.rs`, `tests/estimator.rs`.
- Property tests (proptest): `tests/property.rs` cover numeric and distributional invariance and geometry scaling.
- Seeded samplers ensure reproducibility in CI.

Notes
- Confidence intervals use the simple Wald interval; for near-0/1 probabilities or small n, consider Wilson/Agresti–Coull if needed.