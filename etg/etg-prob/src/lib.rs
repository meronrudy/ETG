#![doc = r#"P-ETG (v0.2) skeleton: probabilistic hooks layered over etg-core.

- EventDist: a simple distribution over events via a sampler closure.
- IntervalRV: helper to draw s^2 samples from a pair of event distributions.
- causal_prob: Monte-Carlo estimator using etg-core's causally_allows.

Notes:
- Deterministic users depend only on etg-core; etg-prob introduces rand only here.
"#]
use etg_core::{Event, MetricSpace, Scalar, s2, causally_allows, boost};
use rand::Rng;

/// Randomization hook (kept out of core).
pub trait Sampler<T> {
    fn sample(&mut self) -> T;
}

/// A minimal random-variable placeholder backed by a closure.
pub struct RV<T, F: FnMut() -> T> {
    f: F,
    _t: core::marker::PhantomData<T>,
}
impl<T, F: FnMut() -> T> RV<T, F> {
    pub fn new(f: F) -> Self { Self { f, _t: core::marker::PhantomData } }
}
impl<T, F: FnMut() -> T> Sampler<T> for RV<T, F> {
    fn sample(&mut self) -> T { (self.f)() }
}

/// Event distribution placeholder using a sampler closure.
pub struct EventDist<L, F: FnMut() -> Event<L>> {
    f: F,
}
impl<L, F: FnMut() -> Event<L>> EventDist<L, F> {
    pub fn new(f: F) -> Self { Self { f } }
    pub fn sample(&mut self) -> Event<L> { (self.f)() }
}

impl<L, F: FnMut() -> Event<L>> Sampler<Event<L>> for EventDist<L, F> {
    #[inline]
    fn sample(&mut self) -> Event<L> { (self.f)() }
}

/// Interval random variable helper: draws s^2 values from two event distributions.
pub fn interval_sample<L, G, S1, S2>(geom: &G, c: Scalar, e1: &mut S1, e2: &mut S2) -> Scalar
where
    G: MetricSpace<L>,
    S1: Sampler<Event<L>>,
    S2: Sampler<Event<L>>,
{
    let a = e1.sample();
    let b = e2.sample();
    let dt = b.t - a.t;
    let dx = geom.dist(&a.l, &b.l);
    s2(c, dt, dx)
}

/// Monte-Carlo estimator for P(E1 → E2) using etg-core's causally_allows.
pub fn causal_prob<L, G, S1, S2>(geom: &G, c: Scalar, e1: &mut S1, e2: &mut S2, samples: usize) -> Scalar
where
    G: MetricSpace<L>,
    S1: Sampler<Event<L>>,
    S2: Sampler<Event<L>>,
{
    let mut ok = 0usize;
    for _ in 0..samples {
        let a = e1.sample();
        let b = e2.sample();
        if causally_allows(geom, c, &a, &b) {
            ok += 1;
        }
    }
    (ok as Scalar) / (samples as Scalar)
}

/// Distributional invariance check utility:
/// Empirically verify mean s^2 difference before/after a fixed numeric boost is ~0.
pub fn empirical_s2_invariance<L, G, S1, S2>(
    geom: &G,
    c: Scalar,
    v: Scalar,
    e1: &mut S1,
    e2: &mut S2,
    samples: usize,
) -> Scalar
where
    G: MetricSpace<L>,
    S1: Sampler<Event<L>>,
    S2: Sampler<Event<L>>,
{
    let mut acc = 0.0;
    for _ in 0..samples {
        let a = e1.sample();
        let b = e2.sample();
        let dt = b.t - a.t;
        let dx = geom.dist(&a.l, &b.l);
        let (dtp, dxp) = boost(c, v, dt, dx);
        let d = s2(c, dtp, dxp) - s2(c, dt, dx);
        acc += d;
    }
    acc / (samples as Scalar)
}

// --- P-ETG v0.3 extras: seedable RNG, CIs, and adaptive MC ---

use rand::rngs::StdRng;
use rand::SeedableRng;

/// A generic distribution interface that draws using a caller-supplied RNG.
pub trait Distribution<T> {
    fn sample_with<R: Rng>(&mut self, rng: &mut R) -> T;
}

/// Seeded event distribution: owns a reproducible RNG and a generator closure.
///
/// Example (doctest):
/// ```
/// use etg_core::{Event, Euclid1D};
/// use etg_prob::{SeededEventDist, causal_prob_with_ci, EventDist};
/// use rand::rngs::StdRng;
/// use rand::SeedableRng;
/// use rand::Rng;
///
/// let geom = Euclid1D;
/// let c = 1.0;
///
/// // E1 fixed
/// let mut e1 = EventDist::new(|| Event{ l: 0.0_f64, t: 0.0 });
///
/// // E2 random but reproducible: t in {1,3} with equal probability at fixed l
/// let mut e2 = SeededEventDist::new_seeded(42, |rng: &mut StdRng| {
///     let t = if rng.gen_bool(0.5) { 3.0 } else { 1.0 };
///     Event { l: 2.0_f64, t }
/// });
///
/// let (p, lo, hi) = causal_prob_with_ci(&geom, c, &mut e1, &mut e2, 20_000, 1.96);
/// assert!(p >= lo && p <= hi);
/// ```
pub struct SeededEventDist<L, F: FnMut(&mut StdRng) -> Event<L>> {
    rng: StdRng,
    f: F,
}

impl<L, F: FnMut(&mut StdRng) -> Event<L>> SeededEventDist<L, F> {
    pub fn new_seeded(seed: u64, f: F) -> Self {
        Self { rng: StdRng::seed_from_u64(seed), f }
    }
    #[inline]
    pub fn sample(&mut self) -> Event<L> { (self.f)(&mut self.rng) }
}

impl<L, F: FnMut(&mut StdRng) -> Event<L>> Sampler<Event<L>> for SeededEventDist<L, F> {
    #[inline]
    fn sample(&mut self) -> Event<L> { (self.f)(&mut self.rng) }
}

/// Monte-Carlo estimator with Wald-style confidence interval.
///
/// Returns (p_hat, ci_lo, ci_hi) using half-width z * sqrt(p_hat * (1 - p_hat) / n).
///
/// Note: For small-sample or near-boundary cases, consider Wilson/Agresti-Coull.
/// This simple Wald interval is adequate for large n and non-degenerate probabilities.
///
/// Example (doctest):
/// ```
/// use etg_core::{Event, Euclid1D};
/// use etg_prob::{EventDist, causal_prob_with_ci};
///
/// let geom = Euclid1D;
/// let c = 1.0;
/// let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });
/// let mut e2 = EventDist::new(|| Event { l: 0.0_f64, t: 1.0 }); // always causal
///
/// let (p, lo, hi) = causal_prob_with_ci(&geom, c, &mut e1, &mut e2, 5_000, 1.96);
/// assert!(p > 0.98 && lo > 0.95 && hi <= 1.0);
/// ```
pub fn causal_prob_with_ci<L, G, S1, S2>(
    geom: &G,
    c: Scalar,
    e1: &mut S1,
    e2: &mut S2,
    samples: usize,
    z: Scalar,
) -> (Scalar, Scalar, Scalar)
where
    G: MetricSpace<L>,
    S1: Sampler<Event<L>>,
    S2: Sampler<Event<L>>,
{
    let p = causal_prob(geom, c, e1, e2, samples);
    let var = if samples > 1 { p * (1.0 - p) / (samples as Scalar) } else { 0.0 };
    let half = z * var.sqrt();
    let lo = (p - half).max(0.0);
    let hi = (p + half).min(1.0);
    (p, lo, hi)
}

/// Adaptive Monte-Carlo for causal probability with target CI half-width eps.
///
/// - z: z-score (e.g., 1.96 for ~95%)
/// - eps: desired half-width tolerance
/// - max_samples: ceiling to prevent runaway loops
///
/// Returns (p_hat, n_used). If early stopping fails, uses max_samples.
///
/// Example (doctest):
/// ```
/// use etg_core::{Event, Euclid1D};
/// use etg_prob::{EventDist, causal_prob_adaptive};
///
/// let geom = Euclid1D;
/// let c = 1.0;
/// let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });
/// let mut e2 = EventDist::new(|| Event { l: 2.0_f64, t: 3.0 }); // always causal at c=1
///
/// let (p, n) = causal_prob_adaptive(&geom, c, &mut e1, &mut e2, 100_000, 1e-3, 1.96);
/// assert!(p > 0.999);
/// assert!(n >= 100);
/// ```
pub fn causal_prob_adaptive<L, G, S1, S2>(
    geom: &G,
    c: Scalar,
    e1: &mut S1,
    e2: &mut S2,
    max_samples: usize,
    eps: Scalar,
    z: Scalar,
) -> (Scalar, usize)
where
    G: MetricSpace<L>,
    S1: Sampler<Event<L>>,
    S2: Sampler<Event<L>>,
{
    let mut ok = 0usize;
    let mut n = 0usize;

    while n < max_samples {
        n += 1;
        let a = e1.sample();
        let b = e2.sample();
        if causally_allows(geom, c, &a, &b) {
            ok += 1;
        }

        // After a modest warmup, check CI half-width
        if n >= 100 {
            let p = ok as Scalar / n as Scalar;
            let se = (p * (1.0 - p) / (n as Scalar)).sqrt();
            if z * se <= eps && p.is_finite() {
                return (p, n);
            }
        }
    }

    let p = ok as Scalar / n as Scalar;
    (p, n)
}

/// Compute mean and (unbiased) variance of s^2 deltas under a fixed boost using Welford's method.
///
/// Returns (mean_delta, var_delta).
pub fn empirical_s2_delta_stats<L, G, F1, F2>(
    geom: &G,
    c: Scalar,
    v: Scalar,
    e1: &mut EventDist<L, F1>,
    e2: &mut EventDist<L, F2>,
    samples: usize,
) -> (Scalar, Scalar)
where
    G: MetricSpace<L>,
    F1: FnMut() -> Event<L>,
    F2: FnMut() -> Event<L>,
{
    let mut n: usize = 0;
    let mut mean: Scalar = 0.0;
    let mut m2: Scalar = 0.0;

    for _ in 0..samples {
        let a = e1.sample();
        let b = e2.sample();
        let dt = b.t - a.t;
        let dx = geom.dist(&a.l, &b.l);
        let (dtp, dxp) = boost(c, v, dt, dx);
        let d = s2(c, dtp, dxp) - s2(c, dt, dx);

        n += 1;
        let delta = d - mean;
        mean += delta / (n as Scalar);
        let delta2 = d - mean;
        m2 += delta * delta2;
    }

    if n > 1 {
        (mean, m2 / ((n as Scalar) - 1.0))
    } else {
        (mean, 0.0)
    }
}