use etg_core::{Event, Euclid1D};
use etg_prob::{EventDist, SeededEventDist, causal_prob_with_ci, causal_prob_adaptive};
use rand::rngs::StdRng;
use rand::Rng;

#[test]
fn ci_for_always_causal_is_degenerate_and_centered() {
    let geom = Euclid1D;
    let c = 1.0;

    // Always causal: dx=2, dt=3
    let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });
    let mut e2 = EventDist::new(|| Event { l: 2.0_f64, t: 3.0 });

    let (p, lo, hi) = causal_prob_with_ci(&geom, c, &mut e1, &mut e2, 5_000, 1.96);
    assert!((p - 1.0).abs() < 1e-12, "p not 1: {p}");
    assert!((hi - lo).abs() < 1e-12, "CI not degenerate: [{lo},{hi}]");
    assert!(lo <= p && p <= hi);
}

#[test]
fn ci_half_width_reasonable_for_half_causal() {
    let geom = Euclid1D;
    let c = 1.0;

    let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });

    // Half causal: t in {1,3} with equal probability at fixed l=2
    let mut e2 = SeededEventDist::new_seeded(42, |rng: &mut StdRng| {
        let t = if rng.gen_bool(0.5) { 3.0 } else { 1.0 };
        Event { l: 2.0_f64, t }
    });

    let (p, lo, hi) = causal_prob_with_ci(&geom, c, &mut e1, &mut e2, 20_000, 1.96);
    let width = hi - lo;
    assert!((p - 0.5).abs() < 0.03, "p far from 0.5: {p}");
    assert!(width < 0.02, "CI too wide: width={width}, lo={lo}, hi={hi}");
    assert!(lo <= p && p <= hi);
}

#[test]
fn adaptive_stops_quickly_on_perfectly_causal() {
    let geom = Euclid1D;
    let c = 1.0;

    let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });
    let mut e2 = EventDist::new(|| Event { l: 2.0_f64, t: 3.0 }); // always causal

    // Tight tolerance; should stop near warmup size since p*(1-p)=0
    let (p, n) = causal_prob_adaptive(&geom, c, &mut e1, &mut e2, 10_000, 1e-3, 1.96);
    assert!(p > 0.999999, "p not ~1: {p}");
    assert!(n <= 200, "adaptive did not stop quickly, n={n}");
}

#[test]
fn seeded_event_dist_is_reproducible() {
    let mut a = SeededEventDist::new_seeded(123, |rng: &mut StdRng| {
        let t = if rng.gen_bool(0.5) { 3.0 } else { 1.0 };
        Event { l: 2.0_f64, t }
    });
    let mut b = SeededEventDist::new_seeded(123, |rng: &mut StdRng| {
        let t = if rng.gen_bool(0.5) { 3.0 } else { 1.0 };
        Event { l: 2.0_f64, t }
    });

    for _ in 0..200 {
        let ea = a.sample();
        let eb = b.sample();
        assert_eq!(ea.t, eb.t, "seeded streams diverged");
        assert_eq!(ea.l, eb.l);
    }
}
// Added Euclidean validation tests for causal_prob_adaptive()
// See: [Rust.causal_prob_adaptive()](etg/etg-prob/src/lib.rs:220)

#[test]
fn test_adaptive_prob_strictly_causal_euclid() {
    // Deterministic strictly causal: dt=3, dx=2, c=1 -> causal
    let geom = Euclid1D;
    let c = 1.0;

    let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });
    let mut e2 = EventDist::new(|| Event { l: 2.0_f64, t: 3.0 });

    let (p, n) = causal_prob_adaptive(&geom, c, &mut e1, &mut e2, 50_000, 5e-3, 1.96);
    assert!(p > 0.99, "p too low for strictly causal case: {p}");
    assert!(n <= 5_000, "adaptive did not stop early enough, n={n}");
}

#[test]
fn test_adaptive_prob_strictly_spacelike_euclid() {
    // Deterministic strictly spacelike: dt=1, dx=3, c=1 -> not causal
    let geom = Euclid1D;
    let c = 1.0;

    let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });
    let mut e2 = EventDist::new(|| Event { l: 3.0_f64, t: 1.0 });

    let (p, n) = causal_prob_adaptive(&geom, c, &mut e1, &mut e2, 50_000, 5e-3, 1.96);
    assert!(p < 0.01, "p too high for strictly spacelike case: {p}");
    assert!(n <= 5_000, "adaptive did not stop early enough, n={n}");
}

#[test]
fn test_adaptive_prob_null_boundary_euclid() {
    // Deterministic null boundary: dt=dx/c, here dt=2, dx=2, c=1 -> allowed by dt >= dx/c
    let geom = Euclid1D;
    let c = 1.0;

    let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });
    let mut e2 = EventDist::new(|| Event { l: 2.0_f64, t: 2.0 });

    let (p, n) = causal_prob_adaptive(&geom, c, &mut e1, &mut e2, 100_000, 5e-3, 1.96);
    assert!(p > 0.98, "p too low at null boundary: {p}");
    assert!(n <= 10_000, "adaptive did not stop early enough, n={n}");
}