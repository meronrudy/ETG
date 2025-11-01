use etg_core::Event;
use etg_core::Euclid1D;
use etg_prob::*;
use rand::Rng;

/// Discrete case with known probability: half causal, half not.
#[test]
fn mc_causal_prob_discrete_half() {
    let geom = Euclid1D;
    let c = 1.0;

    // E1: deterministic at (l=0, t=0)
    let mut e1 = EventDist::new(|| Event { l: 0.0_f64, t: 0.0 });

    // E2: l = 2.0 always; t = 3.0 (causal) or 1.0 (not) with equal probability
    let mut rng = rand::thread_rng();
    let mut e2 = EventDist::new(move || {
        let t = if rng.gen_bool(0.5) { 3.0 } else { 1.0 };
        Event { l: 2.0_f64, t }
    });

    let p = causal_prob(&geom, c, &mut e1, &mut e2, 50_000);
    assert!((p - 0.5).abs() < 0.03, "estimated p={p}");
}

/// Empirical distributional invariance: mean s^2 delta ~ 0 under a fixed boost.
#[test]
fn empirical_distributional_invariance_mean_s2_zero() {
    let geom = Euclid1D;
    let c = 1.0;
    let v = 0.6; // subluminal

    let mut rng1 = rand::thread_rng();
    let mut rng2 = rand::thread_rng();

    // E1: centered at (0,0) with small jitter
    let mut e1 = EventDist::new(move || {
        let l = rng1.gen_range(-0.5..0.5);
        let t = rng1.gen_range(-0.5..0.5);
        Event { l, t }
    });

    // E2: wider spread
    let mut e2 = EventDist::new(move || {
        let l = rng2.gen_range(-5.0..5.0);
        let t = rng2.gen_range(-5.0..5.0);
        Event { l, t }
    });

    let mean_delta = empirical_s2_invariance(&geom, c, v, &mut e1, &mut e2, 100_000);
    assert!(mean_delta.abs() < 5e-3, "mean delta too large: {}", mean_delta);
}