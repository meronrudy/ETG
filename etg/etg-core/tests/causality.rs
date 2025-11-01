#![allow(unused_doc_comments)]
use etg_core::*;
use proptest::prelude::*;

// Golden: spacelike exclusion (dt < dx/c).
#[test]
fn golden_spacelike_exclusion() {
    let geom = Euclid1D;
    let c = 1.0;
    // dx=2, dt=1 -> spacelike, not causally allowed
    let e1 = Event { l: 0.0, t: 0.0 };
    let e2 = Event { l: 2.0, t: 1.0 };
    assert!(!causally_allows(&geom, c, &e1, &e2));
}

// Property: if dt <= dx/c - margin (margin>0), then not causally allowed.
proptest! {
    #[test]
    fn prop_spacelike_exclusion(dx in 0.01_f64..10.0, margin in 1e-6_f64..1.0) {
        let geom = Euclid1D;
        let c = 1.0;
        let dt = dx / c - margin;
        let e1 = Event { l: 0.0, t: 0.0 };
        let e2 = Event { l: dx,  t: dt   };
        prop_assert!(!causally_allows(&geom, c, &e1, &e2));
    }
}

// Property: if dt >= dx/c + margin (margin>0), then causally allowed.
proptest! {
    #[test]
    fn prop_timelike_causality(dx in 0.0_f64..10.0, margin in 1e-6_f64..1.0) {
        let geom = Euclid1D;
        let c = 1.0;
        let dt = dx / c + margin;
        let e1 = Event { l: 0.0, t: 0.0 };
        let e2 = Event { l: dx,  t: dt   };
        prop_assert!(causally_allows(&geom, c, &e1, &e2));
    }
}

// Golden: null boundary dt == dx/c is causally allowed (Euclid1D, c=1).
#[test]
fn golden_null_boundary_causal() {
    let geom = Euclid1D;
    let c = 1.0;
    let e1 = Event { l: 0.0, t: 0.0 };
    let e2 = Event { l: 2.0, t: 2.0 }; // dt=2, dx=2 -> null boundary
    // Forward direction: causal at boundary
    assert!(causally_allows(&geom, c, &e1, &e2));
    // Reverse direction: dt becomes negative -> not causal
    assert!(!causally_allows(&geom, c, &e2, &e1));
    // Interval is null in both directions
    let s12 = interval(&geom, c, &e1, &e2);
    let s21 = interval(&geom, c, &e2, &e1);
    assert!(s12.abs() < 1e-12, "s^2 not null forward: {s12}");
    assert!(s21.abs() < 1e-12, "s^2 not null reverse: {s21}");
}

// Golden: time-reversal flips causality while s^2 remains positive and equal (timelike).
#[test]
fn golden_time_reversal_causality_and_s2_consistency() {
    let geom = Euclid1D;
    let c = 1.0;
    let e1 = Event { l: 0.0, t: 0.0 };
    let e2 = Event { l: 2.0, t: 3.0 }; // dt=3, dx=2 -> timelike
    // Forward: causal
    assert!(causally_allows(&geom, c, &e1, &e2), "expected causal forward");
    // Reverse: not causal due to negative dt
    assert!(!causally_allows(&geom, c, &e2, &e1), "expected not causal backward");
    // Interval sign/size consistent under time reversal
    let s12 = interval(&geom, c, &e1, &e2);
    let s21 = interval(&geom, c, &e2, &e1);
    assert!(s12 > 0.0 && s21 > 0.0, "s^2 should be positive timelike: s12={s12}, s21={s21}");
    assert!((s12 - s21).abs() < 1e-12, "s^2 mismatch under time reversal: s12={s12}, s21={s21}");
}