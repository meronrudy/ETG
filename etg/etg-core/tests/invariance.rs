#![allow(unused_doc_comments)]
use etg_core::*;
use proptest::prelude::*;

// Golden test: exact numeric case used in Coq example.
#[test]
fn golden_invariance_specific() {
    let geom = Euclid1D;
    let c = 1.0;
    let e1 = Event { l: 0.0_f64, t: 0.0 };
    let e2 = Event { l: 2.0_f64, t: 3.0 };
    let dt = e2.t - e1.t;
    let dx = geom.dist(&e1.l, &e2.l);
    let (dtp, dxp) = boost(c, 0.6, dt, dx);
    let s_before = s2(c, dt, dx);
    let s_after = s2(c, dtp, dxp);
    assert!((s_after - s_before).abs() < 1.0e-9, "s^2 invariance failed: before={s_before}, after={s_after}");
}

// Golden test: causality inequality on a timelike-separated pair.
#[test]
fn golden_causality_timelike() {
    let geom = Euclid1D;
    let c = 1.0;
    let e1 = Event { l: 0.0, t: 0.0 };
    let e2 = Event { l: 1.0, t: 2.0 }; // dt=2, dx=1 -> dt >= dx/c
    assert!(causally_allows(&geom, c, &e1, &e2));
}

// Property test: invariance holds for random differences and subluminal v.
proptest! {
    #[test]
    fn prop_invariance(
        v in -0.9_f64..0.9_f64,
        dt in -10.0_f64..10.0_f64,
        dx in -10.0_f64..10.0_f64
    ) {
        let c = 1.0;
        let (dtp, dxp) = boost(c, v, dt, dx);
        let s_before = s2(c, dt, dx);
        let s_after  = s2(c, dtp, dxp);
        prop_assert!((s_after - s_before).abs() < 1.0e-8);
    }
}