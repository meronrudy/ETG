#![allow(unused_doc_comments)]
use etg_core::*;
use proptest::prelude::*;

// Golden: null preservation s^2 == 0 before/after boost.
#[test]
fn golden_null_preservation() {
    let c = 1.0;
    let v = 0.5;
    // Choose a null pair: dx = c * dt
    let dt = 3.0;
    let dx = c * dt;
    let s_before = s2(c, dt, dx);
    assert!(s_before.abs() < 1e-12, "not null before: {s_before}");
    let (dtp, dxp) = boost(c, v, dt, dx);
    let s_after = s2(c, dtp, dxp);
    assert!(s_after.abs() < 1e-9, "not null after: {s_after}");
}

// Property: null preservation for random subluminal velocities and scales.
proptest! {
    #[test]
    fn prop_null_preservation(
        v in -0.9_f64..0.9_f64,
        k in -10.0_f64..10.0_f64
    ) {
        let c = 1.0;
        let dt = k;
        let dx = c * dt; // null line
        let (dtp, dxp) = boost(c, v, dt, dx);
        let s_after = s2(c, dtp, dxp);
        prop_assert!(s_after.abs() < 1e-8);
    }
}

// Golden: composition of boosts equals single boost with Einstein addition.
#[test]
fn golden_boost_composition() {
    let c = 1.0;
    let v1 = 0.3;
    let v2 = 0.4;
    let dt = 3.0;
    let dx = 2.0;

    // Sequential boosts
    let (dt1, dx1) = boost(c, v1, dt, dx);
    let (dt2, dx2) = boost(c, v2, dt1, dx1);

    // Equivalent single boost with velocity addition
    let v12 = (v1 + v2) / (1.0 + (v1 * v2) / (c * c));
    let (dt_single, dx_single) = boost(c, v12, dt, dx);

    assert!((dt2 - dt_single).abs() < 1e-9, "dt mismatch: seq={dt2}, single={dt_single}");
    assert!((dx2 - dx_single).abs() < 1e-9, "dx mismatch: seq={dx2}, single={dx_single}");
}

// Property: composition equality holds across random subluminal velocities.
proptest! {
    #[test]
    fn prop_boost_composition(
        v1 in -0.6_f64..0.6_f64,
        v2 in -0.6_f64..0.6_f64,
        dt in -10.0_f64..10.0_f64,
        dx in -10.0_f64..10.0_f64
    ) {
        let c = 1.0;
        let (dt1, dx1) = boost(c, v1, dt, dx);
        let (dt2, dx2) = boost(c, v2, dt1, dx1);
        let v12 = (v1 + v2) / (1.0 + (v1 * v2) / (c * c));
        let (dt_single, dx_single) = boost(c, v12, dt, dx);
        prop_assert!((dt2 - dt_single).abs() < 1e-8);
        prop_assert!((dx2 - dx_single).abs() < 1e-8);
    }
}