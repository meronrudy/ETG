use etg_core::{boost, s2, Scalar};
use etg_geom::{GeometryT, ScaledEuclidDyn};

#[test]
fn slice_local_invariance_with_instantaneous_c() {
    // Setup dynamic geometry: scale(t) = 1 + 0.1 t, c(t) = 1 + 0.2 t
    let geom = ScaledEuclidDyn {
        scale: |t: Scalar| 1.0 + 0.1 * t,
        speed: |t: Scalar| 1.0 + 0.2 * t,
    };

    let t0: Scalar = 0.3;
    let c0 = geom.c_at(t0);

    let dt: Scalar = 1.25;
    let dx: Scalar = 0.8;
    let v: Scalar = 0.5 * c0; // |v| < c(t0)

    let s2_before = s2(c0, dt, dx);
    let (dtp, dxp) = boost(c0, v, dt, dx);
    let s2_after  = s2(c0, dtp, dxp);

    assert!(
        (s2_after - s2_before).abs() <= 1e-12,
        "slice-local invariance failed: before={s2_before}, after={s2_after}"
    );
}

#[test]
fn null_preservation_at_slice() {
    let geom = ScaledEuclidDyn {
        scale: |t: Scalar| 1.0 + 0.1 * t,
        speed: |t: Scalar| 1.0 + 0.2 * t,
    };
    let t0: Scalar = 0.3;
    let c0 = geom.c_at(t0);

    let dt: Scalar = 0.9;
    let dx: Scalar = c0 * dt; // null separation
    let v: Scalar = 0.4 * c0;

    let s2_before = s2(c0, dt, dx);
    assert!(s2_before.abs() <= 1e-12, "not null before boost: s2={s2_before}");

    let (dtp, dxp) = boost(c0, v, dt, dx);
    let s2_after  = s2(c0, dtp, dxp);
    assert!(s2_after.abs() <= 1e-12, "null not preserved under boost: s2'={s2_after}");
}

#[test]
fn classification_sensitivity_across_slices() {
    // Fix dt and choose dx so that class changes as c(t) changes
    let geom = ScaledEuclidDyn {
        scale: |t: Scalar| 1.0 + 0.1 * t,
        speed: |t: Scalar| 1.0 + 0.2 * t,
    };
    let dt: Scalar = 1.0;
    let dx: Scalar = 1.1; // choose to straddle dt vs dx/c(t)

    let t1: Scalar = 0.0; // c1 = 1.0
    let t2: Scalar = 1.0; // c2 = 1.2

    let c1 = geom.c_at(t1);
    let c2 = geom.c_at(t2);

    // At t1: dx / c1 = 1.1 > dt => spacelike
    assert!(dx / c1 > dt, "expected spacelike at t1");

    // At t2: dx / c2 ≈ 0.916 < dt => timelike
    assert!(dx / c2 < dt, "expected timelike at t2");
}