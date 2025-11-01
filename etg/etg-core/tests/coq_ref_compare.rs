use etg_core::boost;

mod coq_ref {
    #[inline]
    pub fn gamma(c: f64, v: f64) -> f64 {
        1.0 / (1.0 - (v * v) / (c * c)).sqrt()
    }

    #[inline]
    pub fn boost_dt(c: f64, v: f64, dt: f64, dx: f64) -> f64 {
        let g = gamma(c, v);
        g * (dt - (v * dx) / (c * c))
    }

    #[inline]
    pub fn boost_dx(c: f64, v: f64, dt: f64, dx: f64) -> f64 {
        let g = gamma(c, v);
        g * (dx - v * dt)
    }
}

fn is_finite_all(vals: &[f64]) -> bool {
    vals.iter().all(|x| x.is_finite())
}

/// Local numeric s^2 with fused multiply-add for improved precision:
/// s^2 = (c*c)*(dt*dt) - (dx*dx)
#[inline]
fn s2_fma(c: f64, dt: f64, dx: f64) -> f64 {
    // Use mul_add to compute (c*c)*(dt*dt) + (-(dx*dx)) with one rounding
    (c * c).mul_add(dt * dt, -(dx * dx))
}

#[test]
fn compare_boost_outputs_many_random() {
    use rand::{rngs::StdRng, Rng, SeedableRng};

    const N_SAMPLES: usize = 20_000;
    const TOL: f64 = 1e-12;

    let mut rng = StdRng::seed_from_u64(0xC0A1_5EED_2025);

    let mut accepted = 0usize;
    // Loop until we collect N_SAMPLES valid finite tuples.
    while accepted < N_SAMPLES {
        // Sample ranges (chosen to avoid numerical amplification near singularities while
        // remaining stringent):
        // c ∈ [0.5, 2.5], v ∈ [-0.8c, 0.8c], dt, dx ∈ [-8, 8]
        let c = rng.gen_range(0.5..=2.5);
        let vmax = 0.8 * c;
        let v = rng.gen_range(-vmax..=vmax);
        let dt = rng.gen_range(-8.0..=8.0);
        let dx = rng.gen_range(-8.0..=8.0);

        // Short-circuit on any non-finite (should not occur with these ranges, but be defensive).
        if !is_finite_all(&[c, v, dt, dx]) {
            continue;
        }

        // Library implementation
        let (dt_lib, dx_lib) = boost(c, v, dt, dx);

        // Reference formulas (transcribed from Coq Base.v structure)
        let dt_ref = coq_ref::boost_dt(c, v, dt, dx);
        let dx_ref = coq_ref::boost_dx(c, v, dt, dx);

        // If any result is non-finite, skip this sample.
        if !is_finite_all(&[dt_lib, dx_lib, dt_ref, dx_ref]) {
            continue;
        }

        // Tight equality vs Coq reference
        let d_dt = (dt_lib - dt_ref).abs();
        let d_dx = (dx_lib - dx_ref).abs();
        assert!(
            d_dt <= TOL,
            "dt mismatch: |{} - {}| = {} > {} (c={}, v={}, dt={}, dx={})",
            dt_lib,
            dt_ref,
            d_dt,
            TOL,
            c,
            v,
            dt,
            dx
        );
        assert!(
            d_dx <= TOL,
            "dx mismatch: |{} - {}| = {} > {} (c={}, v={}, dt={}, dx={})",
            dx_lib,
            dx_ref,
            d_dx,
            TOL,
            c,
            v,
            dt,
            dx
        );

        // s^2 invariance: c^2 dt^2 - dx^2 preserved
        let s_before = s2_fma(c, dt, dx);
        let s_after = s2_fma(c, dt_lib, dx_lib);
        let ds = (s_before - s_after).abs();
        assert!(
            ds <= TOL,
            "s^2 invariance violated: |{} - {}| = {} > {} (c={}, v={}, dt={}, dx={}; dt'={}, dx'={})",
            s_before,
            s_after,
            ds,
            TOL,
            c,
            v,
            dt,
            dx,
            dt_lib,
            dx_lib
        );

        accepted += 1;
    }
}