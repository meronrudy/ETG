#![doc = r#"G-ETG dynamic geometry: time-varying metric/speed fields and curvature interface.

This crate introduces a time-indexed geometry API suitable for slice-local
reasoning and invariance tests. It provides:
- [`GeometryT()`](etg/etg-geom/src/lib.rs): slice-local distance and invariant speed accessors.
- [`ScaledEuclidDyn()`](etg/etg-geom/src/lib.rs): a 1D Euclidean geometry with time-varying spatial scale and speed.
- [`Curvature()`](etg/etg-geom/src/lib.rs): a minimal curvature interface with an Ollivier–Ricci-like edge kappa.

Examples

```rust
use etg_core::Scalar;
use etg_geom::{GeometryT, ScaledEuclidDyn};

let geom = ScaledEuclidDyn {
    scale: |t: Scalar| 1.0 + 0.1 * t,
    speed: |t: Scalar| 1.0 + 0.2 * t,
};

let t0: Scalar = 0.3;
let d = geom.dist_at(t0, &(-1.0), &(2.0));
let c = geom.c_at(t0);
assert!(d > 0.0);
assert!(c > 0.0);
```
"#]
use etg_core::Scalar;

/// Time-indexed geometry: provides slice-local distance and invariant speed.
pub trait GeometryT<L> {
    /// Distance between a and b measured on the slice at time t.
    fn dist_at(&self, t: Scalar, a: &L, b: &L) -> Scalar;
    /// Invariant signal speed c on the slice at time t (must be > 0).
    fn c_at(&self, t: Scalar) -> Scalar;
}

/// Dynamic Euclidean implementation for L = f64 with time-varying scale and speed.
///
/// dist_at(t, x, y) = |scale(t)| * |x - y|
/// c_at(t) = speed(t)
///
/// The provided closures may return non-positive values; this implementation
/// clamps them to strictly positive via `f64::EPSILON` to satisfy metric/speed
/// requirements.
#[derive(Debug)]
pub struct ScaledEuclidDyn<SF, CF>
where
    SF: Fn(Scalar) -> Scalar,
    CF: Fn(Scalar) -> Scalar,
{
    /// Spatial scale factor as a function of time.
    pub scale: SF,
    /// Invariant speed c as a function of time.
    pub speed: CF,
}

#[inline]
fn clamp_pos(x: Scalar) -> Scalar {
    if x <= 0.0 { f64::EPSILON } else { x }
}

impl<SF, CF> GeometryT<Scalar> for ScaledEuclidDyn<SF, CF>
where
    SF: Fn(Scalar) -> Scalar,
    CF: Fn(Scalar) -> Scalar,
{
    #[inline]
    fn dist_at(&self, t: Scalar, a: &Scalar, b: &Scalar) -> Scalar {
        let s = clamp_pos((self.scale)(t)).abs();
        s * (a - b).abs()
    }

    #[inline]
    fn c_at(&self, t: Scalar) -> Scalar {
        clamp_pos((self.speed)(t))
    }
}

/// Curvature interface with a minimal Ollivier–Ricci-like edge kappa.
pub trait Curvature<L> {
    /// Returns an edge-based curvature (kappa) evaluated at slice t between a and b.
    fn or_edge_kappa(&self, t: Scalar, a: &L, b: &L) -> Scalar;
}

/// In this flat, scaled 1D Euclidean model, the Ollivier–Ricci-like edge kappa is zero.
/// The geometry is globally flat; a time-dependent overall spatial scale does not
/// introduce intrinsic curvature along the line in this model.
impl<SF, CF> Curvature<Scalar> for ScaledEuclidDyn<SF, CF>
where
    SF: Fn(Scalar) -> Scalar,
    CF: Fn(Scalar) -> Scalar,
{
    #[inline]
    fn or_edge_kappa(&self, _t: Scalar, _a: &Scalar, _b: &Scalar) -> Scalar {
        0.0
    }
}