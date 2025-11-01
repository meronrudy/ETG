#![doc = r#"
etg-core: Deterministic Event–Time Geometry (D-ETG) core

Spec anchors:
- See [etg/specs/d-etg.md](../../specs/d-etg.md)
Proof anchors:
- See [etg/proofs-coq](../../proofs-coq)

This crate provides:
- Core types Event and Scalar
- MetricSpace trait and a Euclid1D metric for simple tests
- interval, causally_allows functions over events/geometry
- boost(c, v, dt, dx) reference transform over differences
- LorentzLike predicate (placeholder) for admissible frames
"#]

pub type Scalar = f64;

/// A metric provider for location type `L`.
pub trait MetricSpace<L> {
    fn dist(&self, a: &L, b: &L) -> Scalar;
}

/// An event consists of a location and an absolute time (Scalar).
#[derive(Clone, Debug)]
pub struct Event<L> {
    pub l: L,
    pub t: Scalar,
}

/// Minkowski-like quadratic form s^2 = c^2 dt^2 - dx^2 over number differences.
#[inline]
pub fn s2(c: Scalar, dt: Scalar, dx: Scalar) -> Scalar {
    c * c * dt * dt - dx * dx
}

/// Interval between two events via a geometry provider and invariant speed c.
#[inline]
pub fn interval<L, G: MetricSpace<L>>(geom: &G, c: Scalar, e1: &Event<L>, e2: &Event<L>) -> Scalar {
    let dt = e2.t - e1.t;
    let dx = geom.dist(&e1.l, &e2.l);
    s2(c, dt, dx)
}

/// Causality predicate: dt >= dx / c
#[inline]
pub fn causally_allows<L, G: MetricSpace<L>>(geom: &G, c: Scalar, e1: &Event<L>, e2: &Event<L>) -> bool {
    let dt = e2.t - e1.t;
    let dx = geom.dist(&e1.l, &e2.l);
    dt >= dx / c
}

/// 1D Lorentz-like boost over differences (reference implementation).
/// Precondition: |v| < c, c > 0.
#[inline]
pub fn boost(c: Scalar, v: Scalar, dt: Scalar, dx: Scalar) -> (Scalar, Scalar) {
    let gamma = 1.0 / (1.0 - (v * v) / (c * c)).sqrt();
    let dtp = gamma * (dt - (v * dx) / (c * c));
    let dxp = gamma * (dx - v * dt);
    (dtp, dxp)
}

/// A simple Euclidean metric in 1D for examples/tests.
pub struct Euclid1D;

impl MetricSpace<f64> for Euclid1D {
    #[inline]
    fn dist(&self, a: &f64, b: &f64) -> Scalar {
        (a - b).abs()
    }
}

/// A simple boost descriptor; admissibility predicate placeholder.
pub struct Boost1D {
    pub v: Scalar,
}

/// Admissibility interface for frames/transforms.
/// G-ETG and P-ETG will reuse this predicate.
pub trait LorentzLike {
    fn preserves_null(&self, c: Scalar) -> bool;
}

impl LorentzLike for Boost1D {
    #[inline]
    fn preserves_null(&self, _c: Scalar) -> bool {
        // The numeric boost() preserves the null form by construction.
        true
    }
}