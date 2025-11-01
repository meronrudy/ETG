#![doc = r#"Evolution stepper skeleton for time-varying geometry.

Provides:
- `Evolver<G>` trait.
- `Field1D`: a simple 1D scalar field with `sum()` helper.
- `DiffuseEvolver`: a conservative explicit diffusion-like stepper (zero-flux).
- `conserved_sum`: helper to check mass conservation across a step.
"#]
use etg_core::Scalar;

/// A minimal evolution stepper interface.
pub trait Evolver<G> {
    fn step(&mut self, g: &mut G, dt: Scalar);
}

/// A simple scalar field over a 1D lattice.
#[derive(Clone, Debug)]
pub struct Field1D {
    pub data: Vec<Scalar>,
}
impl Field1D {
    pub fn new(data: Vec<Scalar>) -> Self { Self { data } }
    #[inline]
    pub fn len(&self) -> usize { self.data.len() }
    #[inline]
    pub fn is_empty(&self) -> bool { self.data.is_empty() }
    #[inline]
    pub fn sum(&self) -> Scalar { self.data.iter().copied().sum() }
}

/// Check conservation of total sum between two fields within a relative tolerance.
///
/// Returns true iff:
/// |sum(next) - sum(prev)| ≤ tol * max(1.0, |sum(prev)|)
#[inline]
pub fn conserved_sum(prev: &Field1D, next: &Field1D, tol: Scalar) -> bool {
    let sp = prev.sum();
    let sn = next.sum();
    let diff = (sn - sp).abs();
    let denom = 1.0_f64.max(sp.abs());
    diff <= tol * denom
}

/**/
/// A conservative explicit stepper: zero-flux boundaries, symmetric stencil.
///
/// new\[i] = old\[i] + alpha*dt*(old\[i-1] - 2*old\[i] + old\[i+1])
///
/// Zero-flux boundaries are implemented by mirroring the boundary values:
/// left = old\[0] for i=0 and right = old\[n-1] for i=n-1. For a uniform field,
/// the discrete Laplacian vanishes everywhere, preserving total "mass" exactly
/// up to floating-point rounding.
#[derive(Clone, Copy, Debug)]
pub struct DiffuseEvolver {
    pub alpha: Scalar,
}
impl Evolver<Field1D> for DiffuseEvolver {
    fn step(&mut self, f: &mut Field1D, dt: Scalar) {
        let n = f.len();
        if n == 0 { return; }
        let a = self.alpha * dt;
        let old = f.data.clone();
        for i in 0..n {
            let left  = if i == 0 { old[0] } else { old[i - 1] };
            let mid   = old[i];
            let right = if i + 1 == n { old[n - 1] } else { old[i + 1] };
            f.data[i] = mid + a * (left - 2.0 * mid + right);
        }
        // This discretization is conservative under zero-flux boundaries;
        // numerical drift is bounded by floating precision.
    }
}