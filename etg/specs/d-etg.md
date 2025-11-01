# D-ETG (Deterministic Event–Time Geometry) — v0.1 Spec and API Outline

Objective
- Deliver a thin, end-to-end deterministic ETG vertical slice that:
  - Fixes the core invariant (interval invariance),
  - Runs a reference implementation,
  - Exports a stable API that P-ETG and G-ETG can extend without breaking changes.

Anchors and references
- Proof artifacts (Coq):
  - [etg/proofs-coq/Base.v](etg/proofs-coq/Base.v)
  - [etg/proofs-coq/Metric.v](etg/proofs-coq/Metric.v)
  - [etg/proofs-coq/DETG.v](etg/proofs-coq/DETG.v)
  - [etg/proofs-coq/Frames.v](etg/proofs-coq/Frames.v)
  - [etg/proofs-coq/Invariance.v](etg/proofs-coq/Invariance.v)
  - [etg/proofs-coq/PETG.v](etg/proofs-coq/PETG.v)
  - [etg/proofs-coq/GETG.v](etg/proofs-coq/GETG.v)
  - [etg/proofs-coq/Examples.v](etg/proofs-coq/Examples.v)
- Toolchain: [etg/specs/TOOLCHAIN.md](etg/specs/TOOLCHAIN.md)

Design once, extend later (contracts)
- Time and Location abstractions
  - Time is a totally ordered additive group (default to real numbers now; keep parametric to allow discrete time later).
  - Location carries a metric space through a provider; distance is not hardcoded, enabling graph or manifold later.
- Event, interval, and causality
  - Event: a pair (location, time).
  - Interval: scalar computed from dt and dx using the invariant speed c.
  - Causality: inequality relating dt and dx with c to determine causal allowance.
- Frames and invariance
  - Frame provides signed spatial coordinate differences to define boosts over differences.
  - Admissible frames preserve the null form; these become the predicate used by P-ETG and G-ETG to accept transforms.
- Null-form provider
  - Null form is a quadratic form provider; in G-ETG it becomes slice-local and time-varying.
- Randomization hooks (kept out of core)
  - Sampling and random variables live in P-ETG; core remains deterministic.
- Geometry provider (stubbed in D-ETG)
  - Geometry provider supplies the metric for locations; becomes time-indexed in G-ETG.

API outline (Rust crates, to be implemented)
- Crate etg-core (deterministic foundation, no probability):
  - Types
    - Time (trait-like abstraction, default real)
    - Location (opaque type parameterized by a metric provider)
    - Event (location, time)
    - Scalar (numeric scalar for intervals)
  - Traits
    - MetricSpace for Location
    - Frame for signed differences
    - Geometry for metric provider binding
    - LorentzLike predicate to check null-preservation
  - Pure functions
    - interval: compute scalar interval from two events
    - causally_allows: causal inequality classification
    - boost: construct a one-dimensional boost transform over differences (reference transform for tests)
- Crate etg-prob (probabilistic layer; no breaking changes to etg-core):
  - Types
    - EventDist (distribution over events)
    - IntervalRV (random variable induced from a pair of random events)
  - Functions
    - causal_prob: probability of causal allowance between two event distributions
  - Estimators and serializers added here so deterministic users incur zero dependency drag
- Crate etg-geom (dynamic geometry fields):
  - Types
    - Geometry_t (time-indexed geometry)
    - Curvature interface (e.g., discrete Ricci or Ollivier-Ricci)
  - Functions
    - Providers for local metric and null forms on slices
- Crate etg-evolve (evolution of dynamic geometry):
  - Stepper that advances Geometry_t with conservation checks
  - Hooks for telemetry and safety invariants (e.g., divergence of a conserved field near zero)

Stable interfaces that future-proof the core
- Keep Time parametric and default to real numbers.
- Keep Geometry behind a trait from day one; all call sites depend on a provider, not a concrete metric.
- Encode null-form preservation as the admissibility predicate for frames; P-ETG and G-ETG reuse the same predicate.
- Keep probability strictly in etg-prob; deterministic users depend only on etg-core.

Mapping proofs to API
- Interval invariance under boosts:
  - Formalized in the Coq proofs; see [etg/proofs-coq/Base.v](etg/proofs-coq/Base.v) and [etg/proofs-coq/Invariance.v](etg/proofs-coq/Invariance.v).
  - Rust API: the boost reference implementation in etg-core must pass golden tests that check invariance over a range of velocities.
- Causality classification:
  - Defined in [etg/proofs-coq/DETG.v](etg/proofs-coq/DETG.v), driven by the c parameter and the metric over locations.
  - Rust API: causally_allows returns a classification that matches proofs for deterministic cases; property tests should match Coq-driven fixtures.

Acceptance criteria (D-ETG v0.1)
- Coq proofs
  - Interval invariance proven and checked against numeric instances; example invariance holds in [etg/proofs-coq/Examples.v](etg/proofs-coq/Examples.v).
- Rust etg-core
  - Expose Event, interval, causally_allows, and boost APIs.
  - Golden tests:
    - Invariance: s^2 equality holds over tested boosts.
    - Timelike order: timelike relations do not flip under admissible transforms.
    - Spacelike exclusion: causal allowance rejects spacelike-separated pairs.
    - Null preservation: frames tagged admissible preserve the null set.
    - Boost composition: reference compositions match expected 1D algebraic identities.
  - Property tests:
    - Generate random numeric pairs within safe velocity bounds and assert invariance holds (within tolerance).
- CI
  - Build Coq proofs and Rust tests on macOS and Linux.
  - Publish artifact badges upon success.

Testing strategy
- Golden fixtures derived from the same numeric identities as in [etg/proofs-coq/Base.v](etg/proofs-coq/Base.v), reified into Rust tests.
- Property-based tests to explore wider ranges and edge cases, constrained so that velocities stay subluminal relative to c.
- Serialization tests for later P-ETG integration (types serialize without probabilistic dependencies when behind feature flags).

Extensibility (P-ETG and G-ETG)
- P-ETG
  - Add Sampler and random variable types in etg-prob, keeping deterministic core unchanged.
  - Preserve invariance in distributional sense; provide stochastic tests with tolerance bands.
- G-ETG
  - Promote Geometry into a time-varying provider; introduce local slice null forms and curvature interfaces in etg-geom.
  - Provide an evolution stepper in etg-evolve with stability and conservation checks and basic scenario demos.

Version plan
- v0.1 (D-ETG): Freeze API for Event, Frame, interval, and causally_allows.
- v0.2 (P-ETG): Add EventDist, IntervalRV, causal_prob.
- v0.3 (G-ETG): Add time-indexed Geometry_t, Curvature, Evolver.
- v1.0: Stabilize APIs after integration tests and documentation.

Next actions (tracked)
- Generate Rust workspace skeleton with etg-core, etg-prob, etg-geom, etg-evolve crates.
- Implement golden and property tests in etg-core mirroring proofs.
- Set up CI to build Coq proofs and run Rust tests on Linux/macOS.