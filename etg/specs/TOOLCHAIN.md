# ETG Proofs Toolchain

Build status
- make clean all: SUCCESS at timestamp: 2025-10-31T02:14:02Z

Coq
- Version output:
  ```
  The Coq Proof Assistant, version 8.13.2 (January 2025)
  compiled on Jan 29 2025 22:29:36 with OCaml 4.14.1
  ```

OS/Platform
- sw_vers (if available):
  ```
  ProductName:  macOS
  ProductVersion:  15.6.1
  BuildVersion:  24G90
  ```
- uname:
  ```
  Darwin Mac 24.6.0 Darwin Kernel Version 24.6.0: Mon Jul 14 11:30:40 PDT 2025; root:xnu-11417.140.69~1/RELEASE_ARM64_T8132 arm64
  ```

Notes
- Proof files built:
  - [Base.v](etg/proofs-coq/Base.v)
  - [Metric.v](etg/proofs-coq/Metric.v)
  - [DETG.v](etg/proofs-coq/DETG.v)
  - [Frames.v](etg/proofs-coq/Frames.v)
  - [Invariance.v](etg/proofs-coq/Invariance.v)
  - [PETG.v](etg/proofs-coq/PETG.v)
  - [GETG.v](etg/proofs-coq/GETG.v)
  - [Examples.v](etg/proofs-coq/Examples.v)

- This document is updated whenever the toolchain is validated or changed.