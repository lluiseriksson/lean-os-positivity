# Hypothesis Frontier

Current as of 2026-07-03.

## Lean status

- Lean `sorry`: **0** in the `OSPositivity` source tree.
- Project axioms: **0**.
- Build target: `lake build OSPositivity`.
- This repository is currently a definition/interface satellite, not a completed
  proof of OS reconstruction or Wilson reflection positivity.

## Carried inputs

| Name / interface | Status | Meaning |
|---|---|---|
| `TransferMatrixReflectionCertificate.reflection_positive` | Carried certificate | M1 transfer-matrix proof that a given expectation is reflection positive. This replaces a broken dependency on `lean-transfer-matrix` until that package URL/import path is available. |
| `FerromagneticIsingData.transferCertificate` | Carried certificate | Ising ferromagnetic RP is exposed as a theorem from an explicit transfer-matrix certificate, not proved here yet. |
| `GaussianChainData.transferCertificate` | Carried certificate | Gaussian-chain RP is exposed as a theorem from an explicit covariance/transfer certificate, not proved here yet. |
| `GNSReconstruction` | Carried reconstruction data | The Hilbert quotient, kernel characterization, and reflected inner product are represented as explicit data. Existence from RP is not claimed. |
| `TransferOperator` | Carried operator data | Self-adjointness, positivity, and contraction of the transfer operator are fields. |
| `PositiveHamiltonian.represents_negLog` | Carried functional-calculus identification | Records that the Hamiltonian represents `-log T`; no spectral-calculus theorem is asserted here. |
| `WilsonRPCertificate.rp_wilson` | Carried certificate | Wilson-action lattice reflection positivity is the M3 statements-first target. It is not proved in this initial main branch. |
| `WilsonGaugeData.measure_is_wilson_gibbs` | Carried identification | The finite probability mass is identified with the Wilson Gibbs measure by an explicit field. |

## Distance to the program target

M0 definitions are present and compile.  M1-M3 are statement/interface first.
No continuum limit, no Wightman reconstruction, and no Clay mass gap theorem are
claimed.  The distance to the Clay problem remains effectively unchanged from
the mother repository: **~0% (<0.1%)** until the continuum construction and full
OS/Wightman reconstruction are formalized.
