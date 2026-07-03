# Hypothesis Frontier

Date: 2026-07-03 (second iteration)

## Lean `sorry` count

`main`: 0. No `axiom` declarations.
Statement-first obligations live on `frontier/M1` under
`OSPositivity/Frontier/` and are listed below.

## Explicit hypotheses / certificates currently carried

Unchanged certificate interfaces: `TransferMatrixReflectionCertificate`,
`GNSReconstruction` (data interface), `WilsonRPCertificate`.  These remain
frontier data for generic models.

NEW: the certificates are no longer empty of instances — see below.

## Closed facts on `main`

M0 layer (previous iteration): definitions of `Expectation.reflectionForm`,
`ReflectionPositive`, `FiniteProbability`, `LatticeReflection`,
`DependsOnlyOn`, `positiveObservableSet`.

Pairing-form layer (`PairingForm.lean`):

* `WeightFunction` (unnormalized nonnegative weights) with
  `FiniteProbability.toWeightFunction` bridge (definitional).
* `pairingForm`: sesquilinear form `B(F,G) = Σ w conj(F∘θ) G`;
  `reflectionForm_eq_pairingForm`; sesquilinearity in both slots.
* `pairingForm_conj_symm`: Hermitian symmetry for reflection-invariant
  weights (proof by reindexing along the involution).
* `reflectionForm_im_eq_zero`: the reflection form is real.
* `pairingForm_expand`: diagonal expansion on the span of two observables.
* `normSq_pairingForm_le`: **the reflection Cauchy-Schwarz inequality**
  (Glimm-Jaffe Thm 6.2.2) via the discriminant argument.  This is the
  inequality that makes the M2 GNS quotient well defined.

Bond-model layer (`BondModel.lean`):

* `DependsOnlyOn.add`, `DependsOnlyOn.smul`: half-space observables form a
  complex subspace (closure needed to feed Cauchy-Schwarz from RP).
* `bondReflection`, `bondWeight`, `eval_of_dependsOnlyOn_true`
  (factorization of half-space observables).
* `bondQuadForm_re`, `bondQuadForm_im`,
  `complexNonnegative_bondForm_of_psd`: realification — real symmetric PSD
  kernels control the complex quadratic form.
* `bond_reflectionForm_eq`: the reflection form of a local observable IS the
  kernel quadratic form (reindexing `(Bool → S) ≃ S × S`).
* `bond_reflectionPositive` and `psd_of_bond_reflectionPositive`:
  **reflection positivity across a bond ⟺ PSD transfer kernel** —
  Osterwalder-Seiler's mechanism in miniature, both directions proved.
* `ferromagneticKernel_psd`, `isingBond_reflectionPositive`: the zero-field
  ferromagnetic Ising/Potts bond (`0 ≤ β`) is reflection positive, for
  EVERY finite spin space.  First model-level RP theorem of the ecosystem.

## Frontier obligations (branch `frontier/M1`, statement-first, sorried)

`Frontier/GNSChain.lean`:

* `pairingForm_eq_zero_of_null` (null observables absorb the pairing; direct
  consequence of `normSq_pairingForm_le`).
* `gnsSeminorm_add_le` (triangle inequality for the GNS seminorm).
* `exists_gnsReconstruction` (M2: reconstruction data exist for every
  reflection-positive finite weight).
* `multiBond_reflectionPositive` (M1: n reflected bonds; route: Schur
  product theorem / `Matrix.PosSemidef` Hadamard closure).

## Honest distance to the programme target

Reflection positivity now has content: a two-sided characterization on the
minimal lattice and one unconditional model theorem, plus the Cauchy-Schwarz
inequality all of M2 rests on.  Missing: the chain/torus geometry (multi-bond
statement above), the actual GNS quotient construction, the transfer-matrix
import (blocked on `lean-transfer-matrix` vM1), and everything Wilson.
Continuum limit and full OS axioms remain deliberately out of scope.

## Frontier branch policy

Unchanged: `sorry` only on `frontier/*` branches, each updating this file.
