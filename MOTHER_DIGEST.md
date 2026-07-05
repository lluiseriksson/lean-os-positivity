# Mother-facing digest

Date: 2026-07-05.

This digest is for `THE-ERIKSSON-PROGRAMME` consumers that need the current
Lean interface without reading every implementation module.  The stable
downstream import remains:

```lean
import Interfaces
```

No item below proves OS reconstruction, a continuum limit, a Yang-Mills mass
gap, or source construction.  Frontier data remain explicit certificates or
theorem hypotheses.

## Stable contract files

| File | Role | Downstream use |
|---|---|---|
| `Interfaces.lean` | Root public contract import. | Import this from the mother repo. |
| `INTERFACES.md` | Breaking-change ledger for public names. | Check before relying on argument order or names. |
| `HYPOTHESIS_FRONTIER.md` | Honesty ledger for explicit certificates and missing bridges. | Cite this when explaining what is still assumed. |

## Exact usable names

### Reflection positivity core

File: `OSPositivity/ReflectionPositivity.lean`

- `Observable (Omega : Type u) := Omega -> Complex`
- `ComplexNonnegative (z : Complex) : Prop`
- `Expectation.reflectionForm`
- `Expectation.ReflectionPositive`
- `FiniteProbability.toExpectation`
- `FiniteProbability.ReflectionPositive`
- `LatticeReflection.DependsOnlyOn`
- `LatticeReflection.positiveObservableSet`
- `LatticeReflection.ReflectionPositive`
- `LatticeReflection.reflectionPositive_eval`

Smallest consumption target: use `Expectation.ReflectionPositive` or
`LatticeReflection.ReflectionPositive` as the RP assumption passed into
downstream construction code.

### Pairing-form layer

File: `OSPositivity/PairingForm.lean`

- `WeightFunction`
- `FiniteProbability.toWeightFunction`
- `WeightFunction.pairingForm`
- `WeightFunction.reflectionForm_eq_pairingForm`
- `WeightFunction.pairingForm_add_left`
- `WeightFunction.pairingForm_add_right`
- `WeightFunction.pairingForm_smul_left`
- `WeightFunction.pairingForm_smul_right`
- `WeightFunction.pairingForm_conj_symm`
- `WeightFunction.reflectionForm_im_eq_zero`
- `WeightFunction.pairingForm_expand`
- `WeightFunction.normSq_pairingForm_le`
- `WeightFunction.pairingForm_eq_zero_of_null`
- `WeightFunction.ReflectionNullEquivalent`
- `WeightFunction.reflectionNullEquivalent_refl`
- `WeightFunction.reflectionNullEquivalent_symm`
- `WeightFunction.reflectionNullEquivalent_trans`
- `WeightFunction.pairingForm_respects_null_left`
- `WeightFunction.pairingForm_respects_null_right`
- `WeightFunction.pairingForm_respects_null`
- `WeightFunction.pairingForm_respects_null_equivalent`
- `WeightFunction.ReflectionNullContext`
- `WeightFunction.ReflectionNullContext.diagonal_nonnegative`
- `WeightFunction.ReflectionNullContext.refl`
- `WeightFunction.ReflectionNullContext.symm`
- `WeightFunction.ReflectionNullContext.trans`
- `WeightFunction.ReflectionNullContext.pairingForm_respects_null`

Main hypotheses to supply for `normSq_pairingForm_le`:

- `Function.Involutive theta`
- reflection-invariant weight: `∀ omega, w.weight (theta omega) = w.weight omega`
- diagonal nonnegativity for `F` and `G`
- span nonnegativity:
  `∀ b : Complex, ComplexNonnegative
    (Expectation.reflectionForm w.toExpectation theta (F + b • G))`

Smallest consumption target: use `ReflectionNullContext` when reflection
invariance and span positivity are fixed once for the model, then call
`ReflectionNullContext.refl`, `ReflectionNullContext.symm`,
`ReflectionNullContext.trans`, and
`ReflectionNullContext.pairingForm_respects_null` without restating those
hypotheses at every null-relation step.  Use the one-sided lemmas when only one
representative changes.  These only support well-definedness; they are not GNS
reconstruction theorems.

### Single-bond model

File: `OSPositivity/BondModel.lean`

- `LatticeReflection.DependsOnlyOn.zero`
- `LatticeReflection.DependsOnlyOn.add`
- `LatticeReflection.DependsOnlyOn.smul`
- `LatticeReflection.DependsOnlyOn.neg`
- `LatticeReflection.DependsOnlyOn.sub`
- `bondReflection`
- `bondWeight`
- `eval_of_dependsOnlyOn_true`
- `bondQuadForm_re`
- `bondQuadForm_im`
- `complexNonnegative_bondForm_of_psd`
- `bond_reflectionForm_eq`
- `bond_reflectionPositive`
- `psd_of_bond_reflectionPositive`
- `ferromagneticKernel`
- `ferromagneticKernel_nonneg`
- `ferromagneticKernel_symm`
- `ferromagneticKernel_psd`
- `isingBond_reflectionPositive`

Main hypotheses to supply for `bond_reflectionPositive`:

- finite spin type: `[Fintype S] [DecidableEq S]`
- kernel nonnegativity: `∀ s t, 0 ≤ k s t`
- kernel symmetry: `∀ s t, k s t = k t s`
- real PSD form: `∀ v : S -> Real, 0 ≤ ∑ s, ∑ t, k s t * v t * v s`

Smallest consumption target: instantiate `isingBond_reflectionPositive` when the
mother repo needs a no-certificate finite bond RP example, or use
`psd_of_bond_reflectionPositive` to recover the PSD obligation from an RP
certificate in tests.  Use the `DependsOnlyOn` closure helpers to keep
positive-side locality obligations stable when forming zero observables, linear
combinations, and nullspace differences such as `F - G`.

### Certificate interfaces

Files: `OSPositivity/TransferMatrix.lean`, `OSPositivity/GNS.lean`,
`OSPositivity/Wilson.lean`

- `TransferMatrixReflectionCertificate`
- `reflectionPositive_of_transferMatrixCertificate`
- `FerromagneticIsingData`
- `ferromagneticIsing_reflectionPositive`
- `GaussianChainData`
- `gaussianChain_reflectionPositive`
- `GNSReconstruction`
- `TransferOperator`
- `PositiveHamiltonian`
- `OrthogonalToVacuum`
- `HasOperatorMassGap`
- `HasOperatorMassGap.pos`
- `HasOperatorMassGap.quadratic_lower_bound`
- `WilsonGaugeData`
- `WilsonReflectionPositive`
- `WilsonRPCertificate`
- `rpWilson_of_certificate`
- `WilsonOSMassGapPackage`

Smallest consumption target: pass `TransferMatrixReflectionCertificate` or
`WilsonRPCertificate` explicitly.  Do not treat these certificates as proved by
this repo unless a theorem constructs the certificate in the consuming context.

## Suggested next bridge

The next low-risk bridge is to derive a `ReflectionNullContext` from a concrete
closed positive-observable class in a finite model, so downstream code can move
from model reflection positivity to the packaged null-relation API without
manual span hypotheses.

Expected source: `Expectation.ReflectionPositive`,
`LatticeReflection.DependsOnlyOn.add`/`smul`, and
`WeightFunction.ReflectionNullContext`.

Expected shape: prove only a model/interface helper that supplies the context;
do not construct `GNSReconstruction` or a Hilbert quotient in this repository.
