# Mother-facing digest

Date: 2026-07-06.

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
| `OSPositivity/MotherOracle.lean` | Compile-time consumer oracle. | Checks the `Interfaces` import path for pairing-form algebra, Cauchy-Schwarz/null-absorption helpers, locality/span helpers, and one-sided/two-sided null-representative test shapes. |
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
- `WeightFunction.reflectionNullContext_of_reflectionPositive_univ`
- `WeightFunction.ReflectionNullContext.diagonal_nonnegative`
- `WeightFunction.ReflectionNullContext.refl`
- `WeightFunction.ReflectionNullContext.symm`
- `WeightFunction.ReflectionNullContext.trans`
- `WeightFunction.ReflectionNullContext.pairingForm_respects_null_left`
- `WeightFunction.ReflectionNullContext.pairingForm_respects_null_right`
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
hypotheses at every null-relation step.  If the model has
`Expectation.ReflectionPositive ... Set.univ`, build the context with
`WeightFunction.reflectionNullContext_of_reflectionPositive_univ`.  Use the
context one-sided lemmas when only the left or right representative changes;
use the combined lemma when both representatives change.  These only support
well-definedness; they are not GNS reconstruction theorems.

### Single-bond model

File: `OSPositivity/BondModel.lean`

- `LatticeReflection.DependsOnlyOn.zero`
- `LatticeReflection.DependsOnlyOn.add`
- `LatticeReflection.DependsOnlyOn.smul`
- `LatticeReflection.DependsOnlyOn.neg`
- `LatticeReflection.DependsOnlyOn.sub`
- `LatticeReflection.reflectionPositive_add_smul`
- `LatticeReflection.reflectionPositive_sub_add_smul`
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
- `isingBond_reflectionPositive_sub_add_smul`
- `isingBond_pairingForm_respects_null_left`
- `isingBond_pairingForm_respects_null_right`
- `isingBond_pairingForm_respects_null`
- `isingBond_pairingForm_respects_null_trueSide`

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
combinations, and nullspace differences such as `F - G`.  When an existing
`LatticeReflection.ReflectionPositive` hypothesis is available, call
`LatticeReflection.reflectionPositive_add_smul h hF hG b` to produce the span
nonnegativity input for `F + b • G` from exact positive-side locality proofs
`hF` and `hG`.  For null-representative differences, call
`LatticeReflection.reflectionPositive_sub_add_smul h hF₁ hF₂ hG b` to produce
the input for `(F₁ - F₂) + b • G`.  In the concrete ferromagnetic bond model,
call `isingBond_reflectionPositive_sub_add_smul hbeta hF₁ hF₂ hG b` for that
same span shape without manually re-invoking the model RP theorem.  When the
null relation for `F₁` and `F₂` is already known, call
`isingBond_pairingForm_respects_null_left hbeta hF₁ hF₂ hG hnull` to replace
the left pairing-form representative inside the concrete bond model without a
`Set.univ` null context.  For the symmetric right-side replacement, call
`isingBond_pairingForm_respects_null_right hbeta hF hG₁ hG₂ hnull`.  To replace
both representatives in one concrete bond-model pairing form, call
`isingBond_pairingForm_respects_null hbeta hF₁ hF₂ hG₁ hG₂ hnull_left hnull_right`.
For oracle/tests whose locality hypotheses are already written as literal
`({true} : Set Bool)`, call
`isingBond_pairingForm_respects_null_trueSide hbeta hF₁ hF₂ hG₁ hG₂ hnull_left hnull_right`;
it is only a wrapper around the concrete two-sided helper.

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

## Consumer oracle

`OSPositivity/MotherOracle.lean` now contains compile-time `example`s that
import only `Interfaces` and call
`isingBond_pairingForm_respects_null_left`,
`isingBond_pairingForm_respects_null_right`, and
`isingBond_pairingForm_respects_null_trueSide`, showing the exact hypothesis
bundles that THE-ERIKSSON-PROGRAMME should supply.

Source shape: concrete `{true}`-locality hypotheses plus named
`WeightFunction.ReflectionNullEquivalent` hypotheses for either one changed
observable pair or both changed observable pairs.

The same oracle file also checks the generic null-context API from
`import Interfaces`: construction by
`WeightFunction.reflectionNullContext_of_reflectionPositive_univ`,
then `WeightFunction.ReflectionNullContext.diagonal_nonnegative`, `.refl`,
`.symm`, `.trans`, `.pairingForm_respects_null_left`,
`.pairingForm_respects_null_right`, and `.pairingForm_respects_null`.
It also checks the direct explicit-hypothesis route
`WeightFunction.pairingForm_respects_null_equivalent`, for consumers that have
`Function.Involutive theta`, reflection-invariant weights, diagonal
nonnegativity, and the two span-nonnegativity hypotheses but have not packaged
them into a `WeightFunction.ReflectionNullContext w theta`.  These are the
null-equivalence bookkeeping surfaces for consumers that have full-observable
reflection positivity or fixed model-level null-equivalence inputs.

Before quotient construction, the oracle also checks the basic pairing-form
algebra names from `import Interfaces`:
`WeightFunction.reflectionForm_eq_pairingForm`,
`WeightFunction.pairingForm_add_left`,
`WeightFunction.pairingForm_add_right`,
`WeightFunction.pairingForm_smul_left`,
`WeightFunction.pairingForm_smul_right`, and
`WeightFunction.pairingForm_conj_symm`.

The oracle also checks the quotient-obligation helpers from `import
Interfaces`: `WeightFunction.reflectionForm_im_eq_zero`,
`WeightFunction.pairingForm_expand`,
`WeightFunction.normSq_pairingForm_le`,
`WeightFunction.pairingForm_eq_zero_of_null`,
`WeightFunction.reflectionNullEquivalent_refl`,
`WeightFunction.reflectionNullEquivalent_symm`, and
`WeightFunction.reflectionNullEquivalent_trans`.  These examples spell out the
same hypotheses a mother-side smoke test must provide: `Function.Involutive
theta`, reflection-invariant weights, diagonal nonnegativity, and the relevant
span nonnegativity input.

For the lattice-positive-side inputs to those hypotheses, the oracle checks
`LatticeReflection.DependsOnlyOn.zero`, `.add`, `.smul`, `.neg`, and `.sub`,
plus `LatticeReflection.reflectionPositive_add_smul`,
`LatticeReflection.reflectionPositive_sub_add_smul`, and the concrete
`isingBond_reflectionPositive_sub_add_smul` route with literal
`({true} : Set Bool)` locality hypotheses.

The oracle stops at pairing-form well-definedness.  It does not construct
`GNSReconstruction` or a Hilbert quotient in this repository.

## Suggested next bridge

The next low-risk bridge is a status/checklist item for the mother repository:
copy the oracle shape into THE-ERIKSSON-PROGRAMME as a consumer test from
`import Interfaces`, after deciding where that repo keeps Lean API smoke tests.
