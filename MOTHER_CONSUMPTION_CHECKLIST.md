# Mother consumption checklist

Date: 2026-07-07.

This checklist is for `THE-ERIKSSON-PROGRAMME` after it selects a Lean API
smoke-test file.  The intended downstream import is still:

```lean
import Interfaces
```

The source oracle in this repository is `OSPositivity/MotherOracle.lean`.
Nothing below constructs a quotient, `GNSReconstruction`, OS/Wightman
reconstruction, a continuum limit, source construction, or a mass-gap theorem.

## Mirror order

### 1. Pairing-form algebra

Source section: `PairingFormAlgebraOracle`.

Names to mirror:

- `WeightFunction.reflectionForm_eq_pairingForm`
- `WeightFunction.pairingForm_add_left`
- `WeightFunction.pairingForm_add_right`
- `WeightFunction.pairingForm_smul_left`
- `WeightFunction.pairingForm_smul_right`
- `WeightFunction.pairingForm_conj_symm`

Extra hypotheses for conjugate symmetry:

- `Function.Involutive theta`
- `∀ omega, w.weight (theta omega) = w.weight omega`

Use: normalize pairing-form expressions before quotient well-definedness
obligations.

### 2. Inequality and null absorption

Source section: `PairingFormInequalityOracle`.

Names to mirror:

- `WeightFunction.reflectionForm_im_eq_zero`
- `WeightFunction.pairingForm_expand`
- `WeightFunction.normSq_pairingForm_le`
- `WeightFunction.pairingForm_eq_zero_of_null`
- `WeightFunction.ReflectionNullEquivalent`
- `WeightFunction.reflectionNullEquivalent_refl`
- `WeightFunction.reflectionNullEquivalent_symm`
- `WeightFunction.reflectionNullEquivalent_trans`

Main hypotheses:

- `Function.Involutive theta`
- reflection-invariant weights
- diagonal nonnegativity for the observables being paired
- span nonnegativity for `F + b • G` or `(F - G) + b • H`
- named `WeightFunction.ReflectionNullEquivalent` inputs where representatives
  are replaced

Use: check the null-representative bookkeeping shape needed before a Hilbert
quotient exists.

### 3. Positive-side locality and span helpers

Source section: `LatticeReflectionSpanOracle`.

Names to mirror:

- `LatticeReflection.DependsOnlyOn.zero`
- `LatticeReflection.DependsOnlyOn.add`
- `LatticeReflection.DependsOnlyOn.smul`
- `LatticeReflection.DependsOnlyOn.neg`
- `LatticeReflection.DependsOnlyOn.sub`
- `LatticeReflection.reflectionPositive_add_smul`
- `LatticeReflection.reflectionPositive_sub_add_smul`

Main hypotheses:

- `r.ReflectionPositive mu`
- positive-side locality proofs for the observables in the span expression

Use: produce the span nonnegativity hypotheses consumed by the pairing-form
lemmas without restating model-specific reflection positivity each time.

### 4. Concrete single-bond null representatives

Source section: `IsingBondTrueSideOracle`.

Names to mirror:

- `isingBond_reflectionPositive_sub_add_smul`
- `isingBond_pairingForm_respects_null_left`
- `isingBond_pairingForm_respects_null_right`
- `isingBond_pairingForm_respects_null_left_trueSide`
- `isingBond_pairingForm_respects_null_right_trueSide`
- `isingBond_pairingForm_respects_null_trueSide`

Main hypotheses:

- finite spin type: `[Fintype S] [DecidableEq S]`
- ferromagnetic coupling: `hbeta : 0 <= beta`
- literal locality proofs for `({true} : Set Bool)` in mother-facing tests
- named null relations:
  `WeightFunction.ReflectionNullEquivalent ... F1 F2` and/or
  `WeightFunction.ReflectionNullEquivalent ... G1 G2`

Use: finite single-bond smoke tests for representative replacement in the
pairing form.

### 5. Packaged null context

Source section: `ReflectionNullContextOracle`.

Names to mirror:

- `WeightFunction.ReflectionNullContext`
- `WeightFunction.reflectionNullContext_of_reflectionPositive_univ`
- `WeightFunction.ReflectionNullContext.diagonal_nonnegative`
- `WeightFunction.ReflectionNullContext.refl`
- `WeightFunction.ReflectionNullContext.symm`
- `WeightFunction.ReflectionNullContext.trans`
- `WeightFunction.ReflectionNullContext.pairingForm_respects_null_left`
- `WeightFunction.ReflectionNullContext.pairingForm_respects_null_right`
- `WeightFunction.ReflectionNullContext.pairingForm_respects_null`
- `WeightFunction.pairingForm_respects_null_equivalent`

Main hypotheses for the constructor:

- `Function.Involutive theta`
- reflection-invariant weights
- `Expectation.ReflectionPositive w.toExpectation theta Set.univ`

Use: reduce repeated null-bookkeeping hypotheses when a model has full
observable reflection positivity.

## Exact next downstream action

Choose the mother-repository Lean API smoke-test file, then copy one section at
a time from `OSPositivity/MotherOracle.lean`, starting with
`PairingFormAlgebraOracle`.  Keep each copied section as examples from
`import Interfaces`; do not assert quotient construction or reconstruction
there.
