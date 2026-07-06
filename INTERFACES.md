# Public Interfaces

Downstream import:

```lean
import Interfaces
```

This file is the breaking-change boundary.  Any change to the names or argument
order below is a breaking change for the mother repository.

## Reflection Positivity

- `Observable (Omega : Type u) := Omega -> Complex`
- `ComplexNonnegative (z : Complex) : Prop`
- `Expectation (Omega : Type u)`
- `Expectation.reflectionForm (E : Expectation Omega) (theta : Omega -> Omega)
  (F : Observable Omega) : Complex`
- `Expectation.ReflectionPositive (E : Expectation Omega)
  (theta : Omega -> Omega) (positiveObservable : Set (Observable Omega)) : Prop`
- `FiniteProbability (Omega : Type u) [Fintype Omega]`
- `FiniteProbability.expect`
- `FiniteProbability.toExpectation`
- `FiniteProbability.ReflectionPositive`
- `Configuration (Site Spin)`
- `LatticeObservable (Site Spin)`
- `LatticeReflection (Site)`
- `LatticeReflection.DependsOnlyOn`
- `LatticeReflection.positiveObservableSet`
- `LatticeReflection.ReflectionPositive`

## Pairing Form and Bond Model

- `WeightFunction`
- `FiniteProbability.toWeightFunction`
- `WeightFunction.toExpectation`
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

## Transfer-Matrix Layer

- `TransferMatrixReflectionCertificate`
- `reflectionPositive_of_transferMatrixCertificate`
- `IsingSpin`
- `FerromagneticIsingData`
- `ferromagneticIsing_reflectionPositive`
- `GaussianChainData`
- `gaussianChain_reflectionPositive`

## OS/GNS and Mass Gap

- `GNSReconstruction`
- `TransferOperator`
- `PositiveHamiltonian`
- `OrthogonalToVacuum`
- `HasOperatorMassGap`
- `HasOperatorMassGap.pos`
- `HasOperatorMassGap.quadratic_lower_bound`

## Wilson Gauge Interface

- `WilsonGaugeData`
- `WilsonReflectionPositive`
- `WilsonRPCertificate`
- `rpWilson_of_certificate`
- `WilsonOSMassGapPackage`

## Compatibility Notes

- The Wilson interface is intentionally finite-volume and lattice-only.
- `measure_is_wilson_gibbs` is a `Prop` field, so downstream code can later
  replace it by a theorem without changing the consumer theorem shape.
- `PositiveHamiltonian.represents_negLog` is deliberately explicit.  A future
  implementation may refine it to a concrete continuous-functional-calculus
  statement; that will be a breaking change unless provided as an additional
  theorem.
- The pairing-form and bond-model theorem layers are additive exports through
  `Interfaces.lean`; they do not change the argument order or meaning of the
  original M0/M1/M2/M3 interface declarations.
- `WeightFunction.ReflectionNullEquivalent` is a relation-level predicate for
  null representatives.  It has elementary `refl`, `symm`, and explicit-
  hypothesis `trans` facts, but it does not construct the quotient or a
  `GNSReconstruction`; it only names the hypothesis consumed by
  `WeightFunction.pairingForm_respects_null_equivalent`.
- `WeightFunction.ReflectionNullContext` packages fixed reflection-invariance
  and span-positivity hypotheses for relation-level null bookkeeping.  Its
  methods are wrappers around the existing null-equivalence and pairing-form
  lemmas; they do not construct quotient data.
- `WeightFunction.reflectionNullContext_of_reflectionPositive_univ` builds that
  packaged context from `Expectation.ReflectionPositive ... Set.univ`, for
  finite models where the full observable class is admissible.
- `WeightFunction.ReflectionNullContext.pairingForm_respects_null_left` and
  `.pairingForm_respects_null_right` are one-sided context wrappers for changing
  only the left or right null representative.
- `LatticeReflection.DependsOnlyOn.zero`, `.neg`, and `.sub` are additive
  closure helpers for positive-side observables; they support nullspace
  bookkeeping over differences without changing existing argument order.
- `LatticeReflection.reflectionPositive_add_smul` packages the common span
  nonnegativity call for two positive-side observables under an existing
  lattice reflection-positivity hypothesis; it is a helper for pairing-form
  hypotheses, not a reconstruction theorem.
- `LatticeReflection.reflectionPositive_sub_add_smul` gives the same
  nonnegativity input for `(F₁ - F₂) + b • G`, the exact shape consumed by
  one-sided null-representative lemmas.
- `isingBond_reflectionPositive_sub_add_smul` is the concrete ferromagnetic
  bond-model instance of that null-difference span shape for `{true}`-local
  observables.
- `isingBond_pairingForm_respects_null_left` packages the concrete
  ferromagnetic bond-model inputs needed to replace the left representative in
  the pairing form under a named null relation.
- `isingBond_pairingForm_respects_null_right` is the symmetric concrete helper
  for replacing only the right representative under the same positive-side
  locality and named null-relation hypotheses.
- `isingBond_pairingForm_respects_null` composes the concrete left and right
  helpers to replace both representatives under two named null relations.
- The missing `lean-transfer-matrix` package is not imported in `lakefile.lean`
  because no reachable repository was found during setup.  Its future import
  should produce `TransferMatrixReflectionCertificate` values.
- `OSPositivity.Interfaces` remains as an implementation-side aggregator, but
  the stable contract requested by the ecosystem prompt is the root
  `Interfaces.lean` module.
