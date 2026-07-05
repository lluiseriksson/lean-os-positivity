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
- `WeightFunction.ReflectionNullContext.diagonal_nonnegative`
- `WeightFunction.ReflectionNullContext.trans`
- `WeightFunction.ReflectionNullContext.pairingForm_respects_null`
- `LatticeReflection.DependsOnlyOn.add`
- `LatticeReflection.DependsOnlyOn.smul`
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
- The missing `lean-transfer-matrix` package is not imported in `lakefile.lean`
  because no reachable repository was found during setup.  Its future import
  should produce `TransferMatrixReflectionCertificate` values.
- `OSPositivity.Interfaces` remains as an implementation-side aggregator, but
  the stable contract requested by the ecosystem prompt is the root
  `Interfaces.lean` module.
