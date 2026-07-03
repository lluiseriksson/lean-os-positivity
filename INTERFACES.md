# Public Interfaces

Downstream import:

```lean
import OSPositivity.Interfaces
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
- The missing `lean-transfer-matrix` package is not imported in `lakefile.lean`
  because no reachable repository was found during setup.  Its future import
  should produce `TransferMatrixReflectionCertificate` values.
