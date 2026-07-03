# Mathlib Audit

Audit date: 2026-07-03.

Toolchain inherited from the mother repository:

- Lean: `leanprover/lean4:v4.29.0-rc6`
- Mathlib commit: `07642720480157414db592fa85b626dafb71355b`

## Direct Search Results

Command family used on the pinned Mathlib tree:

```bash
rg -n -i "\b(reflection positivity|reflection positive|ReflectionPositive|Osterwalder|Schrader|Seiler|OS axioms|transfer matrix|transferMatrix|Wilson action|lattice gauge)\b" Mathlib
rg -n -i "\bGNS\b|\bGelfand\b|\bNaimark\b|\bSegal\b" Mathlib
```

Result:

- No direct Mathlib definition was found for Osterwalder-Schrader reflection
  positivity, lattice reflection positivity, Wilson-action RP, or transfer
  matrices in the statistical-mechanics sense.
- Mathlib does contain a C*-algebraic GNS construction:
  `Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`.

## Existing Mathlib Infrastructure To Reuse

| Area | Mathlib files found | Relevance |
|---|---|---|
| Finite sums and finite types | `Mathlib/Data/Fintype/Basic.lean`, `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | Used now for finite probability expectations. |
| Complex conjugation | `Mathlib/Data/Complex/Basic.lean` | Provides `conj` via `ComplexConjugate`; used in the reflected form. |
| Probability and measures | `Mathlib/Probability/ProbabilityMassFunction/*`, `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`, `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean` | Future replacement for the small `FiniteProbability` wrapper once continuous Gaussian chains enter. |
| Hilbert/inner product spaces | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | Used by the GNS and Hamiltonian interfaces. |
| Bounded operators | `Mathlib/Analysis/Normed/Operator/ContinuousLinearMap.lean` | Used for transfer operators and Hamiltonians. |
| Matrix positivity | `Mathlib/LinearAlgebra/Matrix/PosDef.lean`, `Mathlib/LinearAlgebra/SesquilinearForm/Star.lean` | Future route for finite transfer-matrix positivity proofs. |
| C*-algebraic GNS | `Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` | Related but not directly OS reflection-positive quotient construction. |
| Functional calculus log | `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Basic.lean` | Future route for making `H := -log T` concrete. |

## Engineering Decision

This repo defines the OS/RP lattice interface locally because Mathlib does not
currently provide it.  The definitions are intentionally small and use Mathlib
only for generic infrastructure.

Potential upstream candidates after stabilization:

- finite reflection-positive forms over a conjugate-linear involution;
- finite transfer-matrix positivity lemmas using `Matrix.PosSemidef`;
- reusable quotient-by-nullspace constructions for positive semidefinite
  sesquilinear forms, if not already covered by a better Mathlib abstraction.
