import OSPositivity.ReflectionPositivity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# OS/GNS reconstruction interfaces

This file defines the operator-theoretic target of the program.  It does not
assert reconstruction for free: a reconstruction is explicit data, and mass gap
claims are predicates on the reconstructed Hamiltonian.
-/

noncomputable section

namespace OSPositivity

open scoped ComplexConjugate

universe u v

/--
GNS/OS Hilbert-space reconstruction data for a reflection-positive expectation.

The quotient by the null space is represented by `quotientMap` and its kernel
characterization.  This is a data interface, not a theorem asserting existence.

Reference: Glimm and Jaffe, 1981, Chapter "Regularity and Axioms", pp. 219-233;
Osterwalder and Seiler, 1978, Annals of Physics 110, pp. 440-471.
-/
structure GNSReconstruction {Omega : Type u}
    (E : Expectation Omega) (theta : Omega -> Omega)
    (positiveObservable : Set (Observable Omega)) where
  H : Type v
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace Complex H]
  [completeSpace : CompleteSpace H]
  quotientMap : Observable Omega -> H
  quotientMap_positive_only : ∀ F, F ∉ positiveObservable -> quotientMap F = 0
  kernel_characterization :
    ∀ F, quotientMap F = 0 ↔
      Expectation.reflectionForm E theta F = 0
  inner_quotient :
    ∀ F G,
      inner Complex (quotientMap F) (quotientMap G) =
        E (fun omega => conj (F (theta omega)) * G omega)

/-- A bounded transfer operator produced after OS reconstruction. -/
structure TransferOperator (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] where
  toContinuousLinearMap : H →L[Complex] H
  selfAdjoint_form :
    ∀ x y, inner Complex (toContinuousLinearMap x) y =
      inner Complex x (toContinuousLinearMap y)
  positive_form : ∀ x, 0 ≤ (inner Complex (toContinuousLinearMap x) x).re
  contraction : ∀ x, ‖toContinuousLinearMap x‖ ≤ ‖x‖

/--
The positive Hamiltonian associated to a transfer operator, intended as
`-log T` via functional calculus.

The field `represents_negLog` keeps the functional-calculus identification
honest and explicit.
-/
structure PositiveHamiltonian (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] where
  toContinuousLinearMap : H →L[Complex] H
  vacuum : H
  represents_negLog : Prop
  nonnegative_form : ∀ x, 0 ≤ (inner Complex (toContinuousLinearMap x) x).re

/-- Orthogonality to the vacuum vector. -/
def OrthogonalToVacuum {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (A : PositiveHamiltonian H) (x : H) : Prop :=
  inner Complex A.vacuum x = 0

/--
Operatorial mass gap for a reconstructed Hamiltonian.

`m` is a positive lower bound for the quadratic form of `H` on the subspace
orthogonal to the vacuum.
-/
def HasOperatorMassGap {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (A : PositiveHamiltonian H) (m : Real) : Prop :=
  0 < m ∧
    ∀ x, OrthogonalToVacuum A x ->
      m * ‖x‖ ^ 2 ≤ (inner Complex (A.toContinuousLinearMap x) x).re

theorem HasOperatorMassGap.pos {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    {A : PositiveHamiltonian H} {m : Real}
    (hgap : HasOperatorMassGap A m) : 0 < m :=
  hgap.1

theorem HasOperatorMassGap.quadratic_lower_bound {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    {A : PositiveHamiltonian H} {m : Real}
    (hgap : HasOperatorMassGap A m) {x : H}
    (hx : OrthogonalToVacuum A x) :
    m * ‖x‖ ^ 2 ≤ (inner Complex (A.toContinuousLinearMap x) x).re :=
  hgap.2 x hx

end OSPositivity
