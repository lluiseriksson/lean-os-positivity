import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic

/-!
# Lattice reflection positivity: finite and expectation-level interfaces

This file contains the basic definitions used by the public interface.  It is
deliberately statement-first: model-specific positivity proofs are carried as
explicit certificates elsewhere, not postulated as axioms.
-/

noncomputable section

namespace OSPositivity

open scoped BigOperators
open scoped ComplexConjugate

universe u v

/-- Complex-valued observables on a configuration/sample space. -/
abbrev Observable (Omega : Type u) := Omega -> Complex

/-- A complex number which is a nonnegative real, encoded inside `Complex`. -/
def ComplexNonnegative (z : Complex) : Prop :=
  z.im = 0 ∧ 0 ≤ z.re

@[simp]
theorem complexNonnegative_zero : ComplexNonnegative 0 := by
  simp [ComplexNonnegative]

/-- An abstract Euclidean expectation functional on observables. -/
structure Expectation (Omega : Type u) where
  eval : Observable Omega -> Complex

namespace Expectation

instance (Omega : Type u) : CoeFun (Expectation Omega) (fun _ => Observable Omega -> Complex) where
  coe E := E.eval

/-- Reflection form `<Theta F, F>` for a conjugate-linear reflected observable. -/
def reflectionForm (E : Expectation Omega) (theta : Omega -> Omega)
    (F : Observable Omega) : Complex :=
  E fun omega => conj (F (theta omega)) * F omega

/--
Osterwalder-Schrader reflection positivity for an expectation and a chosen
positive-time observable subspace.

Reference: Osterwalder and Seiler, 1978, Annals of Physics 110, pp. 440-471;
Glimm and Jaffe, 1981, Chapter "Regularity and Axioms", pp. 219-233.
-/
def ReflectionPositive (E : Expectation Omega) (theta : Omega -> Omega)
    (positiveObservable : Set (Observable Omega)) : Prop :=
  ∀ F, F ∈ positiveObservable -> ComplexNonnegative (reflectionForm E theta F)

end Expectation

/-- A probability mass function on a finite configuration/sample space. -/
structure FiniteProbability (Omega : Type u) [Fintype Omega] where
  weight : Omega -> Real
  weight_nonnegative : ∀ omega, 0 ≤ weight omega
  total_mass : (Finset.univ.sum fun omega : Omega => weight omega) = 1

namespace FiniteProbability

variable {Omega : Type u} [Fintype Omega]

/-- Finite-volume expectation as a weighted finite sum. -/
def expect (mu : FiniteProbability Omega) (F : Observable Omega) : Complex :=
  Finset.univ.sum fun omega : Omega => (mu.weight omega : Complex) * F omega

@[simp]
theorem expect_zero (mu : FiniteProbability Omega) : mu.expect (fun _ => 0) = 0 := by
  simp [expect]

/-- The expectation functional associated to a finite probability mass. -/
def toExpectation (mu : FiniteProbability Omega) : Expectation Omega where
  eval := mu.expect

/-- Finite-volume reflection positivity, phrased through the abstract interface. -/
def ReflectionPositive (mu : FiniteProbability Omega) (theta : Omega -> Omega)
    (positiveObservable : Set (Observable Omega)) : Prop :=
  Expectation.ReflectionPositive mu.toExpectation theta positiveObservable

end FiniteProbability

/-- A lattice configuration with sites valued in a spin/field type. -/
abbrev Configuration (Site : Type u) (Spin : Type v) := Site -> Spin

/-- Complex-valued observables on lattice configurations. -/
abbrev LatticeObservable (Site : Type u) (Spin : Type v) :=
  Observable (Configuration Site Spin)

/--
A reflection of lattice sites, together with the chosen positive half-lattice.

The fixed hyperplane is represented implicitly as the boundary between
`positiveSide` and its reflected complement.
-/
structure LatticeReflection (Site : Type u) where
  reflect : Site -> Site
  reflect_reflect : ∀ x, reflect (reflect x) = x
  positiveSide : Set Site

namespace LatticeReflection

variable {Site : Type u} {Spin : Type v}

/-- Pull a lattice configuration back by the site reflection. -/
def mapConfig (r : LatticeReflection Site) (sigma : Configuration Site Spin) :
    Configuration Site Spin :=
  fun x => sigma (r.reflect x)

@[simp]
theorem mapConfig_apply (r : LatticeReflection Site) (sigma : Configuration Site Spin)
    (x : Site) : r.mapConfig sigma x = sigma (r.reflect x) :=
  rfl

/-- The induced reflection on configurations is an involution. -/
theorem mapConfig_involutive (r : LatticeReflection Site) :
    Function.Involutive (r.mapConfig : Configuration Site Spin -> Configuration Site Spin) := by
  intro sigma
  funext x
  simp [mapConfig, r.reflect_reflect]

/-- An observable depends only on a chosen set of sites. -/
def DependsOnlyOn (S : Set Site) (F : LatticeObservable Site Spin) : Prop :=
  ∀ sigma tau : Configuration Site Spin,
    (∀ x, x ∈ S -> sigma x = tau x) -> F sigma = F tau

/-- The positive-time observable subspace for this reflection. -/
def positiveObservableSet (r : LatticeReflection Site) : Set (LatticeObservable Site Spin) :=
  {F | DependsOnlyOn r.positiveSide F}

/--
Reflection positivity for a finite lattice probability measure.

Reference: Osterwalder and Seiler, 1978, Annals of Physics 110, pp. 440-471,
definition of lattice reflection positivity for positive-time observables.
-/
def ReflectionPositive [Fintype (Configuration Site Spin)]
    (r : LatticeReflection Site) (mu : FiniteProbability (Configuration Site Spin)) : Prop :=
  FiniteProbability.ReflectionPositive mu
    (r.mapConfig : Configuration Site Spin -> Configuration Site Spin)
    (r.positiveObservableSet : Set (Observable (Configuration Site Spin)))

theorem reflectionPositive_eval [Fintype (Configuration Site Spin)]
    {r : LatticeReflection Site} {mu : FiniteProbability (Configuration Site Spin)}
    (h : r.ReflectionPositive mu) {F : LatticeObservable Site Spin}
    (hF : DependsOnlyOn r.positiveSide F) :
    ComplexNonnegative
      (Expectation.reflectionForm mu.toExpectation
        (r.mapConfig : Configuration Site Spin -> Configuration Site Spin) F) :=
  h F hF

end LatticeReflection

end OSPositivity
