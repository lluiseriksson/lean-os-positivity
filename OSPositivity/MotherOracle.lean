import Interfaces

/-!
# Mother-facing import oracle

This module checks that a downstream consumer can import only `Interfaces` and
call the concrete single-bond null-representative helpers with literal `{true}`
locality hypotheses.  It adds no public theorem; the `example`s are compile-time
oracles for THE-ERIKSSON-PROGRAMME-shaped code.

It also checks the generic null-equivalence API exposed through `Interfaces`.
The examples cover both the direct explicit-hypothesis theorem
`WeightFunction.pairingForm_respects_null_equivalent` and the packaged
`WeightFunction.ReflectionNullContext` route, including the `Set.univ`
constructor.

The first section checks the pairing-form algebra names that a downstream GNS
consumer is likely to use before quotient construction.
-/

noncomputable section

namespace OSPositivity

open scoped ComplexConjugate

universe u

section PairingFormAlgebraOracle

variable {Omega : Type u} [Fintype Omega]
variable {w : WeightFunction Omega} {theta : Omega -> Omega}
variable {F G H : Observable Omega} {b : Complex}

example :
    Expectation.reflectionForm w.toExpectation theta F =
      WeightFunction.pairingForm w theta F F :=
  WeightFunction.reflectionForm_eq_pairingForm w theta F

example :
    WeightFunction.pairingForm w theta (F + G) H =
      WeightFunction.pairingForm w theta F H +
        WeightFunction.pairingForm w theta G H :=
  WeightFunction.pairingForm_add_left w theta F G H

example :
    WeightFunction.pairingForm w theta F (G + H) =
      WeightFunction.pairingForm w theta F G +
        WeightFunction.pairingForm w theta F H :=
  WeightFunction.pairingForm_add_right w theta F G H

example :
    WeightFunction.pairingForm w theta (b • F) G =
      conj b * WeightFunction.pairingForm w theta F G :=
  WeightFunction.pairingForm_smul_left w theta b F G

example :
    WeightFunction.pairingForm w theta F (b • G) =
      b * WeightFunction.pairingForm w theta F G :=
  WeightFunction.pairingForm_smul_right w theta b F G

example
    (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega) :
    WeightFunction.pairingForm w theta G F =
      conj (WeightFunction.pairingForm w theta F G) :=
  WeightFunction.pairingForm_conj_symm w htheta hw F G

end PairingFormAlgebraOracle

section IsingBondTrueSideOracle

variable {S : Type u} [Fintype S] [DecidableEq S]
variable {beta : Real} (hbeta : 0 <= beta)
variable {F1 F2 G1 G2 : LatticeObservable Bool S}

example
    (hF1 : LatticeReflection.DependsOnlyOn ({true} : Set Bool) F1)
    (hF2 : LatticeReflection.DependsOnlyOn ({true} : Set Bool) F2)
    (hG1 : LatticeReflection.DependsOnlyOn ({true} : Set Bool) G1)
    (hnull_left : WeightFunction.ReflectionNullEquivalent
      (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F1 F2) :
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F1 G1
      =
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F2 G1 := by
  exact isingBond_pairingForm_respects_null_left hbeta
    (by simpa [bondReflection] using hF1)
    (by simpa [bondReflection] using hF2)
    (by simpa [bondReflection] using hG1)
    hnull_left

example
    (hF1 : LatticeReflection.DependsOnlyOn ({true} : Set Bool) F1)
    (hG1 : LatticeReflection.DependsOnlyOn ({true} : Set Bool) G1)
    (hG2 : LatticeReflection.DependsOnlyOn ({true} : Set Bool) G2)
    (hnull_right : WeightFunction.ReflectionNullEquivalent
      (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) G1 G2) :
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F1 G1
      =
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F1 G2 := by
  exact isingBond_pairingForm_respects_null_right hbeta
    (by simpa [bondReflection] using hF1)
    (by simpa [bondReflection] using hG1)
    (by simpa [bondReflection] using hG2)
    hnull_right

example
    (hF1 : LatticeReflection.DependsOnlyOn ({true} : Set Bool) F1)
    (hF2 : LatticeReflection.DependsOnlyOn ({true} : Set Bool) F2)
    (hG1 : LatticeReflection.DependsOnlyOn ({true} : Set Bool) G1)
    (hG2 : LatticeReflection.DependsOnlyOn ({true} : Set Bool) G2)
    (hnull_left : WeightFunction.ReflectionNullEquivalent
      (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F1 F2)
    (hnull_right : WeightFunction.ReflectionNullEquivalent
      (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) G1 G2) :
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F1 G1
      =
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F2 G2 := by
  exact isingBond_pairingForm_respects_null_trueSide hbeta hF1 hF2 hG1 hG2
    hnull_left hnull_right

end IsingBondTrueSideOracle

section ReflectionNullContextOracle

variable {Omega : Type u} [Fintype Omega]
variable {w : WeightFunction Omega} {theta : Omega -> Omega}
variable (ctx : WeightFunction.ReflectionNullContext w theta)
variable {F G H F₁ F₂ G₁ G₂ : Observable Omega}

example
    (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega)
    (hRP : Expectation.ReflectionPositive w.toExpectation theta Set.univ) :
    WeightFunction.ReflectionNullContext w theta :=
  WeightFunction.reflectionNullContext_of_reflectionPositive_univ w htheta hw hRP

example :
    WeightFunction.ReflectionNullEquivalent w theta F F :=
  ctx.refl F

example :
    ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta F) :=
  ctx.diagonal_nonnegative F

example
    (hFG : WeightFunction.ReflectionNullEquivalent w theta F G) :
    WeightFunction.ReflectionNullEquivalent w theta G F :=
  ctx.symm F G hFG

example
    (hFG : WeightFunction.ReflectionNullEquivalent w theta F G)
    (hGH : WeightFunction.ReflectionNullEquivalent w theta G H) :
    WeightFunction.ReflectionNullEquivalent w theta F H :=
  ctx.trans F G H hFG hGH

example
    (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega)
    (hleft : WeightFunction.ReflectionNullEquivalent w theta F₁ F₂)
    (hG₁ : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta G₁))
    (hspan_left : ∀ b : Complex,
      ComplexNonnegative
        (Expectation.reflectionForm w.toExpectation theta ((F₁ - F₂) + b • G₁)))
    (hright : WeightFunction.ReflectionNullEquivalent w theta G₁ G₂)
    (hF₂ : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta F₂))
    (hspan_right : ∀ b : Complex,
      ComplexNonnegative
        (Expectation.reflectionForm w.toExpectation theta ((G₁ - G₂) + b • F₂))) :
    WeightFunction.pairingForm w theta F₁ G₁ =
      WeightFunction.pairingForm w theta F₂ G₂ :=
  WeightFunction.pairingForm_respects_null_equivalent w htheta hw
    F₁ F₂ G₁ G₂ hleft hG₁ hspan_left hright hF₂ hspan_right

example
    (hleft : WeightFunction.ReflectionNullEquivalent w theta F₁ F₂) :
    WeightFunction.pairingForm w theta F₁ G₁ =
      WeightFunction.pairingForm w theta F₂ G₁ :=
  ctx.pairingForm_respects_null_left F₁ F₂ G₁ hleft

example
    (hright : WeightFunction.ReflectionNullEquivalent w theta G₁ G₂) :
    WeightFunction.pairingForm w theta F₁ G₁ =
      WeightFunction.pairingForm w theta F₁ G₂ :=
  ctx.pairingForm_respects_null_right F₁ G₁ G₂ hright

example
    (hleft : WeightFunction.ReflectionNullEquivalent w theta F₁ F₂)
    (hright : WeightFunction.ReflectionNullEquivalent w theta G₁ G₂) :
    WeightFunction.pairingForm w theta F₁ G₁ =
      WeightFunction.pairingForm w theta F₂ G₂ :=
  ctx.pairingForm_respects_null F₁ F₂ G₁ G₂ hleft hright

end ReflectionNullContextOracle

end OSPositivity
