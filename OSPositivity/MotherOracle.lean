import Interfaces

/-!
# Mother-facing import oracle

This module checks that a downstream consumer can import only `Interfaces` and
call the concrete single-bond null-representative helpers with literal `{true}`
locality hypotheses.  It adds no public theorem; the `example`s are compile-time
oracles for THE-ERIKSSON-PROGRAMME-shaped code.
-/

noncomputable section

namespace OSPositivity

universe u

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

end OSPositivity
