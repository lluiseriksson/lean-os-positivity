import OSPositivity.ReflectionPositivity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The sesquilinear pairing form and the reflection Cauchy-Schwarz inequality

For an unnormalized finite weight, the pairing form
`B(F, G) = Σ w(ω) conj(F(θω)) G(ω)` is sesquilinear, Hermitian when the
weight is reflection invariant, and its diagonal is the `reflectionForm` of
milestone M0.  The main theorem is the Osterwalder-Schrader Cauchy-Schwarz
inequality: reflection positivity on the span of two observables bounds
`|B(F,G)|²` by the product of the diagonal values.  This inequality is what
makes the M2 GNS quotient construction work.

Reference: Glimm and Jaffe, 1981, "Quantum Physics", Theorem 6.2.2 and
Chapter "Regularity and Axioms", pp. 219-233; Osterwalder and Seiler, 1978,
Annals of Physics 110, pp. 440-471.
-/

noncomputable section

namespace OSPositivity

open scoped BigOperators
open scoped ComplexConjugate

universe u

/-- An unnormalized nonnegative weight on a finite configuration space. -/
structure WeightFunction (Omega : Type u) [Fintype Omega] where
  weight : Omega -> Real
  weight_nonneg : ∀ omega, 0 ≤ weight omega

namespace WeightFunction

variable {Omega : Type u} [Fintype Omega]

/-- The (unnormalized) expectation functional of a weight. -/
def toExpectation (w : WeightFunction Omega) : Expectation Omega where
  eval := fun F => Finset.univ.sum fun omega => (w.weight omega : Complex) * F omega

/-- Every finite probability forgets to a weight function. -/
def _root_.OSPositivity.FiniteProbability.toWeightFunction
    (mu : FiniteProbability Omega) : WeightFunction Omega where
  weight := mu.weight
  weight_nonneg := mu.weight_nonnegative

@[simp] theorem _root_.OSPositivity.FiniteProbability.toWeightFunction_toExpectation
    (mu : FiniteProbability Omega) :
    mu.toWeightFunction.toExpectation = mu.toExpectation :=
  rfl

/-- The sesquilinear pairing form `B(F,G) = Σ w conj(F∘θ) G`, conjugate
linear in the first slot. -/
def pairingForm (w : WeightFunction Omega) (theta : Omega -> Omega)
    (F G : Observable Omega) : Complex :=
  Finset.univ.sum fun omega =>
    (w.weight omega : Complex) * conj (F (theta omega)) * G omega

/-- The diagonal of the pairing form is the M0 reflection form. -/
theorem reflectionForm_eq_pairingForm (w : WeightFunction Omega)
    (theta : Omega -> Omega) (F : Observable Omega) :
    Expectation.reflectionForm w.toExpectation theta F = pairingForm w theta F F := by
  show (Finset.univ.sum fun omega =>
      (w.weight omega : Complex) * (conj (F (theta omega)) * F omega))
    = Finset.univ.sum fun omega =>
      (w.weight omega : Complex) * conj (F (theta omega)) * F omega
  exact Finset.sum_congr rfl fun omega _ => by ring

theorem pairingForm_add_left (w : WeightFunction Omega) (theta : Omega -> Omega)
    (F₁ F₂ G : Observable Omega) :
    pairingForm w theta (F₁ + F₂) G
      = pairingForm w theta F₁ G + pairingForm w theta F₂ G := by
  unfold pairingForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun omega _ => ?_
  simp only [Pi.add_apply, map_add]
  ring

theorem pairingForm_add_right (w : WeightFunction Omega) (theta : Omega -> Omega)
    (F G₁ G₂ : Observable Omega) :
    pairingForm w theta F (G₁ + G₂)
      = pairingForm w theta F G₁ + pairingForm w theta F G₂ := by
  unfold pairingForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun omega _ => ?_
  simp only [Pi.add_apply]
  ring

theorem pairingForm_smul_left (w : WeightFunction Omega) (theta : Omega -> Omega)
    (b : Complex) (F G : Observable Omega) :
    pairingForm w theta (b • F) G = conj b * pairingForm w theta F G := by
  unfold pairingForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun omega _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem pairingForm_smul_right (w : WeightFunction Omega) (theta : Omega -> Omega)
    (b : Complex) (F G : Observable Omega) :
    pairingForm w theta F (b • G) = b * pairingForm w theta F G := by
  unfold pairingForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun omega _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Hermitian symmetry of the pairing form for reflection-invariant weights. -/
theorem pairingForm_conj_symm (w : WeightFunction Omega) {theta : Omega -> Omega}
    (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega)
    (F G : Observable Omega) :
    pairingForm w theta G F = conj (pairingForm w theta F G) := by
  unfold pairingForm
  rw [map_sum]
  exact Fintype.sum_equiv ⟨theta, theta, htheta, htheta⟩ _ _ fun omega => by
    simp only [Equiv.coe_fn_mk, map_mul, Complex.conj_conj, Complex.conj_ofReal,
      hw omega, htheta omega]
    ring

/-- Under reflection invariance the reflection form is real. -/
theorem reflectionForm_im_eq_zero (w : WeightFunction Omega)
    {theta : Omega -> Omega} (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega)
    (F : Observable Omega) :
    (Expectation.reflectionForm w.toExpectation theta F).im = 0 := by
  have h := pairingForm_conj_symm w htheta hw F F
  rw [reflectionForm_eq_pairingForm]
  exact Complex.conj_eq_iff_im.mp h.symm

/-- Sesquilinear expansion of the diagonal on the span of two observables. -/
theorem pairingForm_expand (w : WeightFunction Omega) (theta : Omega -> Omega)
    (F G : Observable Omega) (b : Complex) :
    pairingForm w theta (F + b • G) (F + b • G)
      = pairingForm w theta F F + b * pairingForm w theta F G
        + conj b * pairingForm w theta G F
        + conj b * b * pairingForm w theta G G := by
  simp only [pairingForm_add_left, pairingForm_add_right, pairingForm_smul_left,
    pairingForm_smul_right]
  ring

/--
**Reflection Cauchy-Schwarz.**  If the reflection form is nonnegative on the
complex span of `F` and `G` (this is exactly what reflection positivity gives
when the positive-observable class is closed under linear combinations), then
`|B(F,G)|² ≤ Q(F) Q(G)` with `Q` the reflection form.  This is the inequality
that makes the M2 GNS quotient well defined.

Reference: Glimm and Jaffe, 1981, Theorem 6.2.2.
-/
theorem normSq_pairingForm_le (w : WeightFunction Omega)
    {theta : Omega -> Omega} (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega)
    (F G : Observable Omega)
    (hF : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta F))
    (hG : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta G))
    (hspan : ∀ b : Complex,
      ComplexNonnegative
        (Expectation.reflectionForm w.toExpectation theta (F + b • G))) :
    Complex.normSq (pairingForm w theta F G)
      ≤ (Expectation.reflectionForm w.toExpectation theta F).re
        * (Expectation.reflectionForm w.toExpectation theta G).re := by
  classical
  set c : Complex := pairingForm w theta F G with hc
  set n : Real := Complex.normSq c with hn
  have hBGF : pairingForm w theta G F = conj c :=
    pairingForm_conj_symm w htheta hw F G
  have key : ∀ t : Real,
      0 ≤ n * (pairingForm w theta G G).re * (t * t)
        + (2 * n) * t
        + (pairingForm w theta F F).re := by
    intro t
    have h0 := (hspan ((t : Complex) * conj c)).2
    rw [reflectionForm_eq_pairingForm, pairingForm_expand] at h0
    have e1 : (t : Complex) * conj c * c = ((t * n : Real) : Complex) := by
      rw [mul_assoc, mul_comm (conj c) c, Complex.mul_conj]
      push_cast
      ring
    have e2 : conj ((t : Complex) * conj c) * conj c
        = ((t * n : Real) : Complex) := by
      rw [map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_assoc,
        Complex.mul_conj]
      push_cast
      ring
    have e3 : conj ((t : Complex) * conj c) * ((t : Complex) * conj c)
        = ((t ^ 2 * n : Real) : Complex) := by
      rw [map_mul, Complex.conj_conj, Complex.conj_ofReal]
      have hr : (t : Complex) * c * ((t : Complex) * conj c)
          = (t : Complex) * (t : Complex) * (c * conj c) := by ring
      rw [hr, Complex.mul_conj]
      push_cast
      ring
    rw [← hc, hBGF, e1, e2, e3] at h0
    have hQF := reflectionForm_im_eq_zero w htheta hw F
    have hQG := reflectionForm_im_eq_zero w htheta hw G
    rw [reflectionForm_eq_pairingForm] at hQF hQG
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, hQG, mul_zero, sub_zero] at h0
    nlinarith [h0]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  have hQF_eq :
      (Expectation.reflectionForm w.toExpectation theta F).re =
        (pairingForm w theta F F).re := by
    rw [reflectionForm_eq_pairingForm]
  have hQG_eq :
      (Expectation.reflectionForm w.toExpectation theta G).re =
        (pairingForm w theta G G).re := by
    rw [reflectionForm_eq_pairingForm]
  have hF' : 0 ≤ (pairingForm w theta F F).re := by
    simpa [hQF_eq] using hF.2
  have hG' : 0 ≤ (pairingForm w theta G G).re := by
    simpa [hQG_eq] using hG.2
  rw [hQF_eq, hQG_eq]
  rcases (Complex.normSq_nonneg c).lt_or_eq with hpos | hzero
  · have h2 : n * n
        ≤ n * ((pairingForm w theta F F).re * (pairingForm w theta G G).re) := by
      nlinarith [hd]
    have hle : n ≤ (pairingForm w theta F F).re * (pairingForm w theta G G).re :=
      le_of_mul_le_mul_left h2 hpos
    simpa [hn, hc] using hle
  · have hnzero : n = 0 := by
      rw [hn]
      exact hzero.symm
    rw [hnzero]
    exact mul_nonneg hF' hG'

/--
If an observable is null for the reflection form, then its pairing with any
admissible observable vanishes.  This is the first small bridge from reflection
Cauchy-Schwarz toward the GNS nullspace quotient.
-/
theorem pairingForm_eq_zero_of_null (w : WeightFunction Omega)
    {theta : Omega -> Omega} (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega)
    (F G : Observable Omega)
    (hF_zero : Expectation.reflectionForm w.toExpectation theta F = 0)
    (hG : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta G))
    (hspan : ∀ b : Complex,
      ComplexNonnegative
        (Expectation.reflectionForm w.toExpectation theta (F + b • G))) :
    pairingForm w theta F G = 0 := by
  have hF : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta F) := by
    rw [hF_zero]
    exact complexNonnegative_zero
  have hle := normSq_pairingForm_le w htheta hw F G hF hG hspan
  have hle_zero : Complex.normSq (pairingForm w theta F G) ≤ 0 := by
    simpa [hF_zero] using hle
  exact Complex.normSq_eq_zero.mp
    (le_antisymm hle_zero (Complex.normSq_nonneg (pairingForm w theta F G)))

/--
Two observables are equivalent modulo the reflection null relation when their
difference has zero reflection form.  This is only a relation-level predicate;
it does not construct a quotient space.
-/
def ReflectionNullEquivalent (w : WeightFunction Omega) (theta : Omega -> Omega)
    (F G : Observable Omega) : Prop :=
  Expectation.reflectionForm w.toExpectation theta (F - G) = 0

/--
The pairing form is insensitive to replacing its left observable by another
representative modulo the nullspace relation.  This is a relation-level bridge
toward quotient well-definedness; it does not construct the GNS quotient.
-/
theorem pairingForm_respects_null_left (w : WeightFunction Omega)
    {theta : Omega -> Omega} (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega)
    (F₁ F₂ G : Observable Omega)
    (hnull : Expectation.reflectionForm w.toExpectation theta (F₁ - F₂) = 0)
    (hG : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta G))
    (hspan : ∀ b : Complex,
      ComplexNonnegative
        (Expectation.reflectionForm w.toExpectation theta ((F₁ - F₂) + b • G))) :
    pairingForm w theta F₁ G = pairingForm w theta F₂ G := by
  have hzero :
      pairingForm w theta (F₁ - F₂) G = 0 :=
    pairingForm_eq_zero_of_null w htheta hw (F₁ - F₂) G hnull hG hspan
  have hsub :
      pairingForm w theta (F₁ - F₂) G =
        pairingForm w theta F₁ G - pairingForm w theta F₂ G := by
    unfold pairingForm
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun omega _ => ?_
    simp only [Pi.sub_apply, map_sub]
    ring
  have hdiff : pairingForm w theta F₁ G - pairingForm w theta F₂ G = 0 := by
    simpa [hsub] using hzero
  exact sub_eq_zero.mp hdiff

/--
The pairing form is insensitive to replacing its right observable by another
representative modulo the nullspace relation.  This is the symmetric
relation-level bridge toward quotient well-definedness; it does not construct
the GNS quotient.
-/
theorem pairingForm_respects_null_right (w : WeightFunction Omega)
    {theta : Omega -> Omega} (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega)
    (F G₁ G₂ : Observable Omega)
    (hnull : Expectation.reflectionForm w.toExpectation theta (G₁ - G₂) = 0)
    (hF : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta F))
    (hspan : ∀ b : Complex,
      ComplexNonnegative
        (Expectation.reflectionForm w.toExpectation theta ((G₁ - G₂) + b • F))) :
    pairingForm w theta F G₁ = pairingForm w theta F G₂ := by
  have hzero_left :
      pairingForm w theta (G₁ - G₂) F = 0 :=
    pairingForm_eq_zero_of_null w htheta hw (G₁ - G₂) F hnull hF hspan
  have hsym :
      pairingForm w theta (G₁ - G₂) F =
        conj (pairingForm w theta F (G₁ - G₂)) :=
    pairingForm_conj_symm w htheta hw F (G₁ - G₂)
  have hzero_right :
      pairingForm w theta F (G₁ - G₂) = 0 := by
    rw [hsym] at hzero_left
    have h := congrArg conj hzero_left
    simpa using h
  have hsub :
      pairingForm w theta F (G₁ - G₂) =
        pairingForm w theta F G₁ - pairingForm w theta F G₂ := by
    unfold pairingForm
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun omega _ => ?_
    simp only [Pi.sub_apply]
    ring
  have hdiff : pairingForm w theta F G₁ - pairingForm w theta F G₂ = 0 := by
    simpa [hsub] using hzero_right
  exact sub_eq_zero.mp hdiff

/--
The pairing form is insensitive to replacing both observables by null-equivalent
representatives, assuming the explicit span nonnegativity hypotheses needed by
the two one-sided bridges.  This remains a relation-level lemma; it does not
construct the GNS quotient.
-/
theorem pairingForm_respects_null (w : WeightFunction Omega)
    {theta : Omega -> Omega} (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega)
    (F₁ F₂ G₁ G₂ : Observable Omega)
    (hnull_left : Expectation.reflectionForm w.toExpectation theta (F₁ - F₂) = 0)
    (hG₁ : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta G₁))
    (hspan_left : ∀ b : Complex,
      ComplexNonnegative
        (Expectation.reflectionForm w.toExpectation theta ((F₁ - F₂) + b • G₁)))
    (hnull_right : Expectation.reflectionForm w.toExpectation theta (G₁ - G₂) = 0)
    (hF₂ : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta F₂))
    (hspan_right : ∀ b : Complex,
      ComplexNonnegative
        (Expectation.reflectionForm w.toExpectation theta ((G₁ - G₂) + b • F₂))) :
    pairingForm w theta F₁ G₁ = pairingForm w theta F₂ G₂ := by
  calc
    pairingForm w theta F₁ G₁ = pairingForm w theta F₂ G₁ :=
      pairingForm_respects_null_left w htheta hw F₁ F₂ G₁
        hnull_left hG₁ hspan_left
    _ = pairingForm w theta F₂ G₂ :=
      pairingForm_respects_null_right w htheta hw F₂ G₁ G₂
        hnull_right hF₂ hspan_right

/--
The named null-equivalence relation is compatible with the pairing form in both
arguments, under the same explicit positivity hypotheses as
`pairingForm_respects_null`.  This packages quotient well-definedness data only;
it is not a GNS reconstruction theorem.
-/
theorem pairingForm_respects_null_equivalent (w : WeightFunction Omega)
    {theta : Omega -> Omega} (htheta : Function.Involutive theta)
    (hw : ∀ omega, w.weight (theta omega) = w.weight omega)
    (F₁ F₂ G₁ G₂ : Observable Omega)
    (hnull_left : ReflectionNullEquivalent w theta F₁ F₂)
    (hG₁ : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta G₁))
    (hspan_left : ∀ b : Complex,
      ComplexNonnegative
        (Expectation.reflectionForm w.toExpectation theta ((F₁ - F₂) + b • G₁)))
    (hnull_right : ReflectionNullEquivalent w theta G₁ G₂)
    (hF₂ : ComplexNonnegative (Expectation.reflectionForm w.toExpectation theta F₂))
    (hspan_right : ∀ b : Complex,
      ComplexNonnegative
        (Expectation.reflectionForm w.toExpectation theta ((G₁ - G₂) + b • F₂))) :
    pairingForm w theta F₁ G₁ = pairingForm w theta F₂ G₂ :=
  pairingForm_respects_null w htheta hw F₁ F₂ G₁ G₂
    hnull_left hG₁ hspan_left hnull_right hF₂ hspan_right

end WeightFunction

end OSPositivity
