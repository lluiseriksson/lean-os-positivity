import OSPositivity.PairingForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.BigOperators

/-!
# The single-bond model: reflection positivity ⟺ PSD transfer kernel

The smallest lattice with a reflection: two sites `Bool`, reflection `not`,
positive side `{true}`, and Gibbs weight `k (σ true) (σ false)` for a kernel
`k` on an arbitrary finite spin space.  The main theorems:

* `complexNonnegative_bondForm_of_psd`: a real symmetric PSD kernel makes the
  complex reflection quadratic form nonnegative (realification lemma);
* `bond_reflectionPositive`: PSD ⇒ reflection positivity — the first
  unconditional RP theorem of the programme;
* `psd_of_bond_reflectionPositive`: the converse, so RP across a bond IS
  positive semidefiniteness of the transfer kernel;
* `ferromagneticKernel_psd` and `isingBond_reflectionPositive`: the
  zero-field ferromagnetic Ising/Potts bond (`0 ≤ β`) is reflection positive,
  for every finite spin space.

This is Osterwalder-Seiler's mechanism in miniature: the transfer kernel
across the reflecting bond must be a PSD operator.

Reference: Osterwalder and Seiler, 1978, Annals of Physics 110, pp. 440-471;
Glimm and Jaffe, 1981, Chapter 10 (lattice reflection positivity).
-/

noncomputable section

namespace OSPositivity

open scoped BigOperators
open scoped ComplexConjugate

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v

namespace LatticeReflection

variable {Site : Type u} {Spin : Type v}

/-- The zero observable depends only on any chosen site set. -/
theorem DependsOnlyOn.zero (S : Set Site) :
    DependsOnlyOn S (0 : LatticeObservable Site Spin) := by
  intro sigma tau h
  rfl

/-- Half-space observables are closed under addition. -/
theorem DependsOnlyOn.add {S : Set Site} {F G : LatticeObservable Site Spin}
    (hF : DependsOnlyOn S F) (hG : DependsOnlyOn S G) :
    DependsOnlyOn S (F + G) := by
  intro sigma tau h
  simp only [Pi.add_apply, hF sigma tau h, hG sigma tau h]

/-- Half-space observables are closed under complex scaling. -/
theorem DependsOnlyOn.smul {S : Set Site} {F : LatticeObservable Site Spin}
    (b : Complex) (hF : DependsOnlyOn S F) :
    DependsOnlyOn S (b • F) := by
  intro sigma tau h
  simp only [Pi.smul_apply, hF sigma tau h]

/-- Half-space observables are closed under negation. -/
theorem DependsOnlyOn.neg {S : Set Site} {F : LatticeObservable Site Spin}
    (hF : DependsOnlyOn S F) :
    DependsOnlyOn S (-F) := by
  intro sigma tau h
  simp only [Pi.neg_apply, hF sigma tau h]

/-- Half-space observables are closed under subtraction. -/
theorem DependsOnlyOn.sub {S : Set Site} {F G : LatticeObservable Site Spin}
    (hF : DependsOnlyOn S F) (hG : DependsOnlyOn S G) :
    DependsOnlyOn S (F - G) := by
  intro sigma tau h
  simp only [Pi.sub_apply, hF sigma tau h, hG sigma tau h]

/--
Reflection positivity on a lattice reflection is stable on the complex span of
two positive-side observables.  This packages the locality closure needed by
pairing-form Cauchy-Schwarz hypotheses without constructing quotient data.
-/
theorem reflectionPositive_add_smul [Fintype (Configuration Site Spin)]
    {r : LatticeReflection Site} {mu : FiniteProbability (Configuration Site Spin)}
    (h : r.ReflectionPositive mu) {F G : LatticeObservable Site Spin}
    (hF : DependsOnlyOn r.positiveSide F) (hG : DependsOnlyOn r.positiveSide G)
    (b : Complex) :
    ComplexNonnegative
      (Expectation.reflectionForm mu.toExpectation
        (r.mapConfig : Configuration Site Spin -> Configuration Site Spin)
        (F + b • G)) :=
  h (F + b • G) (DependsOnlyOn.add hF (DependsOnlyOn.smul b hG))

/--
Reflection positivity supplies the span nonnegativity input for a positive-side
observable difference plus a complex multiple of another positive-side
observable.  This is the shape used by one-sided null-representative lemmas.
-/
theorem reflectionPositive_sub_add_smul [Fintype (Configuration Site Spin)]
    {r : LatticeReflection Site} {mu : FiniteProbability (Configuration Site Spin)}
    (h : r.ReflectionPositive mu) {F₁ F₂ G : LatticeObservable Site Spin}
    (hF₁ : DependsOnlyOn r.positiveSide F₁) (hF₂ : DependsOnlyOn r.positiveSide F₂)
    (hG : DependsOnlyOn r.positiveSide G) (b : Complex) :
    ComplexNonnegative
      (Expectation.reflectionForm mu.toExpectation
        (r.mapConfig : Configuration Site Spin -> Configuration Site Spin)
        ((F₁ - F₂) + b • G)) :=
  h ((F₁ - F₂) + b • G)
    (DependsOnlyOn.add (DependsOnlyOn.sub hF₁ hF₂) (DependsOnlyOn.smul b hG))

end LatticeReflection

section BondModel

variable {S : Type u} [Fintype S] [DecidableEq S]

/-- The two-site reflection: sites `Bool`, reflection `not`, positive side
`{true}`. -/
def bondReflection : LatticeReflection Bool where
  reflect := not
  reflect_reflect := Bool.not_not
  positiveSide := {true}

/-- The unnormalized single-bond Gibbs weight of a nonnegative kernel. -/
def bondWeight (k : S -> S -> Real) (hk : ∀ s t, 0 ≤ k s t) :
    WeightFunction (Configuration Bool S) where
  weight := fun sigma => k (sigma true) (sigma false)
  weight_nonneg := fun _ => hk _ _

/-- A `{true}`-local observable factors through the value at the positive
site. -/
theorem eval_of_dependsOnlyOn_true {F : LatticeObservable Bool S}
    (hF : LatticeReflection.DependsOnlyOn ({true} : Set Bool) F)
    (sigma : Configuration Bool S) :
    F sigma = F (fun _ => sigma true) := by
  refine hF sigma (fun _ => sigma true) ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rfl

/-- Real/imaginary computation of the bond quadratic form. -/
theorem bondQuadForm_re (k : S -> S -> Real) (f : S -> Complex) :
    (∑ s, ∑ t, (k s t : Complex) * conj (f t) * f s).re
      = ∑ s, ∑ t, k s t * ((f t).re * (f s).re + (f t).im * (f s).im) := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem bondQuadForm_im (k : S -> S -> Real) (f : S -> Complex) :
    (∑ s, ∑ t, (k s t : Complex) * conj (f t) * f s).im
      = ∑ s, ∑ t, k s t * ((f t).re * (f s).im - (f t).im * (f s).re) := by
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Realification.**  A real symmetric kernel that is PSD on real vectors
makes the complex quadratic form a nonnegative real. -/
theorem complexNonnegative_bondForm_of_psd (k : S -> S -> Real)
    (hsymm : ∀ s t, k s t = k t s)
    (hpsd : ∀ v : S -> Real, 0 ≤ ∑ s, ∑ t, k s t * v t * v s)
    (f : S -> Complex) :
    ComplexNonnegative (∑ s, ∑ t, (k s t : Complex) * conj (f t) * f s) := by
  constructor
  · rw [bondQuadForm_im]
    have hswap : (∑ s, ∑ t, k s t * ((f t).re * (f s).im))
        = ∑ s, ∑ t, k s t * ((f t).im * (f s).re) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      rw [hsymm t s]
      ring
    have hsplit : (∑ s, ∑ t, k s t
          * ((f t).re * (f s).im - (f t).im * (f s).re))
        = (∑ s, ∑ t, k s t * ((f t).re * (f s).im))
          - ∑ s, ∑ t, k s t * ((f t).im * (f s).re) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hsplit, hswap, sub_self]
  · rw [bondQuadForm_re]
    have hre : ∀ v : S -> Real, (∑ s, ∑ t, k s t * (v t * v s))
        = ∑ s, ∑ t, k s t * v t * v s := by
      intro v
      exact Finset.sum_congr rfl fun s _ =>
        Finset.sum_congr rfl fun t _ => by ring
    have hsplit : (∑ s, ∑ t, k s t
          * ((f t).re * (f s).re + (f t).im * (f s).im))
        = (∑ s, ∑ t, k s t * ((f t).re * (f s).re))
          + ∑ s, ∑ t, k s t * ((f t).im * (f s).im) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hsplit, hre (fun s => (f s).re), hre (fun s => (f s).im)]
    exact add_nonneg (hpsd fun s => (f s).re) (hpsd fun s => (f s).im)

/-- The reflection form of a `{true}`-local observable is the bond quadratic
form of its factor. -/
theorem bond_reflectionForm_eq (k : S -> S -> Real) (hk : ∀ s t, 0 ≤ k s t)
    {F : LatticeObservable Bool S}
    (hF : LatticeReflection.DependsOnlyOn ({true} : Set Bool) F) :
    Expectation.reflectionForm (bondWeight k hk).toExpectation
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F
      = ∑ s, ∑ t, (k s t : Complex)
          * conj ((fun s => F fun _ => s) t) * (fun s => F fun _ => s) s := by
  show (∑ sigma : Configuration Bool S,
      (k (sigma true) (sigma false) : Complex)
        * (conj (F (bondReflection.mapConfig sigma)) * F sigma)) = _
  calc
    (∑ sigma : Configuration Bool S,
      (k (sigma true) (sigma false) : Complex)
        * (conj (F (bondReflection.mapConfig sigma)) * F sigma))
        = ∑ p : S × S, (k p.1 p.2 : Complex)
            * conj ((fun s => F fun _ => s) p.2)
            * (fun s => F fun _ => s) p.1 := by
          refine Fintype.sum_equiv
            (⟨fun sigma => (sigma true, sigma false),
              fun p => fun b => bif b then p.1 else p.2,
              fun sigma => by funext b; cases b <;> rfl,
              fun p => rfl⟩ :
                Configuration Bool S ≃ S × S) _ _ fun sigma => ?_
          have h1 : F (bondReflection.mapConfig sigma) = F (fun _ => sigma false) := by
            rw [eval_of_dependsOnlyOn_true hF]
            rfl
          have h2 : F sigma = F (fun _ => sigma true) :=
            eval_of_dependsOnlyOn_true hF sigma
          simp only [Equiv.coe_fn_mk, h1, h2]
          ring
    _ = ∑ s, ∑ t, (k s t : Complex)
          * conj ((fun s => F fun _ => s) t) * (fun s => F fun _ => s) s := by
        simpa only using
          (Fintype.sum_prod_type'
            (fun s t => (k s t : Complex)
              * conj ((fun s => F fun _ => s) t) * (fun s => F fun _ => s) s))

/-- **PSD kernel ⇒ reflection positivity of the bond model.**  The first
unconditional reflection-positivity theorem of the programme. -/
theorem bond_reflectionPositive (k : S -> S -> Real)
    (hk : ∀ s t, 0 ≤ k s t) (hsymm : ∀ s t, k s t = k t s)
    (hpsd : ∀ v : S -> Real, 0 ≤ ∑ s, ∑ t, k s t * v t * v s) :
    Expectation.ReflectionPositive (bondWeight k hk).toExpectation
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S)
      (bondReflection.positiveObservableSet :
        Set (Observable (Configuration Bool S))) := by
  intro F hF
  rw [bond_reflectionForm_eq k hk hF]
  exact complexNonnegative_bondForm_of_psd k hsymm hpsd _

/-- **Converse: reflection positivity of the bond model ⇒ PSD kernel.**
Together with the previous theorem: RP across a bond IS positive
semidefiniteness of the transfer kernel. -/
theorem psd_of_bond_reflectionPositive (k : S -> S -> Real)
    (hk : ∀ s t, 0 ≤ k s t)
    (hRP : Expectation.ReflectionPositive (bondWeight k hk).toExpectation
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S)
      (bondReflection.positiveObservableSet :
        Set (Observable (Configuration Bool S))))
    (v : S -> Real) :
    0 ≤ ∑ s, ∑ t, k s t * v t * v s := by
  have hdep : LatticeReflection.DependsOnlyOn ({true} : Set Bool)
      (fun sigma : Configuration Bool S => ((v (sigma true) : Real) : Complex)) := by
    intro sigma tau h
    have := h true (Set.mem_singleton true)
    simp [this]
  have h0 := hRP _ hdep
  rw [bond_reflectionForm_eq k hk hdep] at h0
  have hre := h0.2
  rw [bondQuadForm_re] at hre
  calc (0 : Real) ≤ ∑ s, ∑ t, k s t
        * (((fun s => ((v s : Real) : Complex)) t).re
            * ((fun s => ((v s : Real) : Complex)) s).re
          + ((fun s => ((v s : Real) : Complex)) t).im
            * ((fun s => ((v s : Real) : Complex)) s).im) := hre
    _ = ∑ s, ∑ t, k s t * v t * v s := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        simp [Complex.ofReal_re, Complex.ofReal_im]
        ring

/-- The zero-field ferromagnetic kernel on an arbitrary finite spin space:
`e^β` on the diagonal, `e^{-β}` off it. -/
def ferromagneticKernel (beta : Real) : S -> S -> Real :=
  fun s t => if s = t then Real.exp beta else Real.exp (-beta)

theorem ferromagneticKernel_nonneg (beta : Real) (s t : S) :
    0 ≤ ferromagneticKernel beta s t := by
  unfold ferromagneticKernel
  split <;> exact (Real.exp_pos _).le

theorem ferromagneticKernel_symm (beta : Real) (s t : S) :
    ferromagneticKernel beta s t = ferromagneticKernel beta t s := by
  unfold ferromagneticKernel
  by_cases h : s = t
  · simp [h]
  · simp [h, Ne.symm h]

/-- Ferromagnetic PSD: `Q(v) = e^{-β} (Σv)² + (e^β - e^{-β}) Σ v²`. -/
theorem ferromagneticKernel_psd {beta : Real} (hbeta : 0 ≤ beta)
    (v : S -> Real) :
    0 ≤ ∑ s, ∑ t, ferromagneticKernel beta s t * v t * v s := by
  have hterm : ∀ s t : S, ferromagneticKernel beta s t * v t * v s
      = Real.exp (-beta) * (v s * v t)
        + (if s = t then (Real.exp beta - Real.exp (-beta)) * (v t * v s)
            else 0) := by
    intro s t
    unfold ferromagneticKernel
    by_cases h : s = t
    · subst h
      simp only [if_true]
      ring_nf
    · simp only [if_neg h]
      ring
  have hsum : (∑ s, ∑ t, ferromagneticKernel beta s t * v t * v s)
      = Real.exp (-beta) * ((∑ s, v s) * (∑ t, v t))
        + (Real.exp beta - Real.exp (-beta)) * ∑ s, v s * v s := by
    calc ∑ s, ∑ t, ferromagneticKernel beta s t * v t * v s
        = ∑ s, ((∑ t, Real.exp (-beta) * (v s * v t))
            + ∑ t, if s = t then (Real.exp beta - Real.exp (-beta)) * (v t * v s)
                else 0) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun t _ => hterm s t
      _ = (∑ s, ∑ t, Real.exp (-beta) * (v s * v t))
          + ∑ s, ∑ t, (if s = t then (Real.exp beta - Real.exp (-beta))
              * (v t * v s) else 0) := Finset.sum_add_distrib
      _ = Real.exp (-beta) * ((∑ s, v s) * (∑ t, v t))
          + (Real.exp beta - Real.exp (-beta)) * ∑ s, v s * v s := by
          congr 1
          · rw [Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.sum_ite_eq]
            simp
  rw [hsum]
  have h1 : 0 ≤ Real.exp (-beta) * ((∑ s, v s) * (∑ t, v t)) :=
    mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _)
  have h2 : 0 ≤ Real.exp beta - Real.exp (-beta) := by
    have := Real.exp_le_exp.mpr (by linarith : -beta ≤ beta)
    linarith
  have h3 : 0 ≤ ∑ s, v s * v s :=
    Finset.sum_nonneg fun s _ => mul_self_nonneg (v s)
  have h4 : 0 ≤ (Real.exp beta - Real.exp (-beta)) * ∑ s, v s * v s :=
    mul_nonneg h2 h3
  linarith

/-- **The ferromagnetic Ising/Potts bond is reflection positive** for every
finite spin space and every coupling `0 ≤ β`.  First model-level RP theorem
of the ecosystem. -/
theorem isingBond_reflectionPositive {beta : Real} (hbeta : 0 ≤ beta) :
    Expectation.ReflectionPositive
      (bondWeight (ferromagneticKernel beta)
        (ferromagneticKernel_nonneg beta)).toExpectation
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S)
      (bondReflection.positiveObservableSet :
        Set (Observable (Configuration Bool S))) :=
  bond_reflectionPositive _ _ (ferromagneticKernel_symm beta)
    (ferromagneticKernel_psd hbeta)

/--
Concrete finite-model span nonnegativity for a null-representative difference
in the ferromagnetic bond model.  This is a direct consumption helper for the
one-sided null bookkeeping shape `((F₁ - F₂) + b • G)`.
-/
theorem isingBond_reflectionPositive_sub_add_smul {beta : Real} (hbeta : 0 ≤ beta)
    {F₁ F₂ G : LatticeObservable Bool S}
    (hF₁ : LatticeReflection.DependsOnlyOn bondReflection.positiveSide F₁)
    (hF₂ : LatticeReflection.DependsOnlyOn bondReflection.positiveSide F₂)
    (hG : LatticeReflection.DependsOnlyOn bondReflection.positiveSide G)
    (b : Complex) :
    ComplexNonnegative
      (Expectation.reflectionForm
        (bondWeight (ferromagneticKernel beta)
          (ferromagneticKernel_nonneg beta)).toExpectation
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S)
        ((F₁ - F₂) + b • G)) :=
  isingBond_reflectionPositive hbeta ((F₁ - F₂) + b • G)
    (LatticeReflection.DependsOnlyOn.add
      (LatticeReflection.DependsOnlyOn.sub hF₁ hF₂)
      (LatticeReflection.DependsOnlyOn.smul b hG))

/--
Concrete left-representative invariance for the ferromagnetic bond-model
pairing form.  This packages the exact positive-side locality and span
nonnegativity inputs needed by the abstract null-bookkeeping lemma, without
constructing quotient data.
-/
theorem isingBond_pairingForm_respects_null_left {beta : Real} (hbeta : 0 ≤ beta)
    {F₁ F₂ G : LatticeObservable Bool S}
    (hF₁ : LatticeReflection.DependsOnlyOn bondReflection.positiveSide F₁)
    (hF₂ : LatticeReflection.DependsOnlyOn bondReflection.positiveSide F₂)
    (hG : LatticeReflection.DependsOnlyOn bondReflection.positiveSide G)
    (hnull : WeightFunction.ReflectionNullEquivalent
      (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₁ F₂) :
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₁ G
      =
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₂ G := by
  let w : WeightFunction (Configuration Bool S) :=
    bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta)
  have htheta :
      Function.Involutive
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) :=
    bondReflection.mapConfig_involutive
  have hw :
      ∀ sigma : Configuration Bool S,
        w.weight (bondReflection.mapConfig sigma) = w.weight sigma := by
    intro sigma
    simp [w, bondWeight, LatticeReflection.mapConfig, bondReflection,
      ferromagneticKernel_symm beta]
  exact WeightFunction.pairingForm_respects_null_left w htheta hw F₁ F₂ G
    hnull (isingBond_reflectionPositive hbeta G hG)
    (isingBond_reflectionPositive_sub_add_smul hbeta hF₁ hF₂ hG)

/--
Concrete right-representative invariance for the ferromagnetic bond-model
pairing form.  This is the symmetric one-sided helper for changing only the
right observable under the named null relation, without constructing quotient
data.
-/
theorem isingBond_pairingForm_respects_null_right {beta : Real} (hbeta : 0 ≤ beta)
    {F G₁ G₂ : LatticeObservable Bool S}
    (hF : LatticeReflection.DependsOnlyOn bondReflection.positiveSide F)
    (hG₁ : LatticeReflection.DependsOnlyOn bondReflection.positiveSide G₁)
    (hG₂ : LatticeReflection.DependsOnlyOn bondReflection.positiveSide G₂)
    (hnull : WeightFunction.ReflectionNullEquivalent
      (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) G₁ G₂) :
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F G₁
      =
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F G₂ := by
  let w : WeightFunction (Configuration Bool S) :=
    bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta)
  have htheta :
      Function.Involutive
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) :=
    bondReflection.mapConfig_involutive
  have hw :
      ∀ sigma : Configuration Bool S,
        w.weight (bondReflection.mapConfig sigma) = w.weight sigma := by
    intro sigma
    simp [w, bondWeight, LatticeReflection.mapConfig, bondReflection,
      ferromagneticKernel_symm beta]
  exact WeightFunction.pairingForm_respects_null_right w htheta hw F G₁ G₂
    hnull (isingBond_reflectionPositive hbeta F hF)
    (isingBond_reflectionPositive_sub_add_smul hbeta hG₁ hG₂ hF)

/--
Concrete two-sided representative invariance for the ferromagnetic bond-model
pairing form.  This composes the left and right one-sided helpers under named
null relations, without constructing quotient data.
-/
theorem isingBond_pairingForm_respects_null {beta : Real} (hbeta : 0 ≤ beta)
    {F₁ F₂ G₁ G₂ : LatticeObservable Bool S}
    (hF₁ : LatticeReflection.DependsOnlyOn bondReflection.positiveSide F₁)
    (hF₂ : LatticeReflection.DependsOnlyOn bondReflection.positiveSide F₂)
    (hG₁ : LatticeReflection.DependsOnlyOn bondReflection.positiveSide G₁)
    (hG₂ : LatticeReflection.DependsOnlyOn bondReflection.positiveSide G₂)
    (hnull_left : WeightFunction.ReflectionNullEquivalent
      (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₁ F₂)
    (hnull_right : WeightFunction.ReflectionNullEquivalent
      (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) G₁ G₂) :
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₁ G₁
      =
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₂ G₂ := by
  calc
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₁ G₁
        =
      WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₂ G₁ :=
        isingBond_pairingForm_respects_null_left hbeta hF₁ hF₂ hG₁ hnull_left
    _ =
      WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₂ G₂ :=
        isingBond_pairingForm_respects_null_right hbeta hF₂ hG₁ hG₂ hnull_right

/--
Mother-facing oracle for the concrete single-bond null-representative
replacement.  It exposes the same two-sided pairing-form equality as
`isingBond_pairingForm_respects_null`, but with the locality hypotheses written
as the literal positive site set `{true}`.
-/
theorem isingBond_pairingForm_respects_null_trueSide {beta : Real} (hbeta : 0 ≤ beta)
    {F₁ F₂ G₁ G₂ : LatticeObservable Bool S}
    (hF₁ : LatticeReflection.DependsOnlyOn ({true} : Set Bool) F₁)
    (hF₂ : LatticeReflection.DependsOnlyOn ({true} : Set Bool) F₂)
    (hG₁ : LatticeReflection.DependsOnlyOn ({true} : Set Bool) G₁)
    (hG₂ : LatticeReflection.DependsOnlyOn ({true} : Set Bool) G₂)
    (hnull_left : WeightFunction.ReflectionNullEquivalent
      (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₁ F₂)
    (hnull_right : WeightFunction.ReflectionNullEquivalent
      (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
      (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) G₁ G₂) :
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₁ G₁
      =
    WeightFunction.pairingForm
        (bondWeight (ferromagneticKernel beta) (ferromagneticKernel_nonneg beta))
        (bondReflection.mapConfig : Configuration Bool S -> Configuration Bool S) F₂ G₂ := by
  exact isingBond_pairingForm_respects_null hbeta
    (by simpa [bondReflection] using hF₁)
    (by simpa [bondReflection] using hF₂)
    (by simpa [bondReflection] using hG₁)
    (by simpa [bondReflection] using hG₂)
    hnull_left hnull_right

end BondModel

end OSPositivity
