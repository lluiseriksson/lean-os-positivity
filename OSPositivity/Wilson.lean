import OSPositivity.GNS
import OSPositivity.TransferMatrix

/-!
# Wilson lattice gauge reflection-positivity interface

The Wilson-action theorem is exposed as a precise interface for downstream
repositories.  The proof is deliberately not faked: RP for Wilson gauge theory
is an explicit field of `WilsonRPCertificate` until formalized.
-/

noncomputable section

namespace OSPositivity

universe u

/--
Finite lattice gauge data for the Wilson-action reflection-positivity target.

`Config` is the finite space of link configurations.  The action is recorded
separately from the already-normalized probability mass so that future imports
can prove the measure is the Wilson Gibbs measure.
-/
structure WilsonGaugeData (Config : Type u) [Fintype Config] where
  theta : Config -> Config
  theta_involutive : Function.Involutive theta
  positiveObservable : Set (Observable Config)
  wilsonAction : Config -> Real
  beta : Real
  measure : FiniteProbability Config
  measure_is_wilson_gibbs : Prop

/--
Reflection positivity of the Wilson lattice gauge measure.

Reference: Osterwalder and Seiler, 1978, Annals of Physics 110, pp. 440-471,
Theorem/positivity result for Wilson lattice gauge actions.
-/
def WilsonReflectionPositive {Config : Type u} [Fintype Config]
    (W : WilsonGaugeData Config) : Prop :=
  FiniteProbability.ReflectionPositive W.measure W.theta W.positiveObservable

/--
Certificate for Wilson reflection positivity.  This is the M3 statements-first
frontier: downstream code must pass the certificate explicitly until the proof is
formalized.
-/
structure WilsonRPCertificate {Config : Type u} [Fintype Config]
    (W : WilsonGaugeData Config) where
  rp_wilson : WilsonReflectionPositive W

/-- Public theorem shape consumed by the mother repository. -/
theorem rpWilson_of_certificate {Config : Type u} [Fintype Config]
    (W : WilsonGaugeData Config) (C : WilsonRPCertificate W) :
    WilsonReflectionPositive W :=
  C.rp_wilson

/--
Final lattice OS target exposed by this repository: Wilson RP, a reconstructed
positive Hamiltonian, and an operatorial mass gap predicate.
-/
structure WilsonOSMassGapPackage {Config : Type u} [Fintype Config]
    (W : WilsonGaugeData Config) where
  rpCertificate : WilsonRPCertificate W
  H : Type u
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace Complex H]
  transfer : TransferOperator H
  hamiltonian : PositiveHamiltonian H
  massGap : Real
  hasMassGap : HasOperatorMassGap hamiltonian massGap

end OSPositivity
