import OSPositivity.ReflectionPositivity

/-!
# Transfer-matrix certificates

The external `lean-transfer-matrix` dependency is represented here by a small
certificate interface.  Once that repository is available, these certificates
should be produced by its theorems rather than filled manually.
-/

noncomputable section

namespace OSPositivity

open scoped BigOperators

universe u

/--
A transfer-matrix certificate for reflection positivity of a Euclidean
expectation.

The fields `representsExpectation` and `reflection_positive` are explicit
frontier data until the transfer-matrix repository is imported.

Reference: Glimm and Jaffe, 1981, Chapter "Regularity and Axioms", pp. 219-233,
for the transfer operator viewpoint behind OS reconstruction.
-/
structure TransferMatrixReflectionCertificate
    {Omega : Type u} (E : Expectation Omega) (theta : Omega -> Omega)
    (positiveObservable : Set (Observable Omega)) where
  stateSpace : Type u
  [stateFintype : Fintype stateSpace]
  transferMatrix : stateSpace -> stateSpace -> Real
  transferMatrix_nonnegative : ∀ i j, 0 ≤ transferMatrix i j
  representsExpectation : Prop
  reflection_positive : Expectation.ReflectionPositive E theta positiveObservable

/-- A certificate immediately yields the advertised RP statement. -/
theorem reflectionPositive_of_transferMatrixCertificate
    {Omega : Type u} {E : Expectation Omega} {theta : Omega -> Omega}
    {positiveObservable : Set (Observable Omega)}
    (C : TransferMatrixReflectionCertificate E theta positiveObservable) :
    Expectation.ReflectionPositive E theta positiveObservable :=
  C.reflection_positive

/-- A finite-volume Ising spin is represented as a Boolean value. -/
abbrev IsingSpin := Bool

/--
Statement-first finite ferromagnetic Ising data for M1.

The actual transfer-matrix proof is not assumed globally: it is the explicit
field `transferCertificate`.

Reference: Fröhlich, Israel, Lieb, and Simon, 1978, Communications in
Mathematical Physics 62, pp. 1-34, for lattice reflection positivity methods;
Glimm and Jaffe, 1981, pp. 219-233, for the OS positivity role.
-/
structure FerromagneticIsingData (Site : Type u)
    [Fintype (Configuration Site IsingSpin)] where
  reflection : LatticeReflection Site
  measure : FiniteProbability (Configuration Site IsingSpin)
  ferromagneticCouplings : Prop
  transferCertificate :
    TransferMatrixReflectionCertificate measure.toExpectation
      (reflection.mapConfig : Configuration Site IsingSpin -> Configuration Site IsingSpin)
      (reflection.positiveObservableSet :
        Set (Observable (Configuration Site IsingSpin)))

/-- M1 interface: Ising RP follows from the explicit transfer-matrix certificate. -/
theorem ferromagneticIsing_reflectionPositive
    {Site : Type u} [Fintype (Configuration Site IsingSpin)]
    (D : FerromagneticIsingData Site) :
    D.reflection.ReflectionPositive D.measure :=
  D.transferCertificate.reflection_positive

/--
Statement-first Gaussian-chain data for M1.

The configuration space is intentionally abstract: finite-dimensional Gaussian
chains will instantiate `Config` with a real vector space and provide the
expectation functional.  Reflection positivity is still a certificate field.

Reference: Glimm and Jaffe, 1981, covariance and OS positivity discussion in
the function-space integral chapters, especially pp. 123-143 and pp. 219-233.
-/
structure GaussianChainData (Config : Type u) where
  expectation : Expectation Config
  theta : Config -> Config
  theta_involutive : Function.Involutive theta
  positiveObservable : Set (Observable Config)
  covarianceReflectionPositive : Prop
  transferCertificate :
    TransferMatrixReflectionCertificate expectation theta positiveObservable

/-- M1 interface: Gaussian-chain RP follows from the explicit certificate. -/
theorem gaussianChain_reflectionPositive {Config : Type u}
    (D : GaussianChainData Config) :
    Expectation.ReflectionPositive D.expectation D.theta D.positiveObservable :=
  D.transferCertificate.reflection_positive

end OSPositivity
