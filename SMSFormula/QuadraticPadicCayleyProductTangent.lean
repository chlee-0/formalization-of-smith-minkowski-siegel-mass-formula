import SMSFormula.QuadraticPadicCayleyProductDifferential

/-! Intrinsic tangency of the actual product derivative for a supplied locally
SO-valued left factor. Differentiate the inverse-Cayley skew equation;
no tangent membership or horizontal lifting operator is assumed. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice
open scoped Matrix.Norms.Operator Topology

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]

/-- A derivative of an inverse-Cayley coordinate curve is intrinsically
skew-adjoint when the underlying matrices are locally special orthogonal. -/
theorem inverseCayley_derivative_mem_skew
    (g : E → Matrix ι ι ℚ_[p]) (D : E →L[ℚ_[p]] Matrix ι ι ℚ_[p]) (z : E)
    (hd : HasFDerivAt (fun u ↦ padicCayleyInverseMatrix p (g u)) D z)
    (hg : ∀ᶠ u in 𝓝 z, g u ∈ specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p])) ∧
      g u ∈ padicCayleyInverseDomain p) (v : E) :
    D v ∈ (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  let L := skewAdjointOperatorContinuousLinearMap (F.map (algebraMap ℚ ℚ_[p]))
  have hz : (fun u ↦ L (padicCayleyInverseMatrix p (g u))) =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [hg] with u hu
    exact skewAdjointOperator_padicCayleyInverseMatrix_eq_zero F p ⟨g u,hu.1⟩ hu.2
  have he : L.comp D = 0 :=
    (L.hasFDerivAt.comp z hd).unique ((hasFDerivAt_const (0 : Matrix ι ι ℚ_[p]) z).congr_of_eventuallyEq hz)
  apply (mem_ker_skewAdjointOperator_iff _ _).mp
  exact congrArg (fun T : E →L[ℚ_[p]] Matrix ι ι ℚ_[p] ↦ T v) he
/-- The ambient forward differential is also a right inverse of the
inverse differential, by finite dimensionality. -/
theorem cayleyForwardDerivative_inverseDerivative (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) (A : Matrix ι ι ℚ_[p]) :
    padicCayleyForwardDerivative p X
      (padicCayleyInverseDerivative p (padicCayleyForwardMatrix p X) A) = A := by
  have h := padicCayleyInverseDerivative_comp_forwardDerivative p X hX
  have hl := congrArg ContinuousLinearMap.toLinearMap h
  change (padicCayleyInverseDerivative p (padicCayleyForwardMatrix p X)).toLinearMap *
    (padicCayleyForwardDerivative p X).toLinearMap = 1 at hl
  have hr := mul_eq_one_symm hl
  exact congrArg (fun L : Module.End ℚ_[p] (Matrix ι ι ℚ_[p]) ↦ L A) hr

end Matrix

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hS : HasFDerivAt S dS z)
    (hSO : ∀ᶠ u in 𝓝 z, S u ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)

local instance lastProductTangentSkewLiteralIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Submodule.topologicalAddGroup _

local instance lastProductTangentSkewLiteralContinuousAdd :
    ContinuousAdd
      (skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  (Submodule.topologicalAddGroup _).toContinuousAdd

set_option backward.isDefEq.respectTransparency false in
include hS hSO hY hX hproduct in
/-- Near the base point the actual product stays special orthogonal and in
the inverse Cayley domain. Only local SO-values of the supplied factor,
openness of the sources and the product equation are used. -/
theorem lastCayleyProduct_eventually_specialOrthogonal :
    ∀ᶠ q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × E in
      𝓝 (Y,z),
      S q.2 * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1) ∈
          specialOrthogonalMatrixSet
            ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ∧
        S q.2 * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1) ∈
          padicCayleyInverseDomain p := by
  let V := W.nonisotropicLastExtension a ha
  let B := fun Z : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ↦
    fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Z)
  let g := fun q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × E ↦
    S q.2 * B q.1
  have hB : ContinuousAt B Y := (W.hasFDerivAt_lastCayleyLowerMatrix a ha p Y hY).continuousAt
  have hB' : ContinuousAt (fun q : _ × E ↦ B q.1) (Y,z) :=
    ContinuousAt.comp (g := B) (f := Prod.fst) hB continuousAt_fst
  have hc : ContinuousAt g (Y,z) :=
    (hS.continuousAt.comp (f := Prod.snd) continuousAt_snd).mul hB'
  have hi : g (Y,z) ∈ padicCayleyInverseDomain p := by
    change S z * B Y ∈ _
    rw [show B Y = fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) from rfl,
      hproduct]
    exact padicCayleyForwardMatrix_mem_inverseDomain p X.1 hX
  have he := (isOpen_padicCayleyInverseDomain p).mem_nhds hi
  have hy := (isOpen_skewAdjointPadicCayleySource W.pairingMatrix p).mem_nhds hY
  filter_upwards [hc he, continuousAt_fst hy, continuousAt_snd hSO] with q hq hqY hqS
  refine ⟨?_,hq⟩
  have hb := (skewAdjointPadicCayleySpecialOrthogonal V.pairingMatrix p V.form_det_ne_zero
    ⟨W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] q.1,
      (W.lastCayley_embedded_source_iff a ha p q.1).mpr hqY⟩).property
  change skewAdjointPadicCayleyForwardMatrix V.pairingMatrix p
    (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] q.1) ∈ _ at hb
  rw [W.lastCayley_embedded_forward a ha p q.1 hqY] at hb
  constructor
  · apply (formPreservingConstraint_eq_zero_iff _ _).mpr
    have hs := (formPreservingConstraint_eq_zero_iff _ _).mp hqS.1
    have hb' := (formPreservingConstraint_eq_zero_iff _ _).mp hb.1
    change (S q.2 * B q.1)ᵀ * _ * (S q.2 * B q.1) = _
    rw [Matrix.transpose_mul]
    calc
      (B q.1)ᵀ * (S q.2)ᵀ * _ * (S q.2 * B q.1) =
        (B q.1)ᵀ * ((S q.2)ᵀ * V.specialOrthogonalMappedFormMatrix ℚ_[p] * S q.2) * B q.1 := by
          simp only [Matrix.mul_assoc]
          rfl
      _ = _ := by rw [hs]; exact hb'
  · change (S q.2 * B q.1).det = 1
    rw [Matrix.det_mul, hqS.2, hb.2, one_mul]

include hS hSO hY hX hproduct in
/-- The full product derivative lands in the intrinsic Lie algebra.
The locally SO-valued hypothesis concerns only the supplied left factor. -/
theorem lastCayleyProductDerivative_mem_skew
    (v : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × E) :
    W.lastCayleyProductDerivative a ha p (S z) dS Y v ∈
      (skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])).toSubmodule :=
  inverseCayley_derivative_mem_skew (W.nonisotropicLastExtension a ha).pairingMatrix p _ _ (Y,z)
    (W.hasFDerivAt_lastCayleyProduct a ha p S dS z hS Y hY X hX hproduct)
    (W.lastCayleyProduct_eventually_specialOrthogonal a ha p S dS z hS hSO Y hY X hX hproduct) v

/-- Restriction of the computed derivative, using proved tangency. This is
not a new coordinate map, chart, section or choice of horizontal lifts. -/
def lastCayleyProductIntrinsicDerivative :
    (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × E) →L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  (W.lastCayleyProductDerivative a ha p (S z) dS Y).codRestrict _
    (W.lastCayleyProductDerivative_mem_skew a ha p S dS z hS hSO Y hY X hX hproduct)

/-- The intrinsic vertical columns are the already identified full frame. -/
theorem lastCayleyProductIntrinsicDerivative_vertical
    (H : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :
    W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct (H,0) =
      skewAdjointPadicCayleyLeftTrivializedInverse
        (W.nonisotropicLastExtension a ha).pairingMatrix p X
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p]
          (skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p Y hY H)) := by
  apply Subtype.ext
  exact W.lastCayleyProductDerivative_vertical_eq_frame a ha p (S z) dS Y H hY X hX hproduct

/-- The actual horizontal orbit differential is exactly dS(v) applied to the
fixed vector. The lower factor fixes this vector; no lift is substituted. -/
theorem lastCayleyProductIntrinsicDerivative_orbit_horizontal (v : E) :
    (W.nonisotropicLastExtension a ha).cayleyOrbitDerivative p X lastCoordinateVector
      (W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct (0,v)) =
      dS v *ᵥ lastCoordinateVector := by
  change (padicCayleyForwardDerivative p X.1
    (W.lastCayleyProductDerivative a ha p (S z) dS Y (0,v))) *ᵥ lastCoordinateVector = _
  rw [W.lastCayleyProductDerivative_horizontal, hproduct]
  change (padicCayleyForwardDerivative p X.1
    (padicCayleyInverseDerivative p (padicCayleyForwardMatrix p X.1)
      (dS v * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y)))) *ᵥ _ = _
  rw [cayleyForwardDerivative_inverseDerivative p X.1 hX]
  rw [← Matrix.mulVec_mulVec, ← W.lastCayley_embedded_forward a ha p Y hY,
    W.lastCayley_embedded_fixes a ha p Y ((W.lastCayley_embedded_source_iff a ha p Y).mpr hY)]

end RationalQuadraticSpaceMatrix
