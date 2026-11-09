import SMSFormula.PadicUnitCoordinateHaar
import SMSFormula.QuadraticPadicCayleyProductLocalChange

/-! The integrated local change of variables for the actual p-adic Cayley product,
stated for the repository's skew-adjoint coordinate measures: the higher
coordinate measure on the target and the lower coordinate measure times the
unit-cube Haar on the supplied horizontal coefficients on the source. Both are
unit-cube Haar measures in coordinates, and the index concatenation
preserves unit-cube Haar, so no new Haar normalization enters. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric
open scoped Matrix.Norms.Operator Topology ENNReal NNReal

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]

section RepositoryHaar

local instance repositoryHaarPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance repositoryHaarPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance repositoryHaarSkewMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance repositoryHaarSkewBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance repositoryHaarLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance repositoryHaarLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩
local instance repositoryHaarHigherLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance repositoryHaarHigherLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩

/-- The source measure: coordinate unit-cube Haar (mass one on the lower
lattice times `ℤ_p^n`) read on the lower Lie algebra times the horizontal
coefficients. -/
def lastCayleyProductSourceMeasure :
    Measure (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) :=
  (Padic.unitHaar p
    (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n)).map
    (W.lastCayleyProductSourceCoordinates p).symm

/-- The target measure: coordinate unit-cube Haar read on the higher Lie
algebra. In coordinates it is the pushforward of the repository skew
coordinate measure (`Matrix.map_skewAdjointPadicCoordinateMeasure`). -/
def lastCayleyProductTargetMeasure :
    Measure (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  (Padic.unitHaar p (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra
    (W.nonisotropicLastExtension a ha).pairingMatrix)))).map
    (W.lastCayleyProductTargetCoordinates a ha p).symm

/-- The target measure is characterized exactly as the repository coordinate
measure is: mass one on the higher coordinate lattice (unit cube). -/
theorem lastCayleyProductTargetMeasure_unitCube :
    W.lastCayleyProductTargetMeasure a ha p
      ((W.lastCayleyProductTargetCoordinates a ha p) ⁻¹' closedBall 0 1) = 1 := by
  rw [lastCayleyProductTargetMeasure, Measure.map_apply
    (W.lastCayleyProductTargetCoordinates a ha p).symm.continuous.measurable
    ((W.lastCayleyProductTargetCoordinates a ha p).continuous.measurable
      isClosed_closedBall.measurableSet)]
  rw [← Set.preimage_comp]
  have : (W.lastCayleyProductTargetCoordinates a ha p) ∘ (W.lastCayleyProductTargetCoordinates a ha p).symm
      = id := funext fun x ↦ ContinuousLinearEquiv.apply_symm_apply _ x
  rw [this, Set.preimage_id]
  exact Padic.unitHaar_unitCube p _

/-- The source measure has mass one on the lower lattice times `ℤ_p^n`,
i.e. on the preimage of the unit cube. -/
theorem lastCayleyProductSourceMeasure_unitCube :
    W.lastCayleyProductSourceMeasure p
      ((W.lastCayleyProductSourceCoordinates p) ⁻¹' closedBall 0 1) = 1 := by
  rw [lastCayleyProductSourceMeasure, Measure.map_apply
    (W.lastCayleyProductSourceCoordinates p).symm.continuous.measurable
    ((W.lastCayleyProductSourceCoordinates p).continuous.measurable
      isClosed_closedBall.measurableSet)]
  rw [← Set.preimage_comp]
  have : (W.lastCayleyProductSourceCoordinates p) ∘ (W.lastCayleyProductSourceCoordinates p).symm
      = id := funext fun x ↦ ContinuousLinearEquiv.apply_symm_apply _ x
  rw [this, Set.preimage_id]
  exact Padic.unitHaar_unitCube p _

set_option backward.isDefEq.respectTransparency false in
/-- The target measure is the repository's higher skew-adjoint coordinate measure
(mass one on the higher coordinate lattice), on the same underlying type. -/
theorem lastCayleyProductTargetMeasure_eq_repository :
    W.lastCayleyProductTargetMeasure a ha p =
      skewAdjointPadicCoordinateMeasure (W.nonisotropicLastExtension a ha).pairingMatrix p := by
  rw [lastCayleyProductTargetMeasure,
    ← Matrix.map_skewAdjointPadicCoordinateMeasure (W.nonisotropicLastExtension a ha).pairingMatrix p,
    Measure.map_map (W.lastCayleyProductTargetCoordinates a ha p).symm.continuous.measurable
      (skewAdjointPadicCoordinateEquiv _ p).continuous.measurable]
  have hid : ((W.lastCayleyProductTargetCoordinates a ha p).symm ∘
      (skewAdjointPadicCoordinateEquiv (W.nonisotropicLastExtension a ha).pairingMatrix p)) = id :=
    funext fun x ↦ (W.lastCayleyProductTargetCoordinates a ha p).symm_apply_apply x
  rw [hid, Measure.map_id]


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hSs : HasStrictFDerivAt S dS z)
    (hSO : ∀ᶠ u in 𝓝 z, S u ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)
    (v : Fin n → E)
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0)
    (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0)

set_option maxHeartbeats 800000 in
include hs hv in
/-- Integrated local change of variables in repository measures on every
sufficiently small exact compact open coordinate ball `U` around `(Y, 0)`: the typed actual product
is injective and, for every `g`, the higher skew coordinate lintegral over the
image is the group-form modulus on the actual frame columns times the source
lintegral of `g` composed with the product. -/
theorem lastCayleyProduct_exists_forall_lintegral_image_repository
    : ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → Set.InjOn (W.lastCayleyProductFrameValue a ha p S z v)
        ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
          closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      ContinuousOn (W.lastCayleyProductFrameValue a ha p S z v)
        ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
          closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      ∀ g : skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) → ℝ≥0∞,
        ∫⁻ y in W.lastCayleyProductFrameValue a ha p S z v ''
            ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
              closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r),
            g y ∂(W.lastCayleyProductTargetMeasure a ha p) =
          (‖W.lastOrbitGroupForm a ha ℚ_[p]
            (Sum.elim (fun i ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt
                hSO Y hY X hX hproduct (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i, 0))
              (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
                Y hY X hX hproduct (0, v j)))‖₊ : ℝ≥0∞) *
            ∫⁻ q in (W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
              g (W.lastCayleyProductFrameValue a ha p S z v q) ∂(W.lastCayleyProductSourceMeasure p) := by
  set eE := W.lastCayleyProductSourceCoordinates p with heE
  set eF := W.lastCayleyProductTargetCoordinates a ha p with heF
  set f := W.lastCayleyProductFrameValue a ha p S z v with hf
  have hR : (Padic.unitHaar p _).map (W.lastCayleyProductIndexCoordinates a ha p) =
      Padic.unitHaar p _ := Padic.map_funCongrLeft_unitHaar (W.lastOrbitIndexEquiv a ha)
  obtain ⟨δ, hδ, hall⟩ := W.lastCayleyProduct_exists_forall_lintegral_image_groupForm a ha p S dS
    z hSs hSO Y hY X hX hproduct v hs hv (Padic.unitHaar p _)
  refine ⟨δ, hδ, fun r hr hrδ ↦ ?_⟩
  obtain ⟨-, hinj, hcontG, h⟩ := hall r hr hrδ
  set B := closedBall (eE (Y,0)) r with hB
  set U := eE ⁻¹' B with hU
  let mE := eE.symm.toHomeomorph.toMeasurableEquiv
  let mF := eF.symm.toHomeomorph.toMeasurableEquiv
  have hG : ∀ x, W.lastCayleyProductCoordinateValue a ha p S z v x = eF (f (eE.symm x)) :=
    fun _ ↦ rfl
  have hGimage : W.lastCayleyProductCoordinateValue a ha p S z v '' B = eF '' (f '' U) := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨f (eE.symm x), ⟨eE.symm x, ?_, rfl⟩, (hG x).symm⟩
      change eE (eE.symm x) ∈ B
      rwa [ContinuousLinearEquiv.apply_symm_apply]
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨eE q, hq, by rw [hG, ContinuousLinearEquiv.symm_apply_apply]⟩
  refine ⟨?_, ?_, fun g ↦ ?_⟩
  · intro q hq q' hq' hqq
    have h1 : W.lastCayleyProductCoordinateValue a ha p S z v (eE q) =
        W.lastCayleyProductCoordinateValue a ha p S z v (eE q') := by
      rw [hG, hG, ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply,
        hqq]
    exact eE.injective (hinj hq hq' h1)
  · have hc : ContinuousOn (fun q ↦ eF.symm (W.lastCayleyProductCoordinateValue a ha p S z v (eE q))) U :=
      eF.symm.continuous.comp_continuousOn
        (hcontG.comp eE.continuous.continuousOn (fun q hq ↦ hq))
    refine hc.congr (fun q _ ↦ ?_)
    simp only [hG, ContinuousLinearEquiv.symm_apply_apply]
  · have hmain := h (g ∘ eF.symm)
    rw [hR, hGimage] at hmain
    have hL : ∫⁻ y in f '' U, g y ∂(W.lastCayleyProductTargetMeasure a ha p) =
        ∫⁻ y in eF '' (f '' U), (g ∘ eF.symm) y ∂(Padic.unitHaar p _) := by
      change ∫⁻ y in f '' U, g y ∂((Padic.unitHaar p _).map mF) = _
      rw [mF.restrict_map, lintegral_map_equiv _ mF]
      have hpre : mF ⁻¹' (f '' U) = eF '' (f '' U) := by
        ext y
        change eF.symm y ∈ f '' U ↔ y ∈ eF '' (f '' U)
        constructor
        · intro hy; exact ⟨eF.symm y, hy, eF.apply_symm_apply y⟩
        · rintro ⟨w, hw, rfl⟩; rwa [eF.symm_apply_apply]
      rw [hpre]
      rfl
    have hRside : ∫⁻ q in U, g (f q) ∂(W.lastCayleyProductSourceMeasure p) =
        ∫⁻ x in B, (g ∘ eF.symm) (W.lastCayleyProductCoordinateValue a ha p S z v x)
          ∂(Padic.unitHaar p _) := by
      change ∫⁻ q in U, g (f q) ∂((Padic.unitHaar p _).map mE) = _
      rw [mE.restrict_map, lintegral_map_equiv _ mE]
      have hpre : mE ⁻¹' U = B := by
        ext x
        change eE (eE.symm x) ∈ B ↔ x ∈ B
        rw [ContinuousLinearEquiv.apply_symm_apply]
      rw [hpre]
      congr 1
      funext x
      change g (f (eE.symm x)) = g (eF.symm (W.lastCayleyProductCoordinateValue a ha p S z v x))
      rw [hG, ContinuousLinearEquiv.symm_apply_apply]
    rw [hL, hRside]
    exact hmain

include hs hv in
/-- Integrated local change of variables in repository measures: on an exact
compact open coordinate ball `U` around `(Y, 0)`, the typed actual product
is injective and, for every `g`, the higher repository-coordinate lintegral over
the image is the group-form modulus times the source lintegral. -/
theorem lastCayleyProduct_exists_lintegral_image_repository
    : ∃ r > 0, Set.InjOn (W.lastCayleyProductFrameValue a ha p S z v)
        ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
          closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      ∀ g : skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) → ℝ≥0∞,
        ∫⁻ y in W.lastCayleyProductFrameValue a ha p S z v ''
            ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
              closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r),
            g y ∂(W.lastCayleyProductTargetMeasure a ha p) =
          (‖W.lastOrbitGroupForm a ha ℚ_[p]
            (Sum.elim (fun i ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt
                hSO Y hY X hX hproduct (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i, 0))
              (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
                Y hY X hX hproduct (0, v j)))‖₊ : ℝ≥0∞) *
            ∫⁻ q in (W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
              g (W.lastCayleyProductFrameValue a ha p S z v q) ∂(W.lastCayleyProductSourceMeasure p) := by
  obtain ⟨δ, hδ, h⟩ := W.lastCayleyProduct_exists_forall_lintegral_image_repository a ha p S dS z
    hSs hSO Y hY X hX hproduct v hs hv
  obtain ⟨h1, -, h3⟩ := h _ (half_pos hδ) (half_lt_self hδ)
  exact ⟨δ / 2, half_pos hδ, h1, h3⟩

end RepositoryHaar

end RationalQuadraticSpaceMatrix
