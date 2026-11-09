import SMSFormula.QuadraticPadicCayleyProductRepositoryHaar
import SMSFormula.PadicCayleyTranslatedChartDifferentialLocalConstancy

/-! Relative fiber product in group-Haar densities for the actual p-adic Cayley
product. The repository group Haar in a Cayley chart is the Cayley source
density rho times the repository coordinate measure. Both densities are locally
constant (existing), so on every sufficiently small exact compact open
coordinate ball around the base point the rho_G-weighted image lintegral equals
the rational form ratio times the actual horizontal orbit-relative factor times
the rho_H-weighted source lintegral. Nothing is normalized; no chart, section
or baseline is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Filter
open scoped Matrix.Norms.Operator Topology ENNReal NNReal

namespace Matrix
variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The Cayley source differential density, read on the whole coordinate space
(it agrees definitionally with the repository density on the exact source). -/
def skewAdjointPadicCayleyAmbientDensity (F : Matrix (Fin n) (Fin n) ℚ)
    (y : (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) : ℝ≥0∞ :=
  (skewAdjointPadicCayleyCoordinateJacobianDensityENNReal p n F y)⁻¹

theorem skewAdjointPadicCayleyAmbientDensity_eq (F : Matrix (Fin n) (Fin n) ℚ)
    (X : skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyAmbientDensity p n F X.1 =
      skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F X := rfl

/-- The ambient density is eventually constant near every point of the exact
Cayley source (from the existing local constancy on the source). -/
theorem eventually_skewAdjointPadicCayleyAmbientDensity_eq (F : Matrix (Fin n) (Fin n) ℚ)
    (X : (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    ∀ᶠ y in 𝓝 X, skewAdjointPadicCayleyAmbientDensity p n F y =
      skewAdjointPadicCayleyAmbientDensity p n F X := by
  have hlc := isLocallyConstant_skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F
  have h1 := (IsLocallyConstant.iff_eventually_eq _).mp hlc ⟨X, hX⟩
  rw [nhds_subtype_eq_comap, Filter.eventually_comap] at h1
  filter_upwards [h1, (isOpen_skewAdjointPadicCayleySource F p).mem_nhds hX] with y hy hyS
  exact hy ⟨y, hyS⟩ rfl

theorem skewAdjointPadicCayleyAmbientDensity_ne_top (F : Matrix (Fin n) (Fin n) ℚ)
    (X : skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyAmbientDensity p n F X.1 ≠ ∞ := by
  rw [skewAdjointPadicCayleyAmbientDensity_eq, skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_coe]
  exact ENNReal.coe_ne_top

end Matrix

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]

section GroupDensity

local instance groupDensityPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance groupDensityPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance groupDensityLowerLieIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  Submodule.topologicalAddGroup _
local instance groupDensityLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance groupDensityLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩
local instance groupDensityHigherLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance groupDensityHigherLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩

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

include hs hv in
/-- Relative fiber product in group-Haar densities: on every sufficiently small
exact compact open coordinate ball `U` around `(Y, 0)`, the typed actual
product is injective and, for every `g`, the higher Cayley-density-weighted
lintegral over the image equals the rational form ratio times the actual
horizontal orbit-relative factor times the lower Cayley-density-weighted source
lintegral of `g` composed with the product. -/
theorem lastCayleyProduct_exists_forall_lintegral_image_groupDensity :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      Set.InjOn (W.lastCayleyProductFrameValue a ha p S z v)
        ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
          closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      ∀ g : skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) → ℝ≥0∞,
        ∫⁻ y in W.lastCayleyProductFrameValue a ha p S z v ''
            ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
              closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r),
            skewAdjointPadicCayleyAmbientDensity p (n+1) (W.nonisotropicLastExtension a ha).pairingMatrix y *
              g y ∂(W.lastCayleyProductTargetMeasure a ha p) =
          (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
              lastCoordinateVector
              (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
              (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
                Y hY X hX hproduct (0, v j))‖₊ : ℝ≥0∞) *
            ∫⁻ q in (W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
              skewAdjointPadicCayleyAmbientDensity p n W.pairingMatrix q.1 *
                g (W.lastCayleyProductFrameValue a ha p S z v q)
                ∂(W.lastCayleyProductSourceMeasure p) := by
  set eE := W.lastCayleyProductSourceCoordinates p with heE
  set f := W.lastCayleyProductFrameValue a ha p S z v with hf
  set ρG := skewAdjointPadicCayleyAmbientDensity p (n+1) (W.nonisotropicLastExtension a ha).pairingMatrix
    with hρG
  set ρH := skewAdjointPadicCayleyAmbientDensity p n W.pairingMatrix with hρH
  obtain ⟨δ0, hδ0, hall⟩ := W.lastCayleyProduct_exists_forall_lintegral_image_repository a ha p S dS
    z hSs hSO Y hY X hX hproduct v hs hv
  -- the base value and continuity of the typed product
  obtain ⟨e, -, hef, hbase, -⟩ := W.lastCayleyProduct_exists_localInverse a ha p S dS z hSs hSO Y hY
    X hX hproduct v hs hv
  have hfY : f (Y,0) = X := by rw [← hbase, hef]
  have hfcont : ContinuousAt f (Y,0) :=
    (W.hasStrictFDerivAt_lastCayleyProductFrameValue a ha p S dS z hSs hSO Y hY X hX hproduct
      v).continuousAt
  -- eventual constancy of both densities near the base point
  have hGev : ∀ᶠ q in 𝓝 ((Y,0) : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × (Fin n → ℚ_[p])), ρG (f q) = ρG X := by
    have h := Matrix.eventually_skewAdjointPadicCayleyAmbientDensity_eq p (n+1)
      (W.nonisotropicLastExtension a ha).pairingMatrix X hX
    rw [← hfY] at h ⊢
    exact hfcont.eventually h
  have hHev : ∀ᶠ q in 𝓝 ((Y,0) : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × (Fin n → ℚ_[p])), ρH q.1 = ρH Y :=
    (continuousAt_fst (p := ((Y, 0) : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × (Fin n → ℚ_[p])))).eventually
      (Matrix.eventually_skewAdjointPadicCayleyAmbientDensity_eq p n W.pairingMatrix Y hY)
  have hP := hGev.and hHev
  -- transport the neighbourhood to coordinates
  have hPc : {x | ρG (f (eE.symm x)) = ρG X ∧ ρH (eE.symm x).1 = ρH Y} ∈ 𝓝 (eE (Y,0)) := by
    have hcont : ContinuousAt eE.symm (eE (Y,0)) := eE.symm.continuous.continuousAt
    rw [← eE.symm_apply_apply (Y,0)] at hP
    exact hcont.preimage_mem_nhds hP
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hPc
  refine ⟨min δ0 ε, lt_min hδ0 hε, fun r hr hrδ ↦ ?_⟩
  obtain ⟨hinj, -, hlaw⟩ := hall r hr (hrδ.trans_le (min_le_left _ _))
  refine ⟨hinj, fun g ↦ ?_⟩
  set U := eE ⁻¹' closedBall (eE (Y,0)) r with hU
  have hUm : MeasurableSet U := (isClosed_closedBall.preimage eE.continuous).measurableSet
  have hUP : ∀ q ∈ U, ρG (f q) = ρG X ∧ ρH q.1 = ρH Y := by
    intro q hq
    have hqball : eE q ∈ ball (eE (Y,0)) ε :=
      closedBall_subset_ball (hrδ.trans_le (min_le_right _ _)) hq
    have := hεsub hqball
    simpa only [Set.mem_setOf_eq, ContinuousLinearEquiv.symm_apply_apply] using this
  have hGX : ρG X ≠ ∞ := Matrix.skewAdjointPadicCayleyAmbientDensity_ne_top p (n+1) _ ⟨X, hX⟩
  have hHY : ρH Y ≠ ∞ := Matrix.skewAdjointPadicCayleyAmbientDensity_ne_top p n _ ⟨Y, hY⟩
  have hdens := W.lastCayleyProduct_density a ha p S dS z hSs.hasFDerivAt hSO Y hY X hX hproduct v
  change ρG X * _ = _ * ρH Y * _ at hdens
  rw [hlaw (fun y ↦ ρG y * g y)]
  have hc1 : ∫⁻ q in U, ρG (f q) * g (f q) ∂(W.lastCayleyProductSourceMeasure p) =
      ∫⁻ q in U, ρG X * g (f q) ∂(W.lastCayleyProductSourceMeasure p) :=
    setLIntegral_congr_fun hUm (fun q hq ↦ by rw [(hUP q hq).1])
  have hc2 : ∫⁻ q in U, ρH q.1 * g (f q) ∂(W.lastCayleyProductSourceMeasure p) =
      ∫⁻ q in U, ρH Y * g (f q) ∂(W.lastCayleyProductSourceMeasure p) :=
    setLIntegral_congr_fun hUm (fun q hq ↦ by rw [(hUP q hq).2])
  rw [hc1, hc2, lintegral_const_mul' _ _ hGX, lintegral_const_mul' _ _ hHY]
  calc _ = (ρG X * _) * ∫⁻ q in U, g (f q) ∂(W.lastCayleyProductSourceMeasure p) := by ring
    _ = _ := by rw [hdens]; ring

end GroupDensity

end RationalQuadraticSpaceMatrix
