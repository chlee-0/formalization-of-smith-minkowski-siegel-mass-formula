import SMSFormula.QuadraticPadicCayleyHorizontalShell

/-! Local relative fiber-product volume identity for tests depending only on the
orbit point. For every sufficiently small exact compact open coordinate ball
(a rectangle: lower coordinate ball × horizontal ball), the repository higher
group-Haar integral of g(lower coordinates of h·x_old) over the Cayley image
of the actual product equals the rational form ratio times the repository lower
group-Haar mass of the lower chart image times the Leray factor times the
lower unit-Haar integral of g over the orbit image. No chart, section or
baseline is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

/-- Integrals of a function of the second coordinate over a rectangle split off
the measure of the first side. -/
theorem MeasureTheory.setLIntegral_prod_snd {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
    (A : Set α) (B : Set β) {F : β → ℝ≥0∞} (hF : AEMeasurable F (ν.restrict B)) :
    ∫⁻ x in A ×ˢ B, F x.2 ∂(μ.prod ν) = μ A * ∫⁻ c in B, F c ∂ν := by
  rw [← Measure.prod_restrict]
  calc ∫⁻ x, F x.2 ∂((μ.restrict A).prod (ν.restrict B))
      = ∫⁻ x, (fun _ : α ↦ (1 : ℝ≥0∞)) x.1 * F x.2 ∂((μ.restrict A).prod (ν.restrict B)) := by
        simp only [one_mul]
    _ = (∫⁻ _, (1 : ℝ≥0∞) ∂(μ.restrict A)) * ∫⁻ c, F c ∂(ν.restrict B) :=
        lintegral_prod_mul aemeasurable_const hF
    _ = μ A * ∫⁻ c in B, F c ∂ν := by rw [lintegral_one, Measure.restrict_apply_univ]

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

section LocalVolume

local instance lvPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance lvPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The source coordinate ball is a rectangle: lower coordinate ball ×
horizontal coefficient ball. -/
theorem lastCayleyProductSourceCoordinates_preimage_closedBall
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    {r : ℝ} (hr : 0 ≤ r) :
    (W.lastCayleyProductSourceCoordinates p) ⁻¹'
        closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r =
      ((skewAdjointPadicCoordinateEquiv W.pairingMatrix p) ⁻¹'
          closedBall (skewAdjointPadicCoordinateEquiv W.pairingMatrix p Y) r :
        Set (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))) ×ˢ
        closedBall (0 : Fin n → ℚ_[p]) r := by
  have hsplit : ∀ q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p]), W.lastCayleyProductSourceCoordinates p q =
        Sum.elim (skewAdjointPadicCoordinateEquiv W.pairingMatrix p q.1) q.2 := by
    intro q
    have h := congrFun (W.lastCayleyProductSourceCoordinates_prodMap p)
      (skewAdjointPadicCoordinateEquiv W.pairingMatrix p q.1, q.2)
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h
    exact h
  ext q
  simp only [mem_preimage, mem_prod, mem_closedBall, hsplit, dist_pi_le_iff hr, Sum.forall,
    Sum.elim_inl, Sum.elim_inr]

end LocalVolume

section OrbitVolume

variable (a : ℚ) (ha : a ≠ 0)

local instance ovPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance ovPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance ovSkewMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance ovSkewBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance ovLowerMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance ovLowerBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance ovGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance ovGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance ovLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance ovLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance ovLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance ovLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩
local instance ovHigherLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance ovHigherLieBorelSpace :
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

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
include hSs hSO hY hproduct hs hv in
/-- Local relative fiber-product volume identity for orbit tests: on every
sufficiently small exact compact open coordinate rectangle around `(Y, 0)`,
the repository higher group-Haar integral of `g(lower coordinates of h·x_old)`
over the Cayley image of the actual product equals the rational form ratio ×
the repository lower group-Haar mass of the lower chart image of the lower ball ×
the Leray factor |(-1)^n/(2 a s)| × the lower unit-Haar integral of `g` over
the orbit image. -/
theorem lastCayleyProduct_exists_forall_lintegral_orbit :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∀ g : (Fin n → ℚ_[p]) → ℝ≥0∞, Measurable g →
        ∫⁻ x in Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))),
            g (fun j ↦ ((x.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ
              lastCoordinateVector) j.castSucc)
            ∂(padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
              (W.nonisotropicLastExtension a ha).pairingMatrix
              (W.nonisotropicLastExtension a ha).form_det_ne_zero) =
          (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
              ((fun X' : skewAdjointPadicCayleySource W.pairingMatrix p ↦
                  ((skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1 X').1)) ''
                (Subtype.val ⁻¹' ((skewAdjointPadicCoordinateEquiv W.pairingMatrix p) ⁻¹'
                  closedBall (skewAdjointPadicCoordinateEquiv W.pairingMatrix p Y) r))) *
            (‖((-1 : ℚ_[p])^n / (2 * algebraMap ℚ ℚ_[p] a *
              ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
                lastCoordinateVector) (Fin.last n)))‖₊ : ℝ≥0∞) *
            ∫⁻ y in lastCayleyHorizontalLower p S z v '' closedBall 0 r, g y
              ∂(Padic.unitHaar p (Fin n)) := by
  classical
  set eE := W.lastCayleyProductSourceCoordinates p with heE
  set h1 := skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1 with hh1
  obtain ⟨δ1, hδ1, hBG⟩ := W.lastCayleyProduct_exists_forall_lintegral_bothGroups p a ha S dS z hSs
    hSO Y hY X hX hproduct v hs hv
  obtain ⟨δ2, hδ2, hGR⟩ := W.lastCayleyProduct_exists_forall_lintegral_groupHaar_repository p a ha S dS
    z hSs hSO Y hY X hX hproduct v hs hv
  obtain ⟨δ4, hδ4, hH⟩ := lastCayleyHorizontalLower_exists_forall_lintegral_image p v hv hSs
  obtain ⟨δ5, hδ5, hL⟩ := lastCayleyProduct_orbitRelative_horizontal_eq_leray (p := p) (v := v)
    (hv := hv) (W := W) (a := a) (ha := ha) (hSO := hSO) (Y := Y) (hY := hY) (X := X) (hX := hX)
    (hproduct := hproduct) (hs := hs) hSs
  have hCM := W.lastCayleyProduct_eventually_chart_matrix a ha p S dS z hSs hSO Y hY X hX hproduct v
  have hCMc : {x | ∀ hq : ((W.lastCayleyProductFrameValue a ha p S z v (eE.symm x) : skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
        (skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
        skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p,
      ((skewAdjointPadicCayleyTranslatedHomeomorph (W.nonisotropicLastExtension a ha).pairingMatrix p
          (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨_, hq⟩).1.1.1.1 :
          Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) =
        S (z + ∑ i, (eE.symm x).2 i • v i) *
          fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p (eE.symm x).1)} ∈
      𝓝 (eE (Y,0)) := by
    have hcont : ContinuousAt eE.symm (eE (Y,0)) := eE.symm.continuous.continuousAt
    rw [← eE.symm_apply_apply (Y,0)] at hCM
    exact hcont.preimage_mem_nhds hCM
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hCMc
  refine ⟨min (min (min δ1 δ2) (min δ4 δ5)) ε,
    lt_min (lt_min (lt_min hδ1 hδ2) (lt_min hδ4 hδ5)) hε, fun r hr hrδ g hg ↦ ?_⟩
  have hr1 : r < δ1 := hrδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hr2 : r < δ2 := hrδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hr4 : r < δ4 := hrδ.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr5 : r < δ5 := hrδ.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr3 : r < ε := hrδ.trans_le (min_le_right _ _)
  obtain ⟨hsubsrc, -, -⟩ := hGR r hr hr2
  obtain ⟨-, hcont, -⟩ := hH r hr hr4
  rw [hBG r hr hr1]
  set U1 : Set (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
    (skewAdjointPadicCoordinateEquiv W.pairingMatrix p) ⁻¹'
      closedBall (skewAdjointPadicCoordinateEquiv W.pairingMatrix p Y) r with hU1
  have hrect := W.lastCayleyProductSourceCoordinates_preimage_closedBall p Y hr.le
  set A := (fun X' : skewAdjointPadicCayleySource W.pairingMatrix p ↦ (h1 X').1) ''
    (Subtype.val ⁻¹' U1) with hA
  have hTW : Prod.map (fun X' : skewAdjointPadicCayleySource W.pairingMatrix p ↦ (h1 X').1) _root_.id ''
      (Prod.map Subtype.val _root_.id ⁻¹' (eE ⁻¹' closedBall (eE (Y,0)) r)) =
      A ×ˢ closedBall (0 : Fin n → ℚ_[p]) r := by
    rw [hrect, preimage_prod_map_prod, prodMap_image_prod, image_id, preimage_id]
  rw [hTW]
  have hemb : MeasurableEmbedding (fun X' : skewAdjointPadicCayleySource W.pairingMatrix p ↦ (h1 X').1) :=
    (MeasurableEmbedding.subtype_coe
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget _ p 1).measurableSet).comp
      h1.measurableEmbedding
  have hU1m : MeasurableSet U1 :=
    (isClosed_closedBall.preimage (skewAdjointPadicCoordinateEquiv W.pairingMatrix p).continuous).measurableSet
  have hAm : MeasurableSet A := hemb.measurableSet_image.mpr (measurable_subtype_coe hU1m)
  have hint : ∫⁻ x in A ×ˢ closedBall (0 : Fin n → ℚ_[p]) r,
        W.lastCayleyProductLowerGroupTest p a ha S z v
          (fun x : specialFormPreservingMatrixSubgroup
              ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦
            g (fun j ↦ ((x.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ
              lastCoordinateVector) j.castSucc)) x
        ∂((padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero).prod
          (Padic.unitHaar p (Fin n))) =
      ∫⁻ x in A ×ˢ closedBall (0 : Fin n → ℚ_[p]) r, g (lastCayleyHorizontalLower p S z v x.2)
        ∂((padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero).prod
          (Padic.unitHaar p (Fin n))) := by
    apply setLIntegral_congr_fun (hAm.prod isClosed_closedBall.measurableSet)
    rintro ⟨x1, c⟩ ⟨⟨X', hX'U1, hX'eq⟩, hcB⟩
    simp only at hX'eq hcB
    subst hX'eq
    have hq : ((X'.1, c) : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p])) ∈ eE ⁻¹' closedBall (eE (Y,0)) r := by
      rw [hrect]; exact ⟨hX'U1, hcB⟩
    have hfsrc := hsubsrc ⟨_, hq, rfl⟩
    have hmat := hεsub (closedBall_subset_ball hr3 hq)
    simp only [Set.mem_setOf_eq, ContinuousLinearEquiv.symm_apply_apply] at hmat
    simp only [lastCayleyProductLowerGroupTest, dif_pos (h1 X').2, Subtype.coe_eta]
    rw [← hh1, Homeomorph.symm_apply_apply]
    simp only [lastCayleyChartPullback]
    rw [dif_pos hfsrc, hmat hfsrc, ← Matrix.mulVec_mulVec]
    rw [show fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p X'.1) *ᵥ
        (lastCoordinateVector : Fin (n+1) → ℚ_[p]) = lastCoordinateVector by
      rw [fixLastBlockMatrix, nonisotropicLastBlockMatrix_mulVec_last, one_smul]]
    rfl
  haveI : SigmaFinite (padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix
      W.form_det_ne_zero) :=
    padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite p n W.pairingMatrix W.form_symm
      W.form_det_ne_zero
  rw [hint, MeasureTheory.setLIntegral_prod_snd _ _ A _
    (F := fun c ↦ g (lastCayleyHorizontalLower p S z v c))
    (hg.comp_aemeasurable (hcont.aemeasurable isClosed_closedBall.measurableSet))]
  have hLr := hL r hr hr5 g
  calc _ = (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
        padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero A *
        ((‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
          lastCoordinateVector
          (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
          (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
            Y hY X hX hproduct (0, v j))‖₊ : ℝ≥0∞) *
          ∫⁻ c in closedBall 0 r, g (lastCayleyHorizontalLower p S z v c)
            ∂(Padic.unitHaar p (Fin n))) := by ring
    _ = _ := by rw [hLr]; ring

end OrbitVolume

end RationalQuadraticSpaceMatrix
