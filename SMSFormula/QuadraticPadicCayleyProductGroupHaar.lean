import SMSFormula.QuadraticPadicCayleyProductGroupDensity
import SMSFormula.PadicCayleyTranslatedChartRecovery

/-! Relative fiber product on the group. The repository p-adic group Haar
(`padicCayleySpecialOrthogonalDifferentialMeasure`) restricts on the identity
Cayley chart to the pushforward of (Cayley density × coordinate measure)
(`comap_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget`). The
image of a small exact compact open coordinate ball under the actual product
followed by the identity Cayley chart therefore has group-Haar integral equal to
the rational form ratio times the actual horizontal orbit-relative factor times
the lower-density-weighted source integral. No chart is chosen: the identity
chart is the Cayley map; the group Haar is the repository's. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Filter Set
open scoped Matrix.Norms.Operator Topology ENNReal NNReal

/-- Lintegrals over a subset of the range of a measurable embedding are
lintegrals for the pulled-back measure. No measurability of the set or the
integrand is needed. -/
theorem MeasurableEmbedding.setLIntegral_eq_comap
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {i : α → β}
    (hi : MeasurableEmbedding i) (ν : Measure β) {T : Set β} (hT : T ⊆ range i)
    (G : β → ℝ≥0∞) :
    ∫⁻ x in T, G x ∂ν = ∫⁻ a in i ⁻¹' T, G (i a) ∂(ν.comap i) := by
  have h1 : ν.restrict T = (ν.restrict (range i)).restrict T := by
    rw [Measure.restrict_restrict' hi.measurableSet_range, inter_eq_left.mpr hT]
  rw [h1, ← hi.map_comap, hi.restrict_map, hi.lintegral_map]

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]

section GroupHaar

local instance groupHaarPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance groupHaarPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance groupHaarLowerLieIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  Submodule.topologicalAddGroup _
local instance groupHaarSkewMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance groupHaarSkewBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance groupHaarGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance groupHaarGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance groupHaarLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance groupHaarLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩
local instance groupHaarHigherLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance groupHaarHigherLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩

/-- A group test function read on the higher Lie algebra through the
identity Cayley chart (junk zero off the exact source). -/
def lastCayleyChartPullback
    (G : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) → ℝ≥0∞)
    (y : (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    ℝ≥0∞ := by
  classical
  exact if hy : y ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p then
    G (skewAdjointPadicCayleyTranslatedHomeomorph (W.nonisotropicLastExtension a ha).pairingMatrix p
      (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨y, hy⟩).1
  else 0

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
include hs hv in
/-- Relative fiber product on the group: on every sufficiently small exact compact
open coordinate ball `U` around `(Y, 0)`, the actual product maps `U`
injectively into the exact higher Cayley source, and for every group test
function `G`, the repository group-Haar lintegral over the Cayley image equals
|r| · |orbit-relative| times the lower-Cayley-density-weighted source lintegral
of `G` read through the identity chart. -/
theorem lastCayleyProduct_exists_forall_lintegral_groupHaar :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      W.lastCayleyProductFrameValue a ha p S z v ''
          ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
            closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ⊆
        skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p ∧
      Set.InjOn (W.lastCayleyProductFrameValue a ha p S z v)
        ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
          closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      ∀ G : specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) → ℝ≥0∞,
        ∫⁻ x in Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))),
            G x ∂(padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
              (W.nonisotropicLastExtension a ha).pairingMatrix
              (W.nonisotropicLastExtension a ha).form_det_ne_zero) =
          (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
              lastCoordinateVector
              (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
              (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
                Y hY X hX hproduct (0, v j))‖₊ : ℝ≥0∞) *
            ∫⁻ q in (W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
              skewAdjointPadicCayleyAmbientDensity p n W.pairingMatrix q.1 *
                W.lastCayleyChartPullback a ha p G (W.lastCayleyProductFrameValue a ha p S z v q)
                ∂(W.lastCayleyProductSourceMeasure p) := by
  classical
  set eE := W.lastCayleyProductSourceCoordinates p with heE
  set f := W.lastCayleyProductFrameValue a ha p S z v with hf
  set h1 := skewAdjointPadicCayleyTranslatedHomeomorph (W.nonisotropicLastExtension a ha).pairingMatrix p
    (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 with hh1
  obtain ⟨δ1, hδ1, hGD⟩ := W.lastCayleyProduct_exists_forall_lintegral_image_groupDensity a ha p S dS
    z hSs hSO Y hY X hX hproduct v hs hv
  obtain ⟨δ2, hδ2, hRep⟩ := W.lastCayleyProduct_exists_forall_lintegral_image_repository a ha p S dS
    z hSs hSO Y hY X hX hproduct v hs hv
  obtain ⟨e, -, hef, hbase, -⟩ := W.lastCayleyProduct_exists_localInverse a ha p S dS z hSs hSO Y hY
    X hX hproduct v hs hv
  have hfY : f (Y,0) = X := by rw [← hbase, hef]
  have hfcont : ContinuousAt f (Y,0) :=
    (W.hasStrictFDerivAt_lastCayleyProductFrameValue a ha p S dS z hSs hSO Y hY X hX hproduct
      v).continuousAt
  have hsrcOpen : IsOpen (skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p) := isOpen_skewAdjointPadicCayleySource _ p
  have hsrcN : {q | f q ∈ (skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)} ∈ 𝓝 ((Y,0) : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × (Fin n → ℚ_[p])) := by
    apply hfcont.preimage_mem_nhds
    rw [hfY]
    exact hsrcOpen.mem_nhds hX
  have hsrcC : {x | f (eE.symm x) ∈ (skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)} ∈ 𝓝 (eE (Y,0)) := by
    have hcont : ContinuousAt eE.symm (eE (Y,0)) := eE.symm.continuous.continuousAt
    rw [← eE.symm_apply_apply (Y,0)] at hsrcN
    exact hcont.preimage_mem_nhds hsrcN
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hsrcC
  refine ⟨min (min δ1 δ2) ε, lt_min (lt_min hδ1 hδ2) hε, fun r hr hrδ ↦ ?_⟩
  have hr1 : r < δ1 := hrδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hr2 : r < δ2 := hrδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hr3 : r < ε := hrδ.trans_le (min_le_right _ _)
  obtain ⟨hinj, hlaw⟩ := hGD r hr hr1
  obtain ⟨-, hcont, -⟩ := hRep r hr hr2
  set U := eE ⁻¹' closedBall (eE (Y,0)) r with hU
  have hUsrc : f '' U ⊆ (skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p) := by
    rintro _ ⟨q, hq, rfl⟩
    have := hεsub (closedBall_subset_ball hr3 hq)
    simpa only [Set.mem_setOf_eq, ContinuousLinearEquiv.symm_apply_apply] using this
  refine ⟨hUsrc, hinj, fun G ↦ ?_⟩
  -- measurability of the image
  have hUc : IsCompact U := eE.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hfUm : MeasurableSet (f '' U) := (hUc.image_of_continuousOn hcont).isClosed.measurableSet
  set A : Set (skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p) := Subtype.val ⁻¹' (f '' U) with hA
  have hAm : MeasurableSet A := measurable_subtype_coe hfUm
  -- group → identity chart target
  have hi : MeasurableEmbedding (Subtype.val :
      padicCayleySpecialOrthogonalTranslatedTarget (W.nonisotropicLastExtension a ha).pairingMatrix p 1 →
        specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
    MeasurableEmbedding.subtype_coe
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget _ p 1).measurableSet
  rw [hi.setLIntegral_eq_comap _ (image_subset_range _ _) G,
    comap_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget p (n+1) _
      (W.nonisotropicLastExtension a ha).form_symm (W.nonisotropicLastExtension a ha).form_det_ne_zero 1,
    Subtype.val_injective.preimage_image]
  -- identity chart target → source differential measure
  have hchart : ∫⁻ x in h1 '' A, G x.1 ∂(padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p (n+1) (W.nonisotropicLastExtension a ha).pairingMatrix
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1) =
      ∫⁻ X in A, G (h1 X).1 ∂(Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure p (n+1)
        (W.nonisotropicLastExtension a ha).pairingMatrix) := by
    have hemb : MeasurableEmbedding h1 := h1.measurableEmbedding
    rw [hemb.setLIntegral_eq_comap _ (image_subset_range _ _), h1.injective.preimage_image,
      padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure, hemb.comap_map]
  rw [hchart]
  -- differential measure → coordinate measure with density
  rw [Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _
      (Matrix.measurable_skewAdjointPadicCayleySourceDifferentialDensityENNReal p (n+1) _) _ hAm
      (Eventually.of_forall fun X ↦ by
        rw [Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_coe]
        exact ENNReal.coe_lt_top)]
  -- source subtype → coordinate space
  have hsub : MeasurableEmbedding (Subtype.val : (skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p) → _) :=
    MeasurableEmbedding.subtype_coe hsrcOpen.measurableSet
  have hback := hsub.setLIntegral_eq_comap (T := f '' U)
    (skewAdjointPadicCoordinateMeasure (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (Subtype.range_coe.symm ▸ hUsrc)
    (fun y ↦ skewAdjointPadicCayleyAmbientDensity p (n+1) (W.nonisotropicLastExtension a ha).pairingMatrix y *
      W.lastCayleyChartPullback a ha p G y)
  have hint : ∫⁻ X in A, (Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal p (n+1)
        (W.nonisotropicLastExtension a ha).pairingMatrix * fun X ↦ G (h1 X).1) X
        ∂(Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p (n+1)
          (W.nonisotropicLastExtension a ha).pairingMatrix) =
      ∫⁻ X in A, skewAdjointPadicCayleyAmbientDensity p (n+1)
          (W.nonisotropicLastExtension a ha).pairingMatrix X.1 *
        W.lastCayleyChartPullback a ha p G X.1
        ∂(Measure.comap Subtype.val
          (skewAdjointPadicCoordinateMeasure (W.nonisotropicLastExtension a ha).pairingMatrix p)) := by
    apply setLIntegral_congr_fun hAm
    intro X _
    simp only [Pi.mul_apply, lastCayleyChartPullback, dif_pos X.2, Subtype.coe_eta]
    rfl
  rw [hint, ← hback, ← W.lastCayleyProductTargetMeasure_eq_repository a ha p]
  exact hlaw (W.lastCayleyChartPullback a ha p G)

include hSs hSO hY hX hproduct in
/-- Near the base point the identity-chart image of the actual product is the
supplied left factor times the embedded lower Cayley group point: the group
image in the fiber-product theorem is the lower group translated by `S`. -/
theorem lastCayleyProduct_eventually_chart_matrix :
    ∀ᶠ q in 𝓝 ((Y, 0) : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p])),
      ∀ hq : ((W.lastCayleyProductFrameValue a ha p S z v q :
          skewAdjointMatricesLieSubalgebra
            ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
          (skewAdjointMatricesLieSubalgebra
            ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
          skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p,
        ((skewAdjointPadicCayleyTranslatedHomeomorph (W.nonisotropicLastExtension a ha).pairingMatrix p
            (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨_, hq⟩).1.1.1.1 :
            Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) =
          S (z + ∑ i, q.2 i • v i) *
            fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1) := by
  have hσ : Tendsto
      (fun q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p]) ↦ (q.1, z + ∑ i, q.2 i • v i)) (𝓝 (Y,0)) (𝓝 (Y,z)) := by
    have hc : Continuous
        (fun q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
          (Fin n → ℚ_[p]) ↦ (q.1, z + ∑ i, q.2 i • v i)) := by fun_prop
    simpa using hc.tendsto (Y,0)
  filter_upwards [W.lastCayleyProductFrameValue_eventually_eq a ha p S dS z hSs hSO Y hY X hX
      hproduct v,
    hσ.eventually (W.lastCayleyProduct_eventually_specialOrthogonal a ha p S dS z
      hSs.hasFDerivAt hSO Y hY X hX hproduct)] with q hq hdom hsrc
  rw [coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]
  have hval : ((W.lastCayleyProductFrameValue a ha p S z v q :
      skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
      Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) =
      padicCayleyInverseMatrix p (S (z + ∑ i, q.2 i • v i) *
        fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1)) := hq
  change ((1 : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).1.1.1 : Matrix _ _ _) *
    padicCayleyForwardMatrix p ((W.lastCayleyProductFrameValue a ha p S z v q :
      skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
      Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) = _
  rw [hval, padicCayleyForwardMatrix_inverse p _ hdom.2]
  simp

end GroupHaar

end RationalQuadraticSpaceMatrix
