import SMSFormula.RationalCliffordSpinCandidateDifferentialCoordinateChart

/-!
# Haar recovery in Spin differential coordinates

The real and p-adic Spin differential-coordinate charts are constructed by
composing an identity chart for the Spin-to-`SO` point map with the
`SO` differential coordinates.  This file proves that the nonlinear source
measures packaged with those composite charts are exactly the restrictions,
expressed by subtype comap, of the full placewise Spin Haar
measures.

The proof keeps both stages of the composite chart explicit.  It first
restricts the `SO` coordinate density to the smaller composite
target and then uses the recovery of the glued Spin measure on
the point-map identity chart.  Consequently the coordinate maps push the
restricted full Spin Haar measures to the exact real Jacobian and p-adic
inverse-Cayley densities.

No bare tangent measure replaces these nonlinear densities.  In particular,
the result is not a point-carrier Frechet derivative or an independent
analytic change-of-variables theorem for the chosen Spin top form.
-/

noncomputable section

open MeasureTheory
open Topology
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

private theorem comap_withDensity_of_measurableEmbedding
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (j : α → β) (hj : MeasurableEmbedding j) (μ : Measure β)
    (f : β → ℝ≥0∞) (hf : Measurable f) :
    Measure.comap j (μ.withDensity f) =
      (Measure.comap j μ).withDensity (f ∘ j) := by
  ext s hs
  rw [Measure.comap_apply j hj.injective
      (fun t ht ↦ hj.measurableSet_image.2 ht) _ hs,
    withDensity_apply _ (hj.measurableSet_image.2 hs),
    withDensity_apply _ hs]
  have himage : MeasurableSet (j '' s) := hj.measurableSet_image.2 hs
  have hrestrict :
      (μ.restrict (Set.range j)).restrict (j '' s) =
        μ.restrict (j '' s) := by
    rw [Measure.restrict_restrict himage]
    congr 1
    exact Set.inter_eq_left.mpr (Set.image_subset_range j s)
  calc
    (∫⁻ y in j '' s, f y ∂μ) =
        ∫⁻ y in j '' s, f y ∂(μ.restrict (Set.range j)) := by
      rw [hrestrict]
    _ = ∫⁻ y in j '' s, f y ∂Measure.map j (Measure.comap j μ) := by
      rw [hj.map_comap]
    _ = ∫⁻ x in j ⁻¹' (j '' s), f (j x) ∂Measure.comap j μ := by
      rw [setLIntegral_map himage hf hj.measurable]
    _ = ∫⁻ x in s, f (j x) ∂Measure.comap j μ := by
      congr 2
      exact Set.preimage_image_eq s hj.injective

private def openSetInclusion
    {α : Type*} (s t : Set α) (h : s ⊆ t) : s → t :=
  fun x ↦ ⟨x.1, h x.2⟩

private theorem measurableEmbedding_openSetInclusion
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (s t : Set α) (h : s ⊆ t) (hs : IsOpen s) :
    MeasurableEmbedding (openSetInclusion s t h) := by
  let u : Set t := Subtype.val ⁻¹' s
  let toU : s → u := fun x ↦ ⟨⟨x.1, h x.2⟩, x.2⟩
  let fromU : u → s := fun x ↦ ⟨x.1.1, x.2⟩
  let e : s ≃ₜ u :=
    { toFun := toU
      invFun := fromU
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      continuous_toFun :=
        ((continuous_subtype_val.subtype_mk _).subtype_mk _)
      continuous_invFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  have hu : IsOpen u := hs.preimage continuous_subtype_val
  have hi : MeasurableEmbedding (Subtype.val : u → t) :=
    MeasurableEmbedding.subtype_coe hu.measurableSet
  have he : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  simpa [openSetInclusion, e, toU, fromU, u, Function.comp_def] using hi.comp he

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

noncomputable local instance scratchRealSkewAdjointMeasurableSpace :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

noncomputable local instance scratchRealSkewAdjointBorelSpace :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

noncomputable local instance scratchRealSpecialOrthogonalMeasurableSpace :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  borel _

noncomputable local instance scratchRealSpecialOrthogonalBorelSpace :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

private theorem realCompositeTarget_subset_soTarget :
    V.realCliffordSpinCandidateSkewAdjointIdentityChart.target ⊆
      (specialFormPreservingSmoothRealIdentityChart
        V.pairingMatrix V.form_symm V.form_det_ne_zero).target := by
  intro y hy
  change y ∈
    (V.realCliffordSpinCandidateIdentityChart.trans
      (specialFormPreservingSmoothRealIdentityChart
        V.pairingMatrix V.form_symm V.form_det_ne_zero)).target at hy
  rw [OpenPartialHomeomorph.trans_target] at hy
  exact hy.1

private def realCompositeTargetToSOTarget :
    V.realCliffordSpinCandidateSkewAdjointIdentityChart.target →
      (specialFormPreservingSmoothRealIdentityChart
        V.pairingMatrix V.form_symm V.form_det_ne_zero).target :=
  openSetInclusion _ _ (V.realCompositeTarget_subset_soTarget)

private theorem measurableEmbedding_realCompositeTargetToSOTarget :
    MeasurableEmbedding V.realCompositeTargetToSOTarget :=
  measurableEmbedding_openSetInclusion _ _
    (V.realCompositeTarget_subset_soTarget)
    V.realCliffordSpinCandidateSkewAdjointIdentityChart.open_target

private theorem realCompositeTargetMeasure_eq_comap :
    Measure.comap V.realCompositeTargetToSOTarget
        (specialFormPreservingSmoothRealChartTargetDensityMeasure
          V.pairingMatrix V.form_symm V.form_det_ne_zero 1) =
      V.realCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure := by
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure,
    realCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure,
    comap_withDensity_of_measurableEmbedding
      V.realCompositeTargetToSOTarget
      V.measurableEmbedding_realCompositeTargetToSOTarget _ _
      (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        V.pairingMatrix V.form_symm V.form_det_ne_zero 1)]
  congr 1
  · rw [Measure.comap_comap
      (fun s hs ↦
        V.measurableEmbedding_realCompositeTargetToSOTarget.measurableSet_image.2 hs)
      (MeasurableEmbedding.subtype_coe
        (specialFormPreservingSmoothRealIdentityChart
          V.pairingMatrix V.form_symm V.form_det_ne_zero).open_target.measurableSet).injective
      (fun s hs ↦ (MeasurableEmbedding.subtype_coe
        (specialFormPreservingSmoothRealIdentityChart
          V.pairingMatrix V.form_symm V.form_det_ne_zero).open_target.measurableSet
        |>.measurableSet_image.2 hs))]
    rfl

private def realCompositeSourceToSOSource :
    V.realCliffordSpinCandidateSkewAdjointIdentityChart.source →
      (specialFormPreservingSmoothRealIdentityChart
        V.pairingMatrix V.form_symm V.form_det_ne_zero).source :=
  (specialFormPreservingSmoothRealIdentityChart
      V.pairingMatrix V.form_symm V.form_det_ne_zero).toHomeomorphSourceTarget.symm ∘
    V.realCompositeTargetToSOTarget ∘
      V.realCliffordSpinCandidateSkewAdjointIdentityChart.toHomeomorphSourceTarget

private theorem measurableEmbedding_realCompositeSourceToSOSource :
    MeasurableEmbedding V.realCompositeSourceToSOSource :=
  (specialFormPreservingSmoothRealIdentityChart
      V.pairingMatrix V.form_symm V.form_det_ne_zero
      |>.toHomeomorphSourceTarget.symm.toMeasurableEquiv.measurableEmbedding).comp
    (V.measurableEmbedding_realCompositeTargetToSOTarget.comp
      (V.realCliffordSpinCandidateSkewAdjointIdentityChart
        |>.toHomeomorphSourceTarget.toMeasurableEquiv.measurableEmbedding))

private theorem realCompositeSourceMeasure_eq_comap_soSource :
    V.realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure =
      Measure.comap V.realCompositeSourceToSOSource
        (specialFormPreservingSmoothRealChartSourceDensityMeasure
          V.pairingMatrix V.form_symm V.form_det_ne_zero 1) := by
  rw [realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure,
    specialFormPreservingSmoothRealChartSourceDensityMeasure_eq_target_comap]
  have hmapSymm :
      Measure.map
          (V.realCliffordSpinCandidateSkewAdjointIdentityChart
            |>.toHomeomorphSourceTarget.symm)
          V.realCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure =
        Measure.comap
          (V.realCliffordSpinCandidateSkewAdjointIdentityChart
            |>.toHomeomorphSourceTarget)
          V.realCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure :=
    V.realCliffordSpinCandidateSkewAdjointIdentityChart
      |>.toHomeomorphSourceTarget.toMeasurableEquiv.map_symm
  rw [hmapSymm]
  rw [← V.realCompositeTargetMeasure_eq_comap]
  calc
    Measure.comap
        V.realCliffordSpinCandidateSkewAdjointIdentityChart.toHomeomorphSourceTarget
        (Measure.comap V.realCompositeTargetToSOTarget
          (specialFormPreservingSmoothRealChartTargetDensityMeasure
            V.pairingMatrix V.form_symm V.form_det_ne_zero 1)) =
        Measure.comap
          (V.realCompositeTargetToSOTarget ∘
            (V.realCliffordSpinCandidateSkewAdjointIdentityChart
              |>.toHomeomorphSourceTarget))
          (specialFormPreservingSmoothRealChartTargetDensityMeasure
            V.pairingMatrix V.form_symm V.form_det_ne_zero 1) :=
      Measure.comap_comap
        (fun s hs ↦
          V.realCliffordSpinCandidateSkewAdjointIdentityChart
            |>.toHomeomorphSourceTarget.toMeasurableEquiv.measurableEmbedding
            |>.measurableSet_image.2 hs)
        V.measurableEmbedding_realCompositeTargetToSOTarget.injective
        (fun s hs ↦
          V.measurableEmbedding_realCompositeTargetToSOTarget.measurableSet_image.2 hs)
        _
    _ = Measure.comap
          ((specialFormPreservingSmoothRealIdentityChart
              V.pairingMatrix V.form_symm V.form_det_ne_zero
              |>.toHomeomorphSourceTarget) ∘
            V.realCompositeSourceToSOSource)
          (specialFormPreservingSmoothRealChartTargetDensityMeasure
            V.pairingMatrix V.form_symm V.form_det_ne_zero 1) := by
      congr 1
      funext x
      exact (specialFormPreservingSmoothRealIdentityChart
        V.pairingMatrix V.form_symm V.form_det_ne_zero
        |>.toHomeomorphSourceTarget.apply_symm_apply
          (V.realCompositeTargetToSOTarget
            (V.realCliffordSpinCandidateSkewAdjointIdentityChart
              |>.toHomeomorphSourceTarget x))).symm
    _ = Measure.comap V.realCompositeSourceToSOSource
          (Measure.comap
            (specialFormPreservingSmoothRealIdentityChart
              V.pairingMatrix V.form_symm V.form_det_ne_zero
              |>.toHomeomorphSourceTarget)
            (specialFormPreservingSmoothRealChartTargetDensityMeasure
              V.pairingMatrix V.form_symm V.form_det_ne_zero 1)) := by
      symm
      exact Measure.comap_comap
        (fun s hs ↦
          V.measurableEmbedding_realCompositeSourceToSOSource.measurableSet_image.2 hs)
        (specialFormPreservingSmoothRealIdentityChart
          V.pairingMatrix V.form_symm V.form_det_ne_zero
          |>.toHomeomorphSourceTarget.toMeasurableEquiv.measurableEmbedding).injective
        (fun s hs ↦
          (specialFormPreservingSmoothRealIdentityChart
            V.pairingMatrix V.form_symm V.form_det_ne_zero
            |>.toHomeomorphSourceTarget.toMeasurableEquiv.measurableEmbedding
            |>.measurableSet_image.2 hs)) _

private theorem realSOSourceDensityMeasure_eq_comap :
    specialFormPreservingSmoothRealChartSourceDensityMeasure
        V.pairingMatrix V.form_symm V.form_det_ne_zero 1 =
      Measure.comap Subtype.val V.realInvariantDifferentialGroupMeasure := by
  apply (MeasurableEmbedding.subtype_coe
    (specialFormPreservingSmoothRealIdentityChart
      V.pairingMatrix V.form_symm V.form_det_ne_zero).open_source.measurableSet).map_injective
  rw [map_comap_subtype_coe
    (specialFormPreservingSmoothRealIdentityChart
      V.pairingMatrix V.form_symm V.form_det_ne_zero).open_source.measurableSet]
  change specialFormPreservingSmoothRealChartAmbientDensityMeasure
      V.pairingMatrix V.form_symm V.form_det_ne_zero 1 =
    V.realInvariantDifferentialGroupMeasure.restrict
      (specialFormPreservingSmoothRealIdentityChart
        V.pairingMatrix V.form_symm V.form_det_ne_zero).source
  exact V.restrict_realInvariantDifferentialGroupMeasure_identityChart.symm

private theorem realCompositeSourceMeasure_eq_comap_pointMap :
    V.realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure =
      Measure.comap
        (fun x : V.realCliffordSpinCandidateSkewAdjointIdentityChart.source ↦
          V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1)
        V.realInvariantDifferentialGroupMeasure := by
  rw [V.realCompositeSourceMeasure_eq_comap_soSource]
  rw [V.realSOSourceDensityMeasure_eq_comap]
  rw [Measure.comap_comap
    (fun s hs ↦ V.measurableEmbedding_realCompositeSourceToSOSource.measurableSet_image.2 hs)
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart
        V.pairingMatrix V.form_symm V.form_det_ne_zero).open_source.measurableSet).injective
    (fun s hs ↦ (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart
        V.pairingMatrix V.form_symm V.form_det_ne_zero).open_source.measurableSet
      |>.measurableSet_image.2 hs))]
  congr 1
  funext x
  let B := specialFormPreservingSmoothRealIdentityChart
    V.pairingMatrix V.form_symm V.form_det_ne_zero
  have hx : x.1 ∈
      (V.realCliffordSpinCandidateIdentityChart.trans B).source := x.2
  rw [OpenPartialHomeomorph.trans_source] at hx
  let z : B.source :=
    ⟨V.realCliffordSpinCandidateIdentityChart x.1, hx.2⟩
  have hy :
      V.realCompositeTargetToSOTarget
          (V.realCliffordSpinCandidateSkewAdjointIdentityChart
            |>.toHomeomorphSourceTarget x) =
        B.toHomeomorphSourceTarget z := by
    apply Subtype.ext
    change V.realCliffordSpinCandidateSkewAdjointIdentityChart x.1 =
      B (V.realCliffordSpinCandidateIdentityChart x.1)
    rw [V.realCliffordSpinCandidateSkewAdjointIdentityChart_apply]
    change B (V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1) =
      B (V.realCliffordSpinCandidateIdentityChart x.1)
    rw [← congrFun V.realCliffordSpinCandidateIdentityChart_coe x.1]
  change (B.toHomeomorphSourceTarget.symm
    (V.realCompositeTargetToSOTarget
      (V.realCliffordSpinCandidateSkewAdjointIdentityChart
        |>.toHomeomorphSourceTarget x))).1 = _
  rw [hy, B.toHomeomorphSourceTarget.symm_apply_apply]
  change V.realCliffordSpinCandidateIdentityChart x.1 =
    V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1
  rw [← congrFun V.realCliffordSpinCandidateIdentityChart_coe x.1]

private theorem realIdentitySpinSourceMeasure_eq_comap_pointMap :
    V.realCliffordSpinCandidateIdentityChartSourceMeasure =
      Measure.comap
        (fun x : V.realCliffordSpinCandidateIdentityChart.source ↦
          V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1)
        V.realInvariantDifferentialGroupMeasure := by
  rw [realCliffordSpinCandidateIdentityChartSourceMeasure,
    realCliffordSpinCandidateIdentityChartTargetMeasure]
  have hmapSymm :
      Measure.map
          V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.symm
          (Measure.comap Subtype.val V.realInvariantDifferentialGroupMeasure) =
        Measure.comap
          V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget
          (Measure.comap Subtype.val V.realInvariantDifferentialGroupMeasure) :=
    V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget
      |>.toMeasurableEquiv.map_symm
  rw [hmapSymm]
  calc
    Measure.comap
        V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget
        (Measure.comap Subtype.val V.realInvariantDifferentialGroupMeasure) =
        Measure.comap
          (Subtype.val ∘
            V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget)
          V.realInvariantDifferentialGroupMeasure :=
      Measure.comap_comap
        (fun s hs ↦
          V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget
            |>.toMeasurableEquiv.measurableEmbedding.measurableSet_image.2 hs)
        (MeasurableEmbedding.subtype_coe
          V.realCliffordSpinCandidateIdentityChart.open_target.measurableSet).injective
        (fun s hs ↦ (MeasurableEmbedding.subtype_coe
          V.realCliffordSpinCandidateIdentityChart.open_target.measurableSet
          |>.measurableSet_image.2 hs)) _
    _ = Measure.comap
          (fun x : V.realCliffordSpinCandidateIdentityChart.source ↦
            V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1)
          V.realInvariantDifferentialGroupMeasure := by
      congr 1
      funext x
      change V.realCliffordSpinCandidateIdentityChart x.1 =
        V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1
      rw [← congrFun V.realCliffordSpinCandidateIdentityChart_coe x.1]

private theorem realGluedMeasure_comap_identitySource :
    Measure.comap Subtype.val V.realCliffordSpinCandidateChartGluedMeasure =
      V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
  apply (MeasurableEmbedding.subtype_coe
    V.realCliffordSpinCandidateIdentityChart.open_source.measurableSet).map_injective
  rw [map_comap_subtype_coe
    V.realCliffordSpinCandidateIdentityChart.open_source.measurableSet]
  calc
    V.realCliffordSpinCandidateChartGluedMeasure.restrict
        V.realCliffordSpinCandidateIdentityChart.source =
        V.realCliffordSpinCandidateChartGluedMeasure.restrict
          (V.RealCliffordSpinCandidateTranslatedChartSource 1) := by
      congr 1
      ext x
      simp [RealCliffordSpinCandidateTranslatedChartSource,
        MeasureTheory.TranslatedHomChart.source]
    _ = Measure.map Subtype.val
        (V.realCliffordSpinCandidateTranslatedChartSourceMeasure 1) :=
      V.restrict_realCliffordSpinCandidateChartGluedMeasure_source 1
    _ = Measure.map Subtype.val
        (Measure.map
          (MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph
            V.realCliffordSpinCandidateIdentityChart 1)
          V.realCliffordSpinCandidateIdentityChartSourceMeasure) := by
      rw [V.map_realCliffordSpinCandidateIdentityChartSourceMeasure_left]
    _ = Measure.map Subtype.val
        V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph
          V.realCliffordSpinCandidateIdentityChart 1).measurable]
      congr 1
      funext x
      simp [MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph]

private theorem realCompositeSource_subset_pointSource :
    V.realCliffordSpinCandidateSkewAdjointIdentityChart.source ⊆
      V.realCliffordSpinCandidateIdentityChart.source := by
  intro x hx
  change x ∈
    (V.realCliffordSpinCandidateIdentityChart.trans
      (specialFormPreservingSmoothRealIdentityChart
        V.pairingMatrix V.form_symm V.form_det_ne_zero)).source at hx
  rw [OpenPartialHomeomorph.trans_source] at hx
  exact hx.1

private def realCompositeSourceToPointSource :
    V.realCliffordSpinCandidateSkewAdjointIdentityChart.source →
      V.realCliffordSpinCandidateIdentityChart.source :=
  openSetInclusion _ _ V.realCompositeSource_subset_pointSource

private theorem measurableEmbedding_realCompositeSourceToPointSource :
    MeasurableEmbedding V.realCompositeSourceToPointSource :=
  measurableEmbedding_openSetInclusion _ _
    V.realCompositeSource_subset_pointSource
    V.realCliffordSpinCandidateSkewAdjointIdentityChart.open_source

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the full glued real Spin Haar measure to the exact composite
coordinate source recovers the nonlinear source measure constructed from the
real `SO` Jacobian density. -/
theorem comap_realCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChartSource :
    Measure.comap Subtype.val V.realCliffordSpinCandidateChartGluedMeasure =
      V.realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure := by
  calc
    Measure.comap Subtype.val V.realCliffordSpinCandidateChartGluedMeasure =
        Measure.comap V.realCompositeSourceToPointSource
          (Measure.comap Subtype.val
            V.realCliffordSpinCandidateChartGluedMeasure) := by
      symm
      rw [Measure.comap_comap
        (fun s hs ↦
          V.measurableEmbedding_realCompositeSourceToPointSource.measurableSet_image.2 hs)
        (MeasurableEmbedding.subtype_coe
          V.realCliffordSpinCandidateIdentityChart.open_source.measurableSet).injective
        (fun s hs ↦ (MeasurableEmbedding.subtype_coe
          V.realCliffordSpinCandidateIdentityChart.open_source.measurableSet
          |>.measurableSet_image.2 hs))]
      rfl
    _ = Measure.comap V.realCompositeSourceToPointSource
          V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
      rw [V.realGluedMeasure_comap_identitySource]
    _ = Measure.comap V.realCompositeSourceToPointSource
          (Measure.comap
            (fun x : V.realCliffordSpinCandidateIdentityChart.source ↦
              V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1)
            V.realInvariantDifferentialGroupMeasure) := by
      rw [V.realIdentitySpinSourceMeasure_eq_comap_pointMap]
    _ = Measure.comap
          (fun x : V.realCliffordSpinCandidateSkewAdjointIdentityChart.source ↦
            V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1)
          V.realInvariantDifferentialGroupMeasure := by
      have hf : MeasurableEmbedding
          (fun x : V.realCliffordSpinCandidateIdentityChart.source ↦
            V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1) := by
        have hcomp := (MeasurableEmbedding.subtype_coe
          V.realCliffordSpinCandidateIdentityChart.open_target.measurableSet).comp
            (V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget
              |>.toMeasurableEquiv.measurableEmbedding)
        simpa [Function.comp_def,
          ← congrFun V.realCliffordSpinCandidateIdentityChart_coe] using hcomp
      rw [Measure.comap_comap
        (fun s hs ↦
          V.measurableEmbedding_realCompositeSourceToPointSource.measurableSet_image.2 hs)
        hf.injective
        (fun s hs ↦ hf.measurableSet_image.2 hs)
        V.realInvariantDifferentialGroupMeasure]
      rfl
    _ = V.realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure := by
      exact V.realCompositeSourceMeasure_eq_comap_pointMap.symm

/-- The real skew-adjoint differential coordinate sends the restricted full
Spin Haar measure to the exact nonlinear target density. -/
theorem map_comap_realCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChart :
    Measure.map
        V.realCliffordSpinCandidateSkewAdjointIdentityChart.toHomeomorphSourceTarget
        (Measure.comap Subtype.val
          V.realCliffordSpinCandidateChartGluedMeasure) =
      V.realCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure := by
  rw [V.comap_realCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChartSource,
    V.map_realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure]

/-- Equivalently, the ambient real Spin Haar measure restricts to the
pushforward of the packaged nonlinear coordinate-source measure. -/
theorem restrict_realCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChartSource :
    V.realCliffordSpinCandidateChartGluedMeasure.restrict
        V.realCliffordSpinCandidateSkewAdjointIdentityChart.source =
      Measure.map Subtype.val
        V.realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure := by
  rw [← map_comap_subtype_coe
    V.realCliffordSpinCandidateSkewAdjointIdentityChart.open_source.measurableSet,
    V.comap_realCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChartSource]

/-! ## Transport to the algebraic Spin tangent -/

/-! P-adic comparison. -/

noncomputable local instance scratchPadicSkewAdjointMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

noncomputable local instance scratchPadicSkewAdjointBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

noncomputable local instance scratchPadicSpecialOrthogonalMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

noncomputable local instance scratchPadicSpecialOrthogonalBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

private theorem padicCompositeTarget_subset_cayleySource
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).target ⊆
      Matrix.skewAdjointPadicCayleySource V.pairingMatrix p := by
  intro y hy
  change y ∈
    ((V.padicCliffordSpinCandidateIdentityChart p).trans
      (V.padicSpecialOrthogonalCayleyIdentityChart p)).target at hy
  rw [OpenPartialHomeomorph.trans_target] at hy
  simpa using hy.1

private def padicCompositeTargetToCayleySource
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).target →
      Matrix.skewAdjointPadicCayleySource V.pairingMatrix p :=
  openSetInclusion _ _ (V.padicCompositeTarget_subset_cayleySource p)

private theorem measurableEmbedding_padicCompositeTargetToCayleySource
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableEmbedding (V.padicCompositeTargetToCayleySource p) :=
  measurableEmbedding_openSetInclusion _ _
    (V.padicCompositeTarget_subset_cayleySource p)
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).open_target

private theorem padicCompositeTargetMeasure_eq_comap
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.comap (V.padicCompositeTargetToCayleySource p)
        (Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
          p n V.pairingMatrix) =
      V.padicCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure p := by
  rw [Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure,
    Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure,
    padicCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure,
    comap_withDensity_of_measurableEmbedding
      (V.padicCompositeTargetToCayleySource p)
      (V.measurableEmbedding_padicCompositeTargetToCayleySource p) _ _
      (Matrix.measurable_skewAdjointPadicCayleySourceDifferentialDensityENNReal
        p n V.pairingMatrix)]
  congr 1
  rw [Measure.comap_comap
    (fun s hs ↦
      (V.measurableEmbedding_padicCompositeTargetToCayleySource p)
        |>.measurableSet_image.2 hs)
    (MeasurableEmbedding.subtype_coe
      (Matrix.isOpen_skewAdjointPadicCayleySource
        V.pairingMatrix p).measurableSet).injective
    (fun s hs ↦ (MeasurableEmbedding.subtype_coe
      (Matrix.isOpen_skewAdjointPadicCayleySource
        V.pairingMatrix p).measurableSet |>.measurableSet_image.2 hs))]
  rfl

private def padicCompositeSourceToCayleyTarget
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source →
      padicCayleySpecialOrthogonalTranslatedTarget V.pairingMatrix p 1 :=
  (skewAdjointPadicCayleyTranslatedHomeomorph
      V.pairingMatrix p V.form_det_ne_zero 1) ∘
    (V.padicCompositeTargetToCayleySource p) ∘
      (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
        p).toHomeomorphSourceTarget

private theorem measurableEmbedding_padicCompositeSourceToCayleyTarget
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableEmbedding (V.padicCompositeSourceToCayleyTarget p) :=
  (skewAdjointPadicCayleyTranslatedHomeomorph
      V.pairingMatrix p V.form_det_ne_zero 1
      |>.toMeasurableEquiv.measurableEmbedding).comp
    ((V.measurableEmbedding_padicCompositeTargetToCayleySource p).comp
      ((V.padicCliffordSpinCandidateSkewAdjointIdentityChart p)
        |>.toHomeomorphSourceTarget.toMeasurableEquiv.measurableEmbedding))

private theorem padicCompositeSourceMeasure_eq_comap_cayleyTarget
    (p : ℕ) [Fact (Nat.Prime p)] :
    V.padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure p =
      Measure.comap (V.padicCompositeSourceToCayleyTarget p)
        (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
          p n V.pairingMatrix V.form_det_ne_zero 1) := by
  rw [padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure]
  have hmapSymm :
      Measure.map
          (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
            p).toHomeomorphSourceTarget.symm
          (V.padicCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure p) =
        Measure.comap
          (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
            p).toHomeomorphSourceTarget
          (V.padicCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure p) :=
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p)
      |>.toHomeomorphSourceTarget.toMeasurableEquiv.map_symm
  rw [hmapSymm]
  rw [← V.padicCompositeTargetMeasure_eq_comap p]
  have hskew :
      Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
          p n V.pairingMatrix =
        Measure.comap
          (skewAdjointPadicCayleyTranslatedHomeomorph
            V.pairingMatrix p V.form_det_ne_zero 1)
          (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
            p n V.pairingMatrix V.form_det_ne_zero 1) := by
    rw [← map_padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_chart_symm
      p n V.pairingMatrix V.form_det_ne_zero 1]
    exact (skewAdjointPadicCayleyTranslatedHomeomorph
      V.pairingMatrix p V.form_det_ne_zero 1).toMeasurableEquiv.map_symm
  rw [hskew]
  calc
    Measure.comap
        (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
          p).toHomeomorphSourceTarget
        (Measure.comap (V.padicCompositeTargetToCayleySource p)
          (Measure.comap
            (skewAdjointPadicCayleyTranslatedHomeomorph
              V.pairingMatrix p V.form_det_ne_zero 1)
            (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
              p n V.pairingMatrix V.form_det_ne_zero 1))) =
        Measure.comap
          ((V.padicCompositeTargetToCayleySource p) ∘
            (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
              p).toHomeomorphSourceTarget)
          (Measure.comap
            (skewAdjointPadicCayleyTranslatedHomeomorph
              V.pairingMatrix p V.form_det_ne_zero 1)
            (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
              p n V.pairingMatrix V.form_det_ne_zero 1)) :=
      Measure.comap_comap
        (fun s hs ↦
          (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p)
            |>.toHomeomorphSourceTarget.toMeasurableEquiv.measurableEmbedding
            |>.measurableSet_image.2 hs)
        (V.measurableEmbedding_padicCompositeTargetToCayleySource p).injective
        (fun s hs ↦
          (V.measurableEmbedding_padicCompositeTargetToCayleySource p)
            |>.measurableSet_image.2 hs) _
    _ = Measure.comap (V.padicCompositeSourceToCayleyTarget p)
          (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
            p n V.pairingMatrix V.form_det_ne_zero 1) := by
      calc
        Measure.comap
            ((V.padicCompositeTargetToCayleySource p) ∘
              (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
                p).toHomeomorphSourceTarget)
            (Measure.comap
              (skewAdjointPadicCayleyTranslatedHomeomorph
                V.pairingMatrix p V.form_det_ne_zero 1)
              (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
                p n V.pairingMatrix V.form_det_ne_zero 1)) =
            Measure.comap
              ((skewAdjointPadicCayleyTranslatedHomeomorph
                  V.pairingMatrix p V.form_det_ne_zero 1) ∘
                (V.padicCompositeTargetToCayleySource p) ∘
                  (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
                    p).toHomeomorphSourceTarget)
              (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
                p n V.pairingMatrix V.form_det_ne_zero 1) :=
          Measure.comap_comap
            (fun s hs ↦
              ((V.measurableEmbedding_padicCompositeTargetToCayleySource p).comp
                ((V.padicCliffordSpinCandidateSkewAdjointIdentityChart p)
                  |>.toHomeomorphSourceTarget.toMeasurableEquiv.measurableEmbedding))
                |>.measurableSet_image.2 hs)
            (skewAdjointPadicCayleyTranslatedHomeomorph
              V.pairingMatrix p V.form_det_ne_zero 1
              |>.toMeasurableEquiv.measurableEmbedding).injective
            (fun s hs ↦
              (skewAdjointPadicCayleyTranslatedHomeomorph
                V.pairingMatrix p V.form_det_ne_zero 1
                |>.toMeasurableEquiv.measurableEmbedding.measurableSet_image.2 hs)) _
        _ = Measure.comap (V.padicCompositeSourceToCayleyTarget p)
              (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
                p n V.pairingMatrix V.form_det_ne_zero 1) := by
          rfl

private theorem padicCayleyTargetMeasure_eq_comap
    (p : ℕ) [Fact (Nat.Prime p)] :
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n V.pairingMatrix V.form_det_ne_zero 1 =
      Measure.comap Subtype.val (V.padicInvariantDifferentialGroupMeasure p) := by
  symm
  simpa [padicInvariantDifferentialGroupMeasure] using
    (comap_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero 1)

private theorem padicCompositeSourceMeasure_eq_comap_pointMap
    (p : ℕ) [Fact (Nat.Prime p)] :
    V.padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure p =
      Measure.comap
        (fun x : (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source ↦
          V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.1)
        (V.padicInvariantDifferentialGroupMeasure p) := by
  rw [V.padicCompositeSourceMeasure_eq_comap_cayleyTarget p,
    V.padicCayleyTargetMeasure_eq_comap p]
  rw [Measure.comap_comap
    (fun s hs ↦
      (V.measurableEmbedding_padicCompositeSourceToCayleyTarget p)
        |>.measurableSet_image.2 hs)
    (MeasurableEmbedding.subtype_coe
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
        V.pairingMatrix p 1).measurableSet).injective
    (fun s hs ↦ (MeasurableEmbedding.subtype_coe
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
        V.pairingMatrix p 1).measurableSet |>.measurableSet_image.2 hs))]
  congr 1
  funext x
  let A := V.padicCliffordSpinCandidateIdentityChart p
  let B := V.padicSpecialOrthogonalCayleyIdentityChart p
  let H := skewAdjointPadicCayleyTranslatedHomeomorph
    V.pairingMatrix p V.form_det_ne_zero 1
  have hx : x.1 ∈ (A.trans B).source := x.2
  rw [OpenPartialHomeomorph.trans_source] at hx
  let y : padicCayleySpecialOrthogonalTranslatedTarget V.pairingMatrix p 1 :=
    ⟨A x.1, by
      rw [← V.padicSpecialOrthogonalCayleyIdentityChart_source p]
      exact hx.2⟩
  have hcoord :
      V.padicCompositeTargetToCayleySource p
          ((V.padicCliffordSpinCandidateSkewAdjointIdentityChart p)
            |>.toHomeomorphSourceTarget x) = H.symm y := by
    apply Subtype.ext
    change V.padicCliffordSpinCandidateSkewAdjointIdentityChart p x.1 =
      (H.symm y).1
    change B (A x.1) = (H.symm y).1
    simp [B, padicSpecialOrthogonalCayleyIdentityChart,
      padicSpecialOrthogonalCayleyTargetInclusion,
      padicSkewAdjointCayleySourceInclusion, H, y]
    congr 2
    apply Subtype.ext
    let eT := V.padicSpecialOrthogonalCayleyTargetInclusion p
    have hmem : A x.1 ∈ eT.target := by
      have hB := hx.2
      change A x.1 ∈
        ((V.padicSpecialOrthogonalCayleyTargetInclusion p).symm.trans
          ((skewAdjointPadicCayleyTranslatedHomeomorph
            V.pairingMatrix p V.form_det_ne_zero 1).symm.toOpenPartialHomeomorph.trans
              (V.padicSkewAdjointCayleySourceInclusion p))).source at hB
      rw [OpenPartialHomeomorph.trans_source] at hB
      exact hB.1
    have hr := eT.right_inv hmem
    simpa [eT, padicSpecialOrthogonalCayleyTargetInclusion] using hr
  change (H
    (V.padicCompositeTargetToCayleySource p
      ((V.padicCliffordSpinCandidateSkewAdjointIdentityChart p)
        |>.toHomeomorphSourceTarget x))).1 = _
  rw [hcoord, H.apply_symm_apply]
  change A x.1 = V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.1
  rw [← congrFun (V.padicCliffordSpinCandidateIdentityChart_coe p) x.1]

private theorem padicIdentitySpinSourceMeasure_eq_comap_pointMap
    (p : ℕ) [Fact (Nat.Prime p)] :
    V.padicCliffordSpinCandidateIdentityChartSourceMeasure p =
      Measure.comap
        (fun x : (V.padicCliffordSpinCandidateIdentityChart p).source ↦
          V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.1)
        (V.padicInvariantDifferentialGroupMeasure p) := by
  rw [padicCliffordSpinCandidateIdentityChartSourceMeasure,
    padicCliffordSpinCandidateIdentityChartTargetMeasure]
  have hmapSymm :
      Measure.map
          (V.padicCliffordSpinCandidateIdentityChart
            p).toHomeomorphSourceTarget.symm
          (Measure.comap Subtype.val (V.padicInvariantDifferentialGroupMeasure p)) =
        Measure.comap
          (V.padicCliffordSpinCandidateIdentityChart
            p).toHomeomorphSourceTarget
          (Measure.comap Subtype.val
            (V.padicInvariantDifferentialGroupMeasure p)) :=
    (V.padicCliffordSpinCandidateIdentityChart p)
      |>.toHomeomorphSourceTarget.toMeasurableEquiv.map_symm
  rw [hmapSymm]
  calc
    Measure.comap
        (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget
        (Measure.comap Subtype.val (V.padicInvariantDifferentialGroupMeasure p)) =
        Measure.comap
          (Subtype.val ∘
            (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget)
          (V.padicInvariantDifferentialGroupMeasure p) :=
      Measure.comap_comap
        (fun s hs ↦
          (V.padicCliffordSpinCandidateIdentityChart p)
            |>.toHomeomorphSourceTarget.toMeasurableEquiv.measurableEmbedding
            |>.measurableSet_image.2 hs)
        (MeasurableEmbedding.subtype_coe
          (V.padicCliffordSpinCandidateIdentityChart p).open_target.measurableSet).injective
        (fun s hs ↦ (MeasurableEmbedding.subtype_coe
          (V.padicCliffordSpinCandidateIdentityChart p).open_target.measurableSet
          |>.measurableSet_image.2 hs)) _
    _ = Measure.comap
          (fun x : (V.padicCliffordSpinCandidateIdentityChart p).source ↦
            V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.1)
          (V.padicInvariantDifferentialGroupMeasure p) := by
      congr 1
      funext x
      change V.padicCliffordSpinCandidateIdentityChart p x.1 =
        V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.1
      rw [← congrFun (V.padicCliffordSpinCandidateIdentityChart_coe p) x.1]

/-- The chart-glued local Spin Haar measure pulls back to the already fixed
identity-chart source measure with coefficient one. -/
theorem padicGluedMeasure_comap_identitySource
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.comap Subtype.val
        (V.padicCliffordSpinCandidateChartGluedMeasure p) =
      V.padicCliffordSpinCandidateIdentityChartSourceMeasure p := by
  apply (MeasurableEmbedding.subtype_coe
    (V.padicCliffordSpinCandidateIdentityChart p).open_source.measurableSet).map_injective
  rw [map_comap_subtype_coe
    (V.padicCliffordSpinCandidateIdentityChart p).open_source.measurableSet]
  calc
    (V.padicCliffordSpinCandidateChartGluedMeasure p).restrict
        (V.padicCliffordSpinCandidateIdentityChart p).source =
        (V.padicCliffordSpinCandidateChartGluedMeasure p).restrict
          (V.PadicCliffordSpinCandidateTranslatedChartSource p 1) := by
      congr 1
      ext x
      simp [PadicCliffordSpinCandidateTranslatedChartSource,
        MeasureTheory.TranslatedHomChart.source]
    _ = Measure.map Subtype.val
        (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p 1) :=
      V.restrict_padicCliffordSpinCandidateChartGluedMeasure_source p 1
    _ = Measure.map Subtype.val
        (Measure.map
          (MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph
            (V.padicCliffordSpinCandidateIdentityChart p) 1)
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p)) := by
      rw [V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure_left p]
    _ = Measure.map Subtype.val
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph
          (V.padicCliffordSpinCandidateIdentityChart p) 1).measurable]
      congr 1
      funext x
      simp [MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph]

/-- Equivalently, the existing identity source pushes forward to the
chart-glued local Spin Haar measure restricted to that source. -/
theorem map_padicCliffordSpinCandidateIdentityChartSourceMeasure_subtypeVal
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map Subtype.val
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) =
      (V.padicCliffordSpinCandidateChartGluedMeasure p).restrict
        (V.padicCliffordSpinCandidateIdentityChart p).source := by
  rw [← V.padicGluedMeasure_comap_identitySource p,
    map_comap_subtype_coe
      (V.padicCliffordSpinCandidateIdentityChart p).open_source.measurableSet]

/-- In particular, the chart-glued Haar mass of the identity source is the
total mass of its already fixed source measure. -/
theorem padicCliffordSpinCandidateChartGluedMeasure_identitySource
    (p : ℕ) [Fact (Nat.Prime p)] :
    V.padicCliffordSpinCandidateChartGluedMeasure p
        (V.padicCliffordSpinCandidateIdentityChart p).source =
      V.padicCliffordSpinCandidateIdentityChartSourceMeasure p Set.univ := by
  rw [← Measure.restrict_apply_univ]
  rw [← V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure_subtypeVal p]
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp

private theorem padicCompositeSource_subset_pointSource
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source ⊆
      (V.padicCliffordSpinCandidateIdentityChart p).source := by
  intro x hx
  change x ∈
    ((V.padicCliffordSpinCandidateIdentityChart p).trans
      (V.padicSpecialOrthogonalCayleyIdentityChart p)).source at hx
  rw [OpenPartialHomeomorph.trans_source] at hx
  exact hx.1

private def padicCompositeSourceToPointSource
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source →
      (V.padicCliffordSpinCandidateIdentityChart p).source :=
  openSetInclusion _ _ (V.padicCompositeSource_subset_pointSource p)

private theorem measurableEmbedding_padicCompositeSourceToPointSource
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableEmbedding (V.padicCompositeSourceToPointSource p) :=
  measurableEmbedding_openSetInclusion _ _
    (V.padicCompositeSource_subset_pointSource p)
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).open_source

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the full glued p-adic Spin Haar measure to the exact composite
coordinate source recovers the inverse-Cayley source measure. -/
theorem comap_padicCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChartSource
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.comap Subtype.val
        (V.padicCliffordSpinCandidateChartGluedMeasure p) =
      V.padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure p := by
  calc
    Measure.comap Subtype.val
        (V.padicCliffordSpinCandidateChartGluedMeasure p) =
        Measure.comap (V.padicCompositeSourceToPointSource p)
          (Measure.comap Subtype.val
            (V.padicCliffordSpinCandidateChartGluedMeasure p)) := by
      symm
      rw [Measure.comap_comap
        (fun s hs ↦
          (V.measurableEmbedding_padicCompositeSourceToPointSource p)
            |>.measurableSet_image.2 hs)
        (MeasurableEmbedding.subtype_coe
          (V.padicCliffordSpinCandidateIdentityChart p).open_source.measurableSet).injective
        (fun s hs ↦ (MeasurableEmbedding.subtype_coe
          (V.padicCliffordSpinCandidateIdentityChart p).open_source.measurableSet
          |>.measurableSet_image.2 hs))]
      rfl
    _ = Measure.comap (V.padicCompositeSourceToPointSource p)
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
      rw [V.padicGluedMeasure_comap_identitySource p]
    _ = Measure.comap (V.padicCompositeSourceToPointSource p)
          (Measure.comap
            (fun x : (V.padicCliffordSpinCandidateIdentityChart p).source ↦
              V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.1)
            (V.padicInvariantDifferentialGroupMeasure p)) := by
      rw [V.padicIdentitySpinSourceMeasure_eq_comap_pointMap p]
    _ = Measure.comap
          (fun x : (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source ↦
            V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.1)
          (V.padicInvariantDifferentialGroupMeasure p) := by
      have hf : MeasurableEmbedding
          (fun x : (V.padicCliffordSpinCandidateIdentityChart p).source ↦
            V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.1) := by
        have hcomp := (MeasurableEmbedding.subtype_coe
          (V.padicCliffordSpinCandidateIdentityChart p).open_target.measurableSet).comp
            ((V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget
              |>.toMeasurableEquiv.measurableEmbedding)
        simpa [Function.comp_def,
          ← congrFun (V.padicCliffordSpinCandidateIdentityChart_coe p)] using hcomp
      rw [Measure.comap_comap
        (fun s hs ↦
          (V.measurableEmbedding_padicCompositeSourceToPointSource p)
            |>.measurableSet_image.2 hs)
        hf.injective (fun s hs ↦ hf.measurableSet_image.2 hs)
        (V.padicInvariantDifferentialGroupMeasure p)]
      rfl
    _ = V.padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure p :=
      (V.padicCompositeSourceMeasure_eq_comap_pointMap p).symm

/-- The p-adic skew-adjoint differential coordinate sends the restricted full
Spin Haar measure to the exact inverse-Cayley target density. -/
theorem map_comap_padicCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChart
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
          p).toHomeomorphSourceTarget
        (Measure.comap Subtype.val
          (V.padicCliffordSpinCandidateChartGluedMeasure p)) =
      V.padicCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure p := by
  rw [V.comap_padicCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChartSource p,
    V.map_padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure p]

/-- Equivalently, the ambient p-adic Spin Haar measure restricts to the
pushforward of the packaged inverse-Cayley coordinate-source measure. -/
theorem restrict_padicCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChartSource
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicCliffordSpinCandidateChartGluedMeasure p).restrict
        (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source =
      Measure.map Subtype.val
        (V.padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure p) := by
  rw [← map_comap_subtype_coe
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).open_source.measurableSet,
    V.comap_padicCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChartSource p]

end RationalQuadraticSpaceMatrix
