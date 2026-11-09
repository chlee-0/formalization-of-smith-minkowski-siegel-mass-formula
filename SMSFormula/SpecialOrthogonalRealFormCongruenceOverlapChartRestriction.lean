import SMSFormula.SpecialOrthogonalRealFormCongruenceOverlapGroupTransport

/-!
# Native chart restrictions for explicit real-congruence overlaps

This module identifies the source and standard-target overlap measures with
restrictions of the corresponding native identity-chart density measures.
Only ordinary subtype inclusions and measurable embeddings are used.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realFormCongruenceOverlapChartRestrictionSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realFormCongruenceOverlapChartRestrictionSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance realFormCongruenceOverlapChartRestrictionGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realFormCongruenceOverlapChartRestrictionGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The source differential density transported through the explicit group
congruence to the transported chart source. -/
def specialFormPreservingSmoothRealFormCongruenceChartSourceDensityMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure
      (specialFormPreservingSmoothRealFormCongruenceChartSource
        F F' hF hdet c) :=
  Measure.map
    (specialFormPreservingSmoothRealFormCongruenceChartSourceHomeomorph
      F F' hF hdet c)
    (specialFormPreservingSmoothRealChartSourceDensityMeasure
      F hF hdet 1)

/-- The full target identity-chart density measure, returned to its ambient
tangent carrier, is the target-coordinate restriction weighted by the
zero-extended standard density. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceTargetIdentityDensityMeasure_ambient
    (F' : Matrix (Fin n) (Fin n) ℚ)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealChartTargetDensityMeasure
          F' hF' hdet' 1) =
      ((Matrix.skewAdjointRealCoordinateDetMeasure F' 0).restrict
        (specialFormPreservingSmoothRealIdentityChart
          F' hF' hdet').target).withDensity
        (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
          F' hF' hdet') := by
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  let i : J.target →
      (skewAdjointMatricesLieSubalgebra
        (F'.map (algebraMap ℚ ℝ))).toSubmodule := Subtype.val
  let μ := Measure.comap i
    (Matrix.skewAdjointRealCoordinateDetMeasure F' 0)
  let f :=
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F' hF' hdet' 1
  let g :=
    specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
      F' hF' hdet'
  have hfg : f = g ∘ i := by
    funext z
    change
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
          F' hF' hdet' 1 z =
        Function.extend Subtype.val
          (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
            F' hF' hdet' 1) (fun _ => 0) z.1
    exact
      (Function.Injective.extend_apply Subtype.val_injective _ _ z).symm
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure]
  change Measure.map i (μ.withDensity f) =
    ((Matrix.skewAdjointRealCoordinateDetMeasure F' 0).restrict
      J.target).withDensity g
  rw [hfg, map_withDensity_comp_of_measurable i μ g
    continuous_subtype_val.measurable
    (measurable_specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
      F' hF' hdet')]
  rw [map_comap_subtype_coe J.open_target.measurableSet]

/-- The source identity-chart target-density measure, returned to its ambient
tangent carrier, is the source-coordinate restriction weighted by the
zero-extended source density. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceSourceIdentityDensityMeasure_ambient
    (F : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealChartTargetDensityMeasure
          F hF hdet 1) =
      ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).target).withDensity
          (specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
            F hF hdet) := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let i : I.target →
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule := Subtype.val
  let μ := Measure.comap i
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0)
  let f :=
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal F hF hdet 1
  let g :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity F hF hdet
  have hfg : f = g ∘ i := by
    funext z
    change
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
          F hF hdet 1 z =
        Function.extend Subtype.val
          (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
            F hF hdet 1) (fun _ => 0) z.1
    exact
      (Function.Injective.extend_apply Subtype.val_injective _ _ z).symm
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure]
  change Measure.map i (μ.withDensity f) =
    ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
      I.target).withDensity g
  rw [hfg, map_withDensity_comp_of_measurable i μ g
    continuous_subtype_val.measurable
    (measurable_specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
      F hF hdet)]
  rw [map_comap_subtype_coe I.open_target.measurableSet]

/-- Every standard target-overlap coordinate belongs to the target identity
chart target. -/
theorem mem_target_of_mem_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    {z : (skewAdjointMatricesLieSubalgebra
      (F'.map (algebraMap ℚ ℝ))).toSubmodule}
    (hz : z ∈
      specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c) :
    z ∈
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target :=
  hz.1

/-- Inclusion of the standard target overlap into the target identity-chart
target. -/
def specialFormPreservingSmoothRealFormCongruenceStandardTargetToIdentityTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c →
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target :=
  fun z => ⟨z.1,
    mem_target_of_mem_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
      F F' hF hdet hF' hdet' c z.2⟩

/-- The standard target overlap viewed inside the target identity-chart
target. -/
def specialFormPreservingSmoothRealFormCongruenceStandardTargetWithinIdentityTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target :=
  Subtype.val ⁻¹'
    specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
      F F' hF hdet hF' hdet' c

/-- Identity-on-coordinates homeomorphism from the standard target overlap to
its copy inside the target identity-chart target. -/
def specialFormPreservingSmoothRealFormCongruenceStandardTargetWithinIdentityTargetHomeomorph
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c ≃ₜ
      specialFormPreservingSmoothRealFormCongruenceStandardTargetWithinIdentityTarget
        F F' hF hdet hF' hdet' c where
  toFun z := ⟨
    specialFormPreservingSmoothRealFormCongruenceStandardTargetToIdentityTarget
      F F' hF hdet hF' hdet' c z, z.2⟩
  invFun z := ⟨z.1.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The standard target-overlap inclusion is a measurable embedding. -/
theorem measurableEmbedding_specialFormPreservingSmoothRealFormCongruenceStandardTargetToIdentityTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    MeasurableEmbedding
      (specialFormPreservingSmoothRealFormCongruenceStandardTargetToIdentityTarget
        F F' hF hdet hF' hdet' c) := by
  let e :=
    specialFormPreservingSmoothRealFormCongruenceStandardTargetWithinIdentityTargetHomeomorph
      F F' hF hdet hF' hdet' c
  have he : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  have hi : MeasurableEmbedding
      (Subtype.val :
        specialFormPreservingSmoothRealFormCongruenceStandardTargetWithinIdentityTarget
            F F' hF hdet hF' hdet' c →
          (specialFormPreservingSmoothRealIdentityChart
            F' hF' hdet').target) :=
    MeasurableEmbedding.subtype_coe
      ((isOpen_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c).measurableSet.preimage
          continuous_subtype_val.measurable)
  simpa [e, Function.comp_def,
    specialFormPreservingSmoothRealFormCongruenceStandardTargetWithinIdentityTargetHomeomorph]
    using hi.comp he

/-- The standard target overlap measure is the restriction of the target
identity-chart density measure after inclusion into its target. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure_identityTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map
        (specialFormPreservingSmoothRealFormCongruenceStandardTargetToIdentityTarget
          F F' hF hdet hF' hdet' c)
        (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure
          F F' hF hdet hF' hdet' c) =
      (specialFormPreservingSmoothRealChartTargetDensityMeasure
        F' hF' hdet' 1).restrict
          (specialFormPreservingSmoothRealFormCongruenceStandardTargetWithinIdentityTarget
            F F' hF hdet hF' hdet' c) := by
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  let T :=
    specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
      F F' hF hdet hF' hdet' c
  let j :=
    specialFormPreservingSmoothRealFormCongruenceStandardTargetToIdentityTarget
      F F' hF hdet hF' hdet' c
  let τ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure F' hF' hdet' 1
  let μt :=
    specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure
      F F' hF hdet hF' hdet' c
  let ν := Matrix.skewAdjointRealCoordinateDetMeasure F' 0
  let g :=
    specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
      F' hF' hdet'
  have hT : MeasurableSet T :=
    (isOpen_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
      F F' hF hdet hF' hdet' c).measurableSet
  have hsub : T ⊆ J.target := fun _ hz => hz.1
  apply (MeasurableEmbedding.subtype_coe J.open_target.measurableSet).map_injective
  calc
    Measure.map Subtype.val (Measure.map j μt) =
        Measure.map Subtype.val μt := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (measurableEmbedding_specialFormPreservingSmoothRealFormCongruenceStandardTargetToIdentityTarget
          F F' hF hdet hF' hdet' c).measurable]
      apply Measure.map_congr
      filter_upwards [] with z
      rfl
    _ = (ν.restrict T).withDensity g := by
      rw [
        map_specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure]
    _ = ((ν.restrict J.target).withDensity g).restrict T := by
      rw [restrict_withDensity hT, Measure.restrict_restrict hT]
      congr 2
      exact (Set.inter_eq_left.mpr hsub).symm
    _ = (Measure.map Subtype.val τ).restrict T := by
      rw [
        map_specialFormPreservingSmoothRealFormCongruenceTargetIdentityDensityMeasure_ambient]
    _ = Measure.map Subtype.val
        (τ.restrict
          (specialFormPreservingSmoothRealFormCongruenceStandardTargetWithinIdentityTarget
            F F' hF hdet hF' hdet' c)) := by
      symm
      rw [Measure.restrict_map continuous_subtype_val.measurable hT]
      rfl

/-- Inclusion of the source ambient overlap into the source identity-chart
target. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientSourceToIdentityTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c →
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
  fun x => ⟨x.1, x.2.1⟩

/-- The source ambient overlap viewed inside the source identity-chart
target. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientSourceWithinIdentityTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
  Subtype.val ⁻¹'
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c

/-- The source ambient overlap is measurable inside the source identity-chart
target. -/
theorem measurableSet_specialFormPreservingSmoothRealFormCongruenceAmbientSourceWithinIdentityTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    MeasurableSet
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceWithinIdentityTarget
        F F' hF hdet hF' hdet' c) :=
  (isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
    F F' hF hdet hF' hdet' c).measurableSet.preimage
      continuous_subtype_val.measurable

/-- The source overlap inclusion is a measurable embedding. -/
theorem measurableEmbedding_specialFormPreservingSmoothRealFormCongruenceAmbientSourceToIdentityTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    MeasurableEmbedding
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceToIdentityTarget
        F F' hF hdet hF' hdet' c) := by
  let P :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceWithinIdentityTarget
      F F' hF hdet hF' hdet' c
  let e :
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
          F F' hF hdet hF' hdet' c ≃ₜ P := {
    toFun := fun x => ⟨
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceToIdentityTarget
        F F' hF hdet hF' hdet' c x, x.2⟩
    invFun := fun x => ⟨x.1.1, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun :=
      (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  }
  have he : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  have hi : MeasurableEmbedding
      (Subtype.val : P →
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).target) :=
    MeasurableEmbedding.subtype_coe
      (measurableSet_specialFormPreservingSmoothRealFormCongruenceAmbientSourceWithinIdentityTarget
        F F' hF hdet hF' hdet' c)
  simpa [e, P, Function.comp_def] using hi.comp he

/-- The source overlap measure is the restriction of the source identity-chart
target-density measure after inclusion. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure_identityTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map
        (specialFormPreservingSmoothRealFormCongruenceAmbientSourceToIdentityTarget
          F F' hF hdet hF' hdet' c)
        (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure
          F F' hF hdet hF' hdet' c) =
      (specialFormPreservingSmoothRealChartTargetDensityMeasure
        F hF hdet 1).restrict
          (specialFormPreservingSmoothRealFormCongruenceAmbientSourceWithinIdentityTarget
            F F' hF hdet hF' hdet' c) := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let U :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c
  let j :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceToIdentityTarget
      F F' hF hdet hF' hdet' c
  let τ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet 1
  let μs :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure
      F F' hF hdet hF' hdet' c
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  let g :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity F hF hdet
  have hU : MeasurableSet U :=
    (isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c).measurableSet
  have hsub : U ⊆ I.target := fun _ hx => hx.1
  apply (MeasurableEmbedding.subtype_coe I.open_target.measurableSet).map_injective
  calc
    Measure.map Subtype.val (Measure.map j μs) =
        Measure.map Subtype.val μs := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (measurableEmbedding_specialFormPreservingSmoothRealFormCongruenceAmbientSourceToIdentityTarget
          F F' hF hdet hF' hdet' c).measurable]
      apply Measure.map_congr
      filter_upwards [] with x
      rfl
    _ = (μ.restrict U).withDensity g := by
      rw [
        map_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure]
    _ = ((μ.restrict I.target).withDensity g).restrict U := by
      rw [restrict_withDensity hU, Measure.restrict_restrict hU]
      congr 2
      exact (Set.inter_eq_left.mpr hsub).symm
    _ = (Measure.map Subtype.val τ).restrict U := by
      rw [
        map_specialFormPreservingSmoothRealFormCongruenceSourceIdentityDensityMeasure_ambient]
    _ = Measure.map Subtype.val
        (τ.restrict
          (specialFormPreservingSmoothRealFormCongruenceAmbientSourceWithinIdentityTarget
            F F' hF hdet hF' hdet' c)) := by
      symm
      rw [Measure.restrict_map continuous_subtype_val.measurable hU]
      rfl

end PositiveDefiniteIntegralLattice
