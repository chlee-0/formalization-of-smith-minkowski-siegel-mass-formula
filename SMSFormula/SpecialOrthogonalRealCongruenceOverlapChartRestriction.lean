import SMSFormula.SpecialOrthogonalRealCongruenceOverlapGroupTransport

/-!
# Chart restrictions on the real congruence common overlap

This module identifies the two measures induced on the common group overlap
with restrictions of the transported source chart and the independently
selected target identity chart.  All comparisons use ordinary subtype
inclusions and measurable embeddings.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceOverlapChartRestrictionSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceOverlapChartRestrictionSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance realCongruenceOverlapChartRestrictionTargetMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceOverlapChartRestrictionTargetBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance realCongruenceOverlapChartRestrictionGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realCongruenceOverlapChartRestrictionGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The full target identity-chart density measure, returned to its ambient
tangent carrier, is restriction of the ambient coordinate measure weighted
by the zero-extended standard density. -/
theorem map_specialFormPreservingSmoothRealCongruenceTargetIdentityDensityMeasure_ambient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealChartTargetDensityMeasure
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1) =
      ((Matrix.skewAdjointRealCoordinateDetMeasure
        (Matrix.skewAdjointCongruenceForm F W) 0).restrict
          (specialFormPreservingSmoothRealIdentityChart
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target).withDensity
        (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
          F hF hdet W) := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let i : (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target →
      (skewAdjointMatricesLieSubalgebra
        (F'.map (algebraMap ℚ ℝ))).toSubmodule := Subtype.val
  let μ := Measure.comap i
    (Matrix.skewAdjointRealCoordinateDetMeasure F' 0)
  let f :=
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F' hF' hdet' 1
  let g :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
      F hF hdet W
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
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target).withDensity g
  rw [hfg, map_withDensity_comp_of_measurable i μ g
    continuous_subtype_val.measurable
    (measurable_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
      F hF hdet W)]
  rw [map_comap_subtype_coe
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').open_target.measurableSet]

/-- The source identity-chart target-density measure, returned to its ambient
tangent carrier, is restriction weighted by the ambient source density. -/
theorem map_specialFormPreservingSmoothRealCongruenceSourceIdentityDensityMeasure_ambient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealChartTargetDensityMeasure
          F hF hdet 1) =
      ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).target).withDensity
          (specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
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
    specialFormPreservingSmoothRealCongruenceAmbientSourceDensity F hF hdet
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
    (measurable_specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
      F hF hdet)]
  rw [map_comap_subtype_coe I.open_target.measurableSet]

/-- Every point of the ambient standard target overlap belongs to the target
identity-chart target. -/
theorem mem_target_of_mem_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    {z : (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule}
    (hz : z ∈
      specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W) :
    z ∈
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target := by
  have hEq :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet_eq
      F hF hdet W
  exact ((Set.ext_iff.mp hEq z).mp hz).1

/-- Inclusion of the ambient standard target overlap into the target
identity-chart target. -/
def specialFormPreservingSmoothRealCongruenceAmbientStandardTargetToIdentityTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W →
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target :=
  fun z => ⟨z.1,
    mem_target_of_mem_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
      F hF hdet W z.2⟩

/-- The standard ambient overlap viewed as a measurable subset of the target
identity-chart target. -/
def specialFormPreservingSmoothRealCongruenceAmbientStandardTargetWithinIdentityTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target :=
  Subtype.val ⁻¹'
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
      F hF hdet W

/-- Identity-on-coordinates homeomorphism from the ambient overlap subtype to
the corresponding subset of the target identity-chart target. -/
def specialFormPreservingSmoothRealCongruenceAmbientStandardTargetWithinIdentityTargetHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W ≃ₜ
      specialFormPreservingSmoothRealCongruenceAmbientStandardTargetWithinIdentityTarget
        F hF hdet W where
  toFun z := ⟨
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetToIdentityTarget
      F hF hdet W z, z.2⟩
  invFun z := ⟨z.1.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The standard target-overlap inclusion is a measurable embedding. -/
theorem measurableEmbedding_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetToIdentityTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    MeasurableEmbedding
      (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetToIdentityTarget
        F hF hdet W) := by
  let e :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetWithinIdentityTargetHomeomorph
      F hF hdet W
  have he : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  have hi : MeasurableEmbedding
      (Subtype.val :
        specialFormPreservingSmoothRealCongruenceAmbientStandardTargetWithinIdentityTarget
            F hF hdet W →
          (specialFormPreservingSmoothRealIdentityChart
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target) :=
    MeasurableEmbedding.subtype_coe
      ((measurableSet_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W).preimage continuous_subtype_val.measurable)
  simpa [e, Function.comp_def,
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetWithinIdentityTargetHomeomorph]
    using hi.comp he

/-- The standard ambient overlap measure is exactly the restriction of the
target identity-chart density measure after inclusion into its target. -/
theorem map_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure_identityTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetToIdentityTarget
          F hF hdet W)
        (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure
          F hF hdet W) =
      (specialFormPreservingSmoothRealChartTargetDensityMeasure
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1).restrict
          (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetWithinIdentityTarget
            F hF hdet W) := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  let T :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
      F hF hdet W
  let j :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetToIdentityTarget
      F hF hdet W
  let τ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure F' hF' hdet' 1
  let μt :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure
      F hF hdet W
  let ν := Matrix.skewAdjointRealCoordinateDetMeasure F' 0
  let g :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
      F hF hdet W
  have hT : MeasurableSet T :=
    measurableSet_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
      F hF hdet W
  have hsub : T ⊆ J.target := fun _ hz =>
    mem_target_of_mem_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
      F hF hdet W hz
  apply (MeasurableEmbedding.subtype_coe J.open_target.measurableSet).map_injective
  calc
    Measure.map Subtype.val (Measure.map j μt) =
        Measure.map Subtype.val μt := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (measurableEmbedding_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetToIdentityTarget
          F hF hdet W).measurable]
      apply Measure.map_congr
      filter_upwards [] with z
      rfl
    _ = (ν.restrict T).withDensity g := by
      rw [map_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure]
    _ = ((ν.restrict J.target).withDensity g).restrict T := by
      rw [restrict_withDensity hT, Measure.restrict_restrict hT]
      congr 2
      exact (Set.inter_eq_left.mpr hsub).symm
    _ = (Measure.map Subtype.val τ).restrict T := by
      rw [map_specialFormPreservingSmoothRealCongruenceTargetIdentityDensityMeasure_ambient]
    _ = Measure.map Subtype.val
        (τ.restrict
          (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetWithinIdentityTarget
            F hF hdet W)) := by
      symm
      rw [Measure.restrict_map continuous_subtype_val.measurable hT]
      rfl

/-- Inclusion of the common group overlap into the target identity-chart
source. -/
def specialFormPreservingSmoothRealCongruenceGroupOverlapToTargetIdentitySource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartGroupOverlap
        F hF hdet W →
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source :=
  fun q => ⟨q.1, q.2.2⟩

/-- The common overlap as a subset of the target identity-chart source. -/
def specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source :=
  Subtype.val ⁻¹'
    specialFormPreservingSmoothRealCongruenceChartSourceSet F hF hdet W

/-- The target-source internal common overlap is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    MeasurableSet
      (specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource
        F hF hdet W) :=
  (isOpen_specialFormPreservingSmoothRealCongruenceChartSourceSet
    F hF hdet W).measurableSet.preimage continuous_subtype_val.measurable

/-- Target identity coordinates in the standard ambient overlap are exactly
the preimage of the common group set under the inverse target chart. -/
theorem preimage_specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).toHomeomorphSourceTarget.symm ⁻¹'
        specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource
          F hF hdet W =
      specialFormPreservingSmoothRealCongruenceAmbientStandardTargetWithinIdentityTarget
        F hF hdet W := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  ext z
  change
    J.symm z ∈
        specialFormPreservingSmoothRealCongruenceChartSourceSet F hF hdet W ↔
      z.1 ∈
        specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
          F hF hdet W
  rw [specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet_eq]
  change
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).symm
          (J.symm z) ∈
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).source ↔
      z.1 ∈ J.target ∧
        (specialFormPreservingRealCongruenceContinuousMulEquiv F W).symm
            (J.symm z) ∈
          (specialFormPreservingSmoothRealIdentityChart F hF hdet).source
  exact ⟨fun hz => ⟨z.2, hz⟩, fun hz => hz.2⟩

/-- The standard induced common-group measure is exactly the target identity
chart-source differential measure restricted to the common overlap. -/
theorem map_specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure_targetIdentitySource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceGroupOverlapToTargetIdentitySource
          F hF hdet W)
        (specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure
          F hF hdet W) =
      (specialFormPreservingSmoothRealChartSourceDensityMeasure
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1).restrict
          (specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource
            F hF hdet W) := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  let R :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapToGroup
      F hF hdet W
  let jt :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetToIdentityTarget
      F hF hdet W
  let jg :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapToTargetIdentitySource
      F hF hdet W
  let μt :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure
      F hF hdet W
  let τ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure F' hF' hdet' 1
  let P :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetWithinIdentityTarget
      F hF hdet W
  let Q :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource
      F hF hdet W
  have hjg : Measurable jg :=
    (continuous_subtype_val.subtype_mk _).measurable
  change Measure.map jg (Measure.map R μt) =
    (Measure.map J.toHomeomorphSourceTarget.symm τ).restrict Q
  calc
    Measure.map jg (Measure.map R μt) =
        Measure.map J.toHomeomorphSourceTarget.symm
          (Measure.map jt μt) := by
      rw [Measure.map_map hjg R.measurable,
        Measure.map_map J.toHomeomorphSourceTarget.symm.measurable
          (measurableEmbedding_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetToIdentityTarget
            F hF hdet W).measurable]
      apply Measure.map_congr
      filter_upwards [] with z
      apply Subtype.ext
      rfl
    _ = Measure.map J.toHomeomorphSourceTarget.symm (τ.restrict P) := by
      rw [map_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure_identityTarget]
    _ = (Measure.map J.toHomeomorphSourceTarget.symm τ).restrict Q := by
      symm
      rw [Measure.restrict_map
        J.toHomeomorphSourceTarget.symm.measurable
        (measurableSet_specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource
          F hF hdet W),
        preimage_specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource]

/-- Inclusion of the fixed-source ambient overlap into the source identity
chart target. -/
def specialFormPreservingSmoothRealCongruenceAmbientSourceToIdentityTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W →
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
  fun x => ⟨x.1, x.2.1⟩

/-- The ambient source overlap as a subset of the source identity-chart
target. -/
def specialFormPreservingSmoothRealCongruenceAmbientSourceWithinIdentityTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
  Subtype.val ⁻¹'
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W

/-- The source ambient overlap is a measurable subset of the source identity
chart target. -/
theorem measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceWithinIdentityTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    MeasurableSet
      (specialFormPreservingSmoothRealCongruenceAmbientSourceWithinIdentityTarget
        F hF hdet W) :=
  (measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
    F hF hdet W).preimage continuous_subtype_val.measurable

/-- The fixed-source overlap inclusion is a measurable embedding. -/
theorem measurableEmbedding_specialFormPreservingSmoothRealCongruenceAmbientSourceToIdentityTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    MeasurableEmbedding
      (specialFormPreservingSmoothRealCongruenceAmbientSourceToIdentityTarget
        F hF hdet W) := by
  let P :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceWithinIdentityTarget
      F hF hdet W
  let e :
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
          F hF hdet W ≃ₜ P := {
    toFun := fun x => ⟨
      specialFormPreservingSmoothRealCongruenceAmbientSourceToIdentityTarget
        F hF hdet W x, x.2⟩
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
      (measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceWithinIdentityTarget
        F hF hdet W)
  simpa [e, P, Function.comp_def] using hi.comp he

/-- The fixed-source overlap measure is the restriction of the source
identity-chart target-density measure after inclusion. -/
theorem map_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure_identityTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceAmbientSourceToIdentityTarget
          F hF hdet W)
        (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure
          F hF hdet W) =
      (specialFormPreservingSmoothRealChartTargetDensityMeasure
        F hF hdet 1).restrict
          (specialFormPreservingSmoothRealCongruenceAmbientSourceWithinIdentityTarget
            F hF hdet W) := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let U :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W
  let j :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceToIdentityTarget
      F hF hdet W
  let τ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet 1
  let μs :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure
      F hF hdet W
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  let g :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceDensity F hF hdet
  have hU : MeasurableSet U :=
    measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W
  have hsub : U ⊆ I.target := fun _ hx => hx.1
  apply (MeasurableEmbedding.subtype_coe I.open_target.measurableSet).map_injective
  calc
    Measure.map Subtype.val (Measure.map j μs) =
        Measure.map Subtype.val μs := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (measurableEmbedding_specialFormPreservingSmoothRealCongruenceAmbientSourceToIdentityTarget
          F hF hdet W).measurable]
      apply Measure.map_congr
      filter_upwards [] with x
      rfl
    _ = (μ.restrict U).withDensity g := by
      rw [map_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure]
    _ = ((μ.restrict I.target).withDensity g).restrict U := by
      rw [restrict_withDensity hU, Measure.restrict_restrict hU]
      congr 2
      exact (Set.inter_eq_left.mpr hsub).symm
    _ = (Measure.map Subtype.val τ).restrict U := by
      rw [map_specialFormPreservingSmoothRealCongruenceSourceIdentityDensityMeasure_ambient]
    _ = Measure.map Subtype.val
        (τ.restrict
          (specialFormPreservingSmoothRealCongruenceAmbientSourceWithinIdentityTarget
            F hF hdet W)) := by
      symm
      rw [Measure.restrict_map continuous_subtype_val.measurable hU]
      rfl

/-- Inclusion of the common group overlap into the transported chart source. -/
def specialFormPreservingSmoothRealCongruenceGroupOverlapToTransportedSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartGroupOverlap
        F hF hdet W →
      specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W :=
  fun q => ⟨q.1, q.2.1⟩

/-- The common overlap as a subset of the transported chart source. -/
def specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set (specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W) :=
  Subtype.val ⁻¹'
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source

/-- The transported-source internal common overlap is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    MeasurableSet
      (specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
        F hF hdet W) :=
  (specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)).open_source.measurableSet.preimage
      continuous_subtype_val.measurable

/-- Pulling the transported-source common overlap back through source-chart
coordinates gives the fixed-source ambient overlap. -/
theorem preimage_specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    ((specialFormPreservingSmoothRealIdentityChart F hF hdet
        ).toHomeomorphSourceTarget.symm.trans
      (specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
        F hF hdet W)) ⁻¹'
        specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
          F hF hdet W =
      specialFormPreservingSmoothRealCongruenceAmbientSourceWithinIdentityTarget
        F hF hdet W := by
  ext x
  change
    specialFormPreservingRealCongruenceContinuousMulEquiv F W
          ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x) ∈
        (specialFormPreservingSmoothRealIdentityChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source ↔
      x.1 ∈
        specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
          F hF hdet W
  change
    specialFormPreservingRealCongruenceContinuousMulEquiv F W
          ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x) ∈
        (specialFormPreservingSmoothRealIdentityChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source ↔
      x.1 ∈ (specialFormPreservingSmoothRealIdentityChart F hF hdet).target ∧
        specialFormPreservingRealCongruenceContinuousMulEquiv F W
            ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x) ∈
          (specialFormPreservingSmoothRealIdentityChart
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source
  exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩

/-- The transported induced common-group measure is exactly the transported
chart-source differential measure restricted to the common overlap. -/
theorem map_specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceGroupOverlapToTransportedSource
          F hF hdet W)
        (specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure
          F hF hdet W) =
      (specialFormPreservingSmoothRealCongruenceChartSourceDensityMeasure
        F hF hdet W).restrict
          (specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
            F hF hdet W) := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let es :=
    specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
      F hF hdet W
  let L := I.toHomeomorphSourceTarget.symm.trans es
  let S :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapToGroup
      F hF hdet W
  let jt :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceToIdentityTarget
      F hF hdet W
  let jg :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapToTransportedSource
      F hF hdet W
  let μs :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure
      F hF hdet W
  let τ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet 1
  let P :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceWithinIdentityTarget
      F hF hdet W
  let Q :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
      F hF hdet W
  have hjg : Measurable jg :=
    (continuous_subtype_val.subtype_mk _).measurable
  have hL :
      Measure.map L τ =
        specialFormPreservingSmoothRealCongruenceChartSourceDensityMeasure
          F hF hdet W := by
    rw [specialFormPreservingSmoothRealCongruenceChartSourceDensityMeasure,
      specialFormPreservingSmoothRealChartSourceDensityMeasure]
    rw [Measure.map_map es.measurable
      I.toHomeomorphSourceTarget.symm.measurable]
    rfl
  change Measure.map jg (Measure.map S μs) =
    (specialFormPreservingSmoothRealCongruenceChartSourceDensityMeasure
      F hF hdet W).restrict Q
  calc
    Measure.map jg (Measure.map S μs) =
        Measure.map L (Measure.map jt μs) := by
      rw [Measure.map_map hjg S.measurable,
        Measure.map_map L.measurable
          (measurableEmbedding_specialFormPreservingSmoothRealCongruenceAmbientSourceToIdentityTarget
            F hF hdet W).measurable]
      apply Measure.map_congr
      filter_upwards [] with x
      apply Subtype.ext
      rfl
    _ = Measure.map L (τ.restrict P) := by
      rw [map_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure_identityTarget]
    _ = (Measure.map L τ).restrict Q := by
      symm
      rw [Measure.restrict_map L.measurable
        (measurableSet_specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
          F hF hdet W),
        preimage_specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource]
    _ = (specialFormPreservingSmoothRealCongruenceChartSourceDensityMeasure
          F hF hdet W).restrict Q := by rw [hL]

end PositiveDefiniteIntegralLattice
