import SMSFormula.SpecialOrthogonalRealDifferentialInvariance
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar properties of the real differential measure

This module promotes the explicitly glued real differential measure to a Haar
measure. The proof uses the exact recovery theorem on the chart centered at
each point: local finiteness and open positivity are transported from the
target-coordinate density measure, never imposed by rescaling a
reference Haar measure.

The final comparison with an arbitrary Haar measure only records the scalar
supplied by Haar uniqueness. No value is assigned to that scalar here.
-/

noncomputable section

open MeasureTheory
open TopologicalSpace
open Topology
open scoped Matrix.Norms.Operator ContDiff ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realDifferentialHaarGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realDifferentialHaarGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance realDifferentialHaarModelMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realDifferentialHaarModelBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

private theorem isLocallyFiniteMeasure_map_homeomorph
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (e : α ≃ₜ β) (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (Measure.map e μ) := by
  refine ⟨fun y ↦ ?_⟩
  rcases μ.exists_isOpen_measure_lt_top (e.symm y) with
    ⟨U, hyU, hU, hμU⟩
  refine ⟨e.symm ⁻¹' U,
    (hU.preimage e.symm.continuous).mem_nhds hyU, ?_⟩
  rw [Measure.map_apply e.measurable
    (hU.preimage e.symm.continuous).measurableSet]
  have hpreimage : e ⁻¹' (e.symm ⁻¹' U) = U := by
    ext x
    simp
  rw [hpreimage]
  exact hμU

/-- The differential measure on every exact chart source is locally finite. -/
theorem specialFormPreservingSmoothRealChartSourceDensityMeasure_isLocallyFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    IsLocallyFiniteMeasure
      (specialFormPreservingSmoothRealChartSourceDensityMeasure
        F hF hdet g) := by
  letI : IsLocallyFiniteMeasure
      (specialFormPreservingSmoothRealChartTargetDensityMeasure
        F hF hdet g) :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure_isLocallyFinite
      F hF hdet g
  rw [specialFormPreservingSmoothRealChartSourceDensityMeasure]
  exact isLocallyFiniteMeasure_map_homeomorph
    (specialFormPreservingSmoothRealChart
      F hF hdet g).toHomeomorphSourceTarget.symm
    (specialFormPreservingSmoothRealChartTargetDensityMeasure
      F hF hdet g)

/-- The differential measure on every exact chart source is positive on
nonempty open sets. -/
theorem specialFormPreservingSmoothRealChartSourceDensityMeasure_isOpenPosMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.IsOpenPosMeasure
      (specialFormPreservingSmoothRealChartSourceDensityMeasure
        F hF hdet g) := by
  letI : Measure.IsOpenPosMeasure
      (specialFormPreservingSmoothRealChartTargetDensityMeasure
        F hF hdet g) :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure_isOpenPosMeasure
      F hF hdet g
  rw [specialFormPreservingSmoothRealChartSourceDensityMeasure]
  exact
    (specialFormPreservingSmoothRealChart
      F hF hdet g).toHomeomorphSourceTarget.symm.continuous
      |>.isOpenPosMeasure_map
        (specialFormPreservingSmoothRealChart
          F hF hdet g).toHomeomorphSourceTarget.symm.surjective

set_option backward.isDefEq.respectTransparency false in
/-- The real special-orthogonal group is locally compact. This follows from
one exact Cayley chart and does not use a measure. -/
theorem specialFormPreservingRealGroup_locallyCompact
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) := by
  let g :
      specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) := 1
  let e :=
    (specialFormPreservingSmoothRealChart
      F hF hdet g).toHomeomorphSourceTarget
  letI : LocallyCompactSpace
      (specialFormPreservingSmoothRealChart F hF hdet g).target :=
    (specialFormPreservingSmoothRealChart
      F hF hdet g).open_target.locallyCompactSpace
  letI : LocallyCompactSpace
      (specialFormPreservingSmoothRealChart F hF hdet g).source :=
    e.isOpenEmbedding.locallyCompactSpace
  let x :
      (specialFormPreservingSmoothRealChart F hF hdet g).source :=
    ⟨g, self_mem_specialFormPreservingSmoothRealCenteredChartSource
      F hF hdet g⟩
  rcases exists_compact_mem_nhds x with ⟨K, hK, hxK⟩
  let j :
      (specialFormPreservingSmoothRealChart F hF hdet g).source →
        specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) :=
    Subtype.val
  have hj :
      IsOpenEmbedding j :=
    (specialFormPreservingSmoothRealChart
      F hF hdet g).open_source.isOpenEmbedding_subtypeVal
  exact (hK.image hj.continuous).locallyCompactSpace_of_mem_nhds_of_group
    (hj.image_mem_nhds.mpr hxK)

/-- The explicitly glued real differential measure is locally finite. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_isLocallyFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    IsLocallyFiniteMeasure
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) := by
  refine ⟨fun x ↦ ?_⟩
  let C := specialFormPreservingSmoothRealChart F hF hdet x
  let ν :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet x
  letI : IsLocallyFiniteMeasure ν :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure_isLocallyFinite
      F hF hdet x
  let xs : C.source :=
    ⟨x, self_mem_specialFormPreservingSmoothRealCenteredChartSource
      F hF hdet x⟩
  rcases ν.exists_isOpen_measure_lt_top xs with ⟨U, hxU, hU, hνU⟩
  let j : C.source →
      specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) :=
    Subtype.val
  let W := j '' U
  have hj : IsOpenEmbedding j := C.open_source.isOpenEmbedding_subtypeVal
  have hW : IsOpen W := hj.isOpenMap U hU
  have hxW : x ∈ W := ⟨xs, hxU, rfl⟩
  refine ⟨W, hW.mem_nhds hxW, ?_⟩
  have hWS : W ⊆ C.source := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  calc
    specialFormPreservingSmoothRealDifferentialMeasure F hF hdet W =
        (specialFormPreservingSmoothRealDifferentialMeasure
          F hF hdet).restrict C.source W := by
      rw [Measure.restrict_apply hW.measurableSet,
        Set.inter_eq_left.mpr hWS]
    _ = specialFormPreservingSmoothRealChartAmbientDensityMeasure
        F hF hdet x W := by
      rw [restrict_specialFormPreservingSmoothRealDifferentialMeasure_source]
    _ = ν U := by
      rw [specialFormPreservingSmoothRealChartAmbientDensityMeasure,
        Measure.map_apply continuous_subtype_val.measurable hW.measurableSet]
      congr 1
      exact Set.preimage_image_eq U hj.injective
    _ < (⊤ : ℝ≥0∞) := hνU

/-- The explicitly glued real differential measure is finite on compact
sets. -/
theorem
    specialFormPreservingSmoothRealDifferentialMeasure_isFiniteOnCompacts
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    IsFiniteMeasureOnCompacts
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) := by
  letI : IsLocallyFiniteMeasure
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) :=
    specialFormPreservingSmoothRealDifferentialMeasure_isLocallyFinite
      F hF hdet
  set_option synthInstance.maxHeartbeats 200000 in
    infer_instance

instance specialFormPreservingSmoothRealDifferentialMeasure_instFiniteOnCompacts
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    IsFiniteMeasureOnCompacts
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) :=
  specialFormPreservingSmoothRealDifferentialMeasure_isFiniteOnCompacts
    F hF hdet

/-- The explicitly glued real differential measure is positive on every
nonempty open set. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_isOpenPosMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure.IsOpenPosMeasure
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) := by
  refine ⟨fun U hU hUne ↦ ?_⟩
  rcases hUne with ⟨x, hxU⟩
  let C := specialFormPreservingSmoothRealChart F hF hdet x
  let ν :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet x
  letI : Measure.IsOpenPosMeasure ν :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure_isOpenPosMeasure
      F hF hdet x
  let W : Set C.source := Subtype.val ⁻¹' U
  have hW : IsOpen W := hU.preimage continuous_subtype_val
  have hWne : W.Nonempty :=
    ⟨⟨x, self_mem_specialFormPreservingSmoothRealCenteredChartSource
      F hF hdet x⟩, hxU⟩
  exact ne_of_gt <| calc
    0 < ν W := hW.measure_pos ν hWne
    _ = specialFormPreservingSmoothRealChartAmbientDensityMeasure
        F hF hdet x U := by
      rw [specialFormPreservingSmoothRealChartAmbientDensityMeasure,
        Measure.map_apply continuous_subtype_val.measurable hU.measurableSet]
    _ = (specialFormPreservingSmoothRealDifferentialMeasure
        F hF hdet).restrict C.source U := by
      rw [restrict_specialFormPreservingSmoothRealDifferentialMeasure_source]
    _ ≤ specialFormPreservingSmoothRealDifferentialMeasure F hF hdet U :=
      Measure.restrict_apply_le C.source U

instance specialFormPreservingSmoothRealDifferentialMeasure_instOpenPosMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure.IsOpenPosMeasure
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) :=
  specialFormPreservingSmoothRealDifferentialMeasure_isOpenPosMeasure
    F hF hdet

/-- The real differential measure is a Haar measure at the scale fixed by
the rational invariant differential. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure.IsHaarMeasure
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) where
  toIsFiniteMeasureOnCompacts :=
    specialFormPreservingSmoothRealDifferentialMeasure_isFiniteOnCompacts
      F hF hdet
  toIsMulLeftInvariant :=
    specialFormPreservingSmoothRealDifferentialMeasure_isMulLeftInvariant
      F hF hdet
  toIsOpenPosMeasure :=
    specialFormPreservingSmoothRealDifferentialMeasure_isOpenPosMeasure
      F hF hdet

instance specialFormPreservingSmoothRealDifferentialMeasure_instHaarMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure.IsHaarMeasure
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) :=
  specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
    F hF hdet

/-- The real differential measure is regular. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_regular
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure.Regular
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) := by
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_locallyCompact F hF hdet
  letI : SecondCountableTopology
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_secondCountable F
  letI : IsLocallyFiniteMeasure
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) :=
    specialFormPreservingSmoothRealDifferentialMeasure_isLocallyFinite
      F hF hdet
  infer_instance

/-- Haar uniqueness compares the differential normalization with any real
reference Haar measure by a scalar determined by the identity-chart scale. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_eq_haarScalarFactor_smul
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (μ : Measure
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))))
    [Measure.IsHaarMeasure μ] :
    specialFormPreservingSmoothRealDifferentialMeasure F hF hdet =
      Measure.haarScalarFactor
          (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) μ •
        μ := by
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_locallyCompact F hF hdet
  letI : SecondCountableTopology
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_secondCountable F
  letI : IsFiniteMeasureOnCompacts
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) :=
    specialFormPreservingSmoothRealDifferentialMeasure_isFiniteOnCompacts
      F hF hdet
  set_option synthInstance.maxHeartbeats 200000 in
    exact Measure.isMulLeftInvariant_eq_smul
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) μ

end PositiveDefiniteIntegralLattice
