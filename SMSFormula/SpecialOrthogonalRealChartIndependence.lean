import SMSFormula.SpecialOrthogonalRealChartGluing

/-!
# Independence of the real differential chart measure

This module identifies both overlap-density measures with pullbacks of their
chart-source differential measures. It then compares the induced ambient chart
measures on every same-point overlap.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator ContDiff ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realIndependenceGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realIndependenceGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance realIndependenceModelMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realIndependenceModelBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- On a same-point overlap, the native right target coordinate is exactly
the right chart coordinate of the same group point. -/
theorem coe_specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :
    ((specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromRight
      F hF hdet g h x).1 :
        (specialFormPreservingSmoothRealChart F hF hdet h).target) =
      (specialFormPreservingSmoothRealChart F hF hdet h).toHomeomorphSourceTarget
        (specialFormPreservingSmoothRealChartSourceOverlapToRight
          F hF hdet g h x) := by
  rfl

/-- Pulling the right chart-source differential measure back along the
same-point inclusion recovers the right overlap-density measure. -/
theorem comap_specialFormPreservingSmoothRealChartSourceDensityMeasure_right
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.comap
        (specialFormPreservingSmoothRealChartSourceOverlapToRight
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceDensityMeasure
          F hF hdet h) =
      specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight
        F hF hdet g h := by
  let i :=
    specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h
  let e :=
    (specialFormPreservingSmoothRealChart
      F hF hdet h).toHomeomorphSourceTarget
  let u :=
    specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromRight
      F hF hdet g h
  let j :
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
          F hF hdet g h →
        (specialFormPreservingSmoothRealChart F hF hdet h).target :=
    Subtype.val
  let μ :=
    specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight
      F hF hdet g h
  let ν :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet h
  let ρ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet h
  let τ :=
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight
      F hF hdet g h
  have hi :
      MeasurableEmbedding i :=
    measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h
  have he : MeasurableEmbedding e :=
    e.toMeasurableEquiv.measurableEmbedding
  have hu : MeasurableEmbedding u :=
    u.toMeasurableEquiv.measurableEmbedding
  have hj : MeasurableEmbedding j :=
    MeasurableEmbedding.subtype_coe
      (measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
        F hF hdet g h)
  rw [specialFormPreservingSmoothRealChartSourceDensityMeasure_eq_target_comap]
  calc
    Measure.comap i (Measure.comap e ρ) =
        Measure.comap (e ∘ i) ρ :=
      Measure.comap_comap
        (fun s hs => hi.measurableSet_image.2 hs) he.injective
        (fun s hs => he.measurableSet_image.2 hs) ρ
    _ = Measure.comap (j ∘ u) ρ := by
      rfl
    _ = Measure.comap u (Measure.comap j ρ) := by
      symm
      exact Measure.comap_comap
        (fun s hs => hu.measurableSet_image.2 hs) hj.injective
        (fun s hs => hj.measurableSet_image.2 hs) ρ
    _ = Measure.comap u τ := by
      rfl
    _ = Measure.map u.symm τ :=
      u.toMeasurableEquiv.map_symm.symm
    _ = μ := by
      have hmap : Measure.map u μ = τ :=
        map_specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight_native
          F hF hdet g h
      calc
        Measure.map u.symm τ =
            Measure.map u.symm (Measure.map u μ) :=
          congrArg (Measure.map u.symm) hmap.symm
        _ = μ := MeasurableEquiv.map_symm_map u.toMeasurableEquiv

/-- The right overlap-density measure maps to the restriction of the right
chart-source differential measure to the exact same-point overlap. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapToRight
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight
          F hF hdet g h) =
      (specialFormPreservingSmoothRealChartSourceDensityMeasure
        F hF hdet h).restrict
        (specialFormPreservingSmoothRealChartSourceOverlapWithinRight
          F hF hdet g h) := by
  rw [← comap_specialFormPreservingSmoothRealChartSourceDensityMeasure_right
    F hF hdet g h,
    (measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h).map_comap,
    range_specialFormPreservingSmoothRealChartSourceOverlapToRight F hF hdet g h]

/-- The differential measure induced by one centered chart, returned to the
ambient real special-orthogonal group. -/
def specialFormPreservingSmoothRealChartAmbientDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  Measure.map Subtype.val
    (specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet g)

/-- Two centered charts induce the same ambient differential measure after
restriction to their exact same-point overlap. -/
theorem restrict_specialFormPreservingSmoothRealChartAmbientDensityMeasure_overlap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealChartAmbientDensityMeasure
      F hF hdet g).restrict
        (specialFormPreservingSmoothRealChart F hF hdet h).source =
      (specialFormPreservingSmoothRealChartAmbientDensityMeasure
        F hF hdet h).restrict
          (specialFormPreservingSmoothRealChart F hF hdet g).source := by
  let μL :=
    specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft
      F hF hdet g h
  let μR :=
    specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight
      F hF hdet g h
  let iL :=
    specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h
  let iR :=
    specialFormPreservingSmoothRealChartSourceOverlapToRight
      F hF hdet g h
  let jL :
      (specialFormPreservingSmoothRealChart F hF hdet g).source →
        specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) :=
    Subtype.val
  let jR :
      (specialFormPreservingSmoothRealChart F hF hdet h).source →
        specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) :=
    Subtype.val
  calc
    (specialFormPreservingSmoothRealChartAmbientDensityMeasure
      F hF hdet g).restrict
        (specialFormPreservingSmoothRealChart F hF hdet h).source =
        Measure.map jL
          ((specialFormPreservingSmoothRealChartSourceDensityMeasure
            F hF hdet g).restrict
              (specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
                F hF hdet g h)) := by
      exact Measure.restrict_map continuous_subtype_val.measurable
        (specialFormPreservingSmoothRealChart F hF hdet h).open_source.measurableSet
    _ = Measure.map jL (Measure.map iL μL) := by
      rw [map_specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft_source]
    _ = Measure.map (jL ∘ iL) μL := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (measurable_specialFormPreservingSmoothRealChartSourceOverlapToLeft
          F hF hdet g h)]
    _ = Measure.map
          (Subtype.val :
            specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h →
              specialFormPreservingMatrixSubgroup
                (F.map (algebraMap ℚ ℝ))) μL := by
      rfl
    _ = Measure.map
          (Subtype.val :
            specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h →
              specialFormPreservingMatrixSubgroup
                (F.map (algebraMap ℚ ℝ))) μR := by
      exact congrArg (Measure.map
        (Subtype.val :
          specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h →
            specialFormPreservingMatrixSubgroup
              (F.map (algebraMap ℚ ℝ))))
        (specialFormPreservingSmoothRealChartSourceOverlapDensityMeasure_eq
          F hF hdet g h)
    _ = Measure.map (jR ∘ iR) μR := by
      rfl
    _ = Measure.map jR (Measure.map iR μR) := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (measurable_specialFormPreservingSmoothRealChartSourceOverlapToRight
          F hF hdet g h)]
    _ = Measure.map jR
          ((specialFormPreservingSmoothRealChartSourceDensityMeasure
            F hF hdet h).restrict
              (specialFormPreservingSmoothRealChartSourceOverlapWithinRight
                F hF hdet g h)) := by
      rw [map_specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight_source]
    _ = (specialFormPreservingSmoothRealChartAmbientDensityMeasure
        F hF hdet h).restrict
          (specialFormPreservingSmoothRealChart F hF hdet g).source := by
      symm
      exact Measure.restrict_map continuous_subtype_val.measurable
        (specialFormPreservingSmoothRealChart F hF hdet g).open_source.measurableSet

/-- A disjoint atlas contribution is exactly its assigned ambient chart
measure restricted to the assigned piece. -/
theorem specialFormPreservingSmoothRealChartCoverPieceMeasure_eq_restrict_ambient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ) :
    specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet k =
      (specialFormPreservingSmoothRealChartAmbientDensityMeasure F hF hdet
        (specialFormPreservingSmoothRealChartCoverCenter
          F hF hdet k)).restrict
        (specialFormPreservingSmoothRealChartCoverPiece F hF hdet k) := by
  symm
  exact Measure.restrict_map continuous_subtype_val.measurable
    (measurableSet_specialFormPreservingSmoothRealChartCoverPiece
      F hF hdet k)

/-- Inside a selected chart, every disjoint atlas contribution is the
selected chart measure restricted to that contribution's piece. -/
theorem restrict_specialFormPreservingSmoothRealChartCoverPieceMeasure_selected_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k m : ℕ) :
    (specialFormPreservingSmoothRealChartCoverPieceMeasure
      F hF hdet k).restrict
        (specialFormPreservingSmoothRealChart F hF hdet
          (specialFormPreservingSmoothRealChartCoverCenter
            F hF hdet m)).source =
      (specialFormPreservingSmoothRealChartAmbientDensityMeasure F hF hdet
        (specialFormPreservingSmoothRealChartCoverCenter
          F hF hdet m)).restrict
        (specialFormPreservingSmoothRealChartCoverPiece F hF hdet k) := by
  let g :=
    specialFormPreservingSmoothRealChartCoverCenter F hF hdet k
  let h :=
    specialFormPreservingSmoothRealChartCoverCenter F hF hdet m
  let P :=
    specialFormPreservingSmoothRealChartCoverPiece F hF hdet k
  let U :=
    (specialFormPreservingSmoothRealChart F hF hdet h).source
  let V :=
    (specialFormPreservingSmoothRealChart F hF hdet g).source
  have hP : MeasurableSet P :=
    measurableSet_specialFormPreservingSmoothRealChartCoverPiece
      F hF hdet k
  have hU : MeasurableSet U :=
    (specialFormPreservingSmoothRealChart F hF hdet h).open_source.measurableSet
  have hPV : P ⊆ V :=
    specialFormPreservingSmoothRealChartCoverPiece_subset_source
      F hF hdet k
  rw [specialFormPreservingSmoothRealChartCoverPieceMeasure_eq_restrict_ambient]
  calc
    ((specialFormPreservingSmoothRealChartAmbientDensityMeasure
      F hF hdet g).restrict P).restrict U =
        ((specialFormPreservingSmoothRealChartAmbientDensityMeasure
          F hF hdet g).restrict U).restrict P := by
      rw [Measure.restrict_restrict hU, Measure.restrict_restrict hP]
      congr 1
      exact Set.inter_comm _ _
    _ = ((specialFormPreservingSmoothRealChartAmbientDensityMeasure
          F hF hdet h).restrict V).restrict P := by
      rw [restrict_specialFormPreservingSmoothRealChartAmbientDensityMeasure_overlap
        F hF hdet g h]
    _ = (specialFormPreservingSmoothRealChartAmbientDensityMeasure
          F hF hdet h).restrict P := by
      rw [Measure.restrict_restrict hP]
      congr 1
      exact Set.inter_eq_left.mpr hPV

/-- The glued real differential measure restricts to every selected chart as
the differential measure induced by that chart. -/
theorem restrict_specialFormPreservingSmoothRealDifferentialMeasure_selected_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (m : ℕ) :
    (specialFormPreservingSmoothRealDifferentialMeasure
      F hF hdet).restrict
        (specialFormPreservingSmoothRealChart F hF hdet
          (specialFormPreservingSmoothRealChartCoverCenter
            F hF hdet m)).source =
      specialFormPreservingSmoothRealChartAmbientDensityMeasure F hF hdet
        (specialFormPreservingSmoothRealChartCoverCenter
          F hF hdet m) := by
  let h :=
    specialFormPreservingSmoothRealChartCoverCenter F hF hdet m
  let U :=
    (specialFormPreservingSmoothRealChart F hF hdet h).source
  let ν :=
    specialFormPreservingSmoothRealChartAmbientDensityMeasure F hF hdet h
  let P :=
    specialFormPreservingSmoothRealChartCoverPiece F hF hdet
  calc
    (specialFormPreservingSmoothRealDifferentialMeasure
      F hF hdet).restrict U =
        Measure.sum (fun k =>
          (specialFormPreservingSmoothRealChartCoverPieceMeasure
            F hF hdet k).restrict U) := by
      ext s hs
      rw [Measure.restrict_apply hs,
        specialFormPreservingSmoothRealDifferentialMeasure,
        Measure.sum_apply _
          (hs.inter
            (specialFormPreservingSmoothRealChart
              F hF hdet h).open_source.measurableSet),
        Measure.sum_apply _ hs]
      congr 1
      funext k
      rw [Measure.restrict_apply hs]
    _ = Measure.sum (fun k => ν.restrict (P k)) := by
      congr 1
      funext k
      exact
        restrict_specialFormPreservingSmoothRealChartCoverPieceMeasure_selected_source
          F hF hdet k m
    _ = ν := by
      symm
      exact measure_eq_sum_restrict_of_disjoint_iUnion_eq_univ ν P
        (measurableSet_specialFormPreservingSmoothRealChartCoverPiece
          F hF hdet)
        (pairwiseDisjoint_specialFormPreservingSmoothRealChartCoverPiece
          F hF hdet)
        (iUnion_specialFormPreservingSmoothRealChartCoverPiece F hF hdet)

/-- Pulling the glued measure back to a selected exact chart source recovers
the chart-source differential measure. -/
theorem comap_specialFormPreservingSmoothRealDifferentialMeasure_selected_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (m : ℕ) :
    Measure.comap Subtype.val
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) =
      specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet
        (specialFormPreservingSmoothRealChartCoverCenter
          F hF hdet m) := by
  let h :=
    specialFormPreservingSmoothRealChartCoverCenter F hF hdet m
  let i :
      (specialFormPreservingSmoothRealChart F hF hdet h).source →
        specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) :=
    Subtype.val
  apply
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealChart
        F hF hdet h).open_source.measurableSet).map_injective
  calc
    Measure.map i
        (Measure.comap i
          (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)) =
        (specialFormPreservingSmoothRealDifferentialMeasure
          F hF hdet).restrict (Set.range i) :=
      (MeasurableEmbedding.subtype_coe
        (specialFormPreservingSmoothRealChart
          F hF hdet h).open_source.measurableSet).map_comap _
    _ = (specialFormPreservingSmoothRealDifferentialMeasure
          F hF hdet).restrict
          (specialFormPreservingSmoothRealChart F hF hdet h).source := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    _ = specialFormPreservingSmoothRealChartAmbientDensityMeasure
          F hF hdet h :=
      restrict_specialFormPreservingSmoothRealDifferentialMeasure_selected_source
        F hF hdet m
    _ = Measure.map i
          (specialFormPreservingSmoothRealChartSourceDensityMeasure
            F hF hdet h) := by
      rfl

/-- The selected chart restrictions uniquely determine the glued real
differential measure. This is the cover-independence principle used by any
alternative countable chart disjointization. -/
theorem measure_eq_specialFormPreservingSmoothRealDifferentialMeasure_of_selected_restrict
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (μ : Measure
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))))
    (hμ : ∀ m,
      μ.restrict
          (specialFormPreservingSmoothRealChart F hF hdet
            (specialFormPreservingSmoothRealChartCoverCenter
              F hF hdet m)).source =
        specialFormPreservingSmoothRealChartAmbientDensityMeasure F hF hdet
          (specialFormPreservingSmoothRealChartCoverCenter
            F hF hdet m)) :
    μ = specialFormPreservingSmoothRealDifferentialMeasure F hF hdet := by
  let P :=
    specialFormPreservingSmoothRealChartCoverPiece F hF hdet
  have hpiece : ∀ k,
      μ.restrict (P k) =
        (specialFormPreservingSmoothRealDifferentialMeasure
          F hF hdet).restrict (P k) := by
    intro k
    let h :=
      specialFormPreservingSmoothRealChartCoverCenter F hF hdet k
    let U :=
      (specialFormPreservingSmoothRealChart F hF hdet h).source
    have hP : MeasurableSet (P k) :=
      measurableSet_specialFormPreservingSmoothRealChartCoverPiece
        F hF hdet k
    have hPU : P k ⊆ U :=
      specialFormPreservingSmoothRealChartCoverPiece_subset_source
        F hF hdet k
    calc
      μ.restrict (P k) = (μ.restrict U).restrict (P k) := by
        rw [Measure.restrict_restrict hP]
        congr 1
        exact (Set.inter_eq_left.mpr hPU).symm
      _ = ((specialFormPreservingSmoothRealDifferentialMeasure
            F hF hdet).restrict U).restrict (P k) := by
        rw [hμ k,
          restrict_specialFormPreservingSmoothRealDifferentialMeasure_selected_source
            F hF hdet k]
      _ = (specialFormPreservingSmoothRealDifferentialMeasure
            F hF hdet).restrict (P k) := by
        rw [Measure.restrict_restrict hP]
        congr 1
        exact Set.inter_eq_left.mpr hPU
  calc
    μ = Measure.sum (fun k => μ.restrict (P k)) :=
      measure_eq_sum_restrict_of_disjoint_iUnion_eq_univ μ P
        (measurableSet_specialFormPreservingSmoothRealChartCoverPiece
          F hF hdet)
        (pairwiseDisjoint_specialFormPreservingSmoothRealChartCoverPiece
          F hF hdet)
        (iUnion_specialFormPreservingSmoothRealChartCoverPiece F hF hdet)
    _ = Measure.sum (fun k =>
        (specialFormPreservingSmoothRealDifferentialMeasure
          F hF hdet).restrict (P k)) := by
      congr 1
      funext k
      exact hpiece k
    _ = specialFormPreservingSmoothRealDifferentialMeasure F hF hdet := by
      symm
      exact measure_eq_sum_restrict_of_disjoint_iUnion_eq_univ
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) P
        (measurableSet_specialFormPreservingSmoothRealChartCoverPiece
          F hF hdet)
        (pairwiseDisjoint_specialFormPreservingSmoothRealChartCoverPiece
          F hF hdet)
        (iUnion_specialFormPreservingSmoothRealChartCoverPiece F hF hdet)

end PositiveDefiniteIntegralLattice
