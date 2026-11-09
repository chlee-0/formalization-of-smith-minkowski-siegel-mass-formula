import SMSFormula.SpecialOrthogonalRealChartIndependence

/-!
# Left invariance of the real differential measure

This module proves that changing the center of a full real chart transports
its differential measure by the corresponding left translation. It then uses
the countable-atlas uniqueness theorem to prove left invariance of the glued
measure.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator ContDiff ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realInvarianceGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realInvarianceGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance realInvarianceModelMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realInvarianceModelBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The exact target-coordinate identification between two centered charts.
It is the identity on the underlying skew-adjoint coordinate matrix. -/
def specialFormPreservingSmoothRealChartTargetCenterHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealChart F hF hdet g).target ≃ₜ
      (specialFormPreservingSmoothRealChart F hF hdet h).target :=
  (specialFormPreservingSmoothRealChartTargetHomeomorph F hF hdet g).trans
    (specialFormPreservingSmoothRealChartTargetHomeomorph F hF hdet h).symm

@[simp]
theorem coe_specialFormPreservingSmoothRealChartTargetCenterHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    ((specialFormPreservingSmoothRealChartTargetCenterHomeomorph
      F hF hdet g h y).1 :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) = y.1 := by
  let Tg :=
    specialFormPreservingSmoothRealChartTargetHomeomorph F hF hdet g
  let Th :=
    specialFormPreservingSmoothRealChartTargetHomeomorph F hF hdet h
  change ((Th.symm (Tg y)).1 :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) = y.1
  calc
    ((Th.symm (Tg y)).1 :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) =
        (Th (Th.symm (Tg y))).1 := by
      symm
      exact coe_specialFormPreservingSmoothRealChartTargetHomeomorph_apply
        F hF hdet h (Th.symm (Tg y))
    _ = (Tg y).1 := congrArg Subtype.val (Th.apply_symm_apply (Tg y))
    _ = y.1 :=
      coe_specialFormPreservingSmoothRealChartTargetHomeomorph_apply
        F hF hdet g y

/-- The invariant differential density is unchanged by the identity
identification of two centered target-coordinate subtypes. -/
theorem specialFormPreservingSmoothRealChartCoordinateDensityENNReal_center
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal F hF hdet h
        (specialFormPreservingSmoothRealChartTargetCenterHomeomorph
          F hF hdet g h y) =
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet g y := by
  let e :=
    specialFormPreservingSmoothRealChartTargetCenterHomeomorph
      F hF hdet g h
  let D :=
    specialFormPreservingSmoothRealDiagonalPartialJacobian F hF hdet
  calc
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet h (e y) =
        ENNReal.ofReal (D (e y).1) :=
      congrArg ENNReal.ofReal
        (specialFormPreservingSmoothRealChartCoordinateDensity_eq_diagonalPartialJacobian
          F hF hdet h (e y))
    _ = ENNReal.ofReal (D y.1) := by
      exact congrArg (fun z => ENNReal.ofReal (D z))
        (coe_specialFormPreservingSmoothRealChartTargetCenterHomeomorph_apply
          F hF hdet g h y)
    _ = specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet g y :=
      congrArg ENNReal.ofReal
        (specialFormPreservingSmoothRealChartCoordinateDensity_eq_diagonalPartialJacobian
          F hF hdet g y).symm

private theorem map_withDensity_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) {f : α → ENNReal} (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs,
    setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp

private theorem map_comap_measurableEquiv_of_commutes
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (e : α ≃ᵐ β) (i : α → γ) (j : β → γ)
    (hi : MeasurableEmbedding i) (hj : MeasurableEmbedding j)
    (hcomm : ∀ x, j (e x) = i x)
    (hrange : Set.range i = Set.range j) (μ : Measure γ) :
    Measure.map e (Measure.comap i μ) = Measure.comap j μ := by
  apply hj.map_injective
  calc
    Measure.map j (Measure.map e (Measure.comap i μ)) =
        Measure.map (j ∘ e) (Measure.comap i μ) := by
      rw [Measure.map_map hj.measurable e.measurable]
    _ = Measure.map i (Measure.comap i μ) := by
      apply Measure.map_congr
      filter_upwards [] with x
      exact hcomm x
    _ = μ.restrict (Set.range i) := hi.map_comap μ
    _ = μ.restrict (Set.range j) := congrArg μ.restrict hrange
    _ = Measure.map j (Measure.comap j μ) := (hj.map_comap μ).symm

/-- The two exact centered target-coordinate subtypes have the same range in
the ambient skew-adjoint model. -/
theorem range_specialFormPreservingSmoothRealChartTarget_center
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Set.range
        (Subtype.val :
          (specialFormPreservingSmoothRealChart F hF hdet g).target →
            (skewAdjointMatricesLieSubalgebra
              (F.map (algebraMap ℚ ℝ))).toSubmodule) =
      Set.range
        (Subtype.val :
          (specialFormPreservingSmoothRealChart F hF hdet h).target →
            (skewAdjointMatricesLieSubalgebra
              (F.map (algebraMap ℚ ℝ))).toSubmodule) := by
  rw [Subtype.range_val, Subtype.range_val]
  ext z
  constructor
  · intro hz
    let y : (specialFormPreservingSmoothRealChart F hF hdet g).target :=
      ⟨z, hz⟩
    let ey :=
      specialFormPreservingSmoothRealChartTargetCenterHomeomorph
        F hF hdet g h y
    have hey : (ey.1 :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) = z :=
      coe_specialFormPreservingSmoothRealChartTargetCenterHomeomorph_apply
        F hF hdet g h y
    exact hey ▸ ey.2
  · intro hz
    let y : (specialFormPreservingSmoothRealChart F hF hdet h).target :=
      ⟨z, hz⟩
    let ey :=
      specialFormPreservingSmoothRealChartTargetCenterHomeomorph
        F hF hdet h g y
    have hey : (ey.1 :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) = z :=
      coe_specialFormPreservingSmoothRealChartTargetCenterHomeomorph_apply
        F hF hdet h g y
    exact hey ▸ ey.2

/-- The identity target-coordinate identification transports the restricted
additive coordinate measure between any two centered target subtypes. -/
theorem map_specialFormPreservingSmoothRealChartTargetCoordinateMeasure_center
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartTargetCenterHomeomorph
          F hF hdet g h)
        (Measure.comap Subtype.val
          (Matrix.skewAdjointRealCoordinateDetMeasure F 0)) =
      Measure.comap Subtype.val
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0) := by
  let e :=
    specialFormPreservingSmoothRealChartTargetCenterHomeomorph
      F hF hdet g h
  let iG :
      (specialFormPreservingSmoothRealChart F hF hdet g).target →
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule :=
    Subtype.val
  let iH :
      (specialFormPreservingSmoothRealChart F hF hdet h).target →
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule :=
    Subtype.val
  exact map_comap_measurableEquiv_of_commutes
    e.toMeasurableEquiv iG iH
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealChart F hF hdet g).open_target.measurableSet)
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealChart F hF hdet h).open_target.measurableSet)
    (fun y =>
      coe_specialFormPreservingSmoothRealChartTargetCenterHomeomorph_apply
        F hF hdet g h y)
    (range_specialFormPreservingSmoothRealChartTarget_center
      F hF hdet g h)
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0)

/-- The identity target-coordinate identification transports the differential
density measure between any two centered target subtypes. -/
theorem map_specialFormPreservingSmoothRealChartTargetDensityMeasure_center
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartTargetCenterHomeomorph
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartTargetDensityMeasure
          F hF hdet g) =
      specialFormPreservingSmoothRealChartTargetDensityMeasure
        F hF hdet h := by
  let e :=
    specialFormPreservingSmoothRealChartTargetCenterHomeomorph
      F hF hdet g h
  let μG :=
    Measure.comap
      (Subtype.val :
        (specialFormPreservingSmoothRealChart F hF hdet g).target →
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule)
      (Matrix.skewAdjointRealCoordinateDetMeasure F 0)
  let μH :=
    Measure.comap
      (Subtype.val :
        (specialFormPreservingSmoothRealChart F hF hdet h).target →
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule)
      (Matrix.skewAdjointRealCoordinateDetMeasure F 0)
  let JG :=
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet g
  let JH :=
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet h
  change Measure.map e (μG.withDensity JG) = μH.withDensity JH
  calc
    Measure.map e (μG.withDensity JG) =
        (Measure.map e μG).withDensity (JG ∘ e.symm) :=
      map_withDensity_measurableEquiv e.toMeasurableEquiv μG
        (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
          F hF hdet g)
    _ = μH.withDensity (JG ∘ e.symm) := by
      rw [show Measure.map e μG = μH from
        map_specialFormPreservingSmoothRealChartTargetCoordinateMeasure_center
          F hF hdet g h]
    _ = μH.withDensity JH := by
      apply withDensity_congr_ae
      filter_upwards [] with y
      have hy :=
        specialFormPreservingSmoothRealChartCoordinateDensityENNReal_center
          F hF hdet g h (e.symm y)
      change JH (e (e.symm y)) = JG (e.symm y) at hy
      rw [e.apply_symm_apply] at hy
      exact hy.symm

/-- Changing chart centers commutes pointwise with the target
coordinates. It is stated pointwise to avoid dependent function equality. -/
theorem specialFormPreservingSmoothRealChartSourceHomeomorph_target
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealChart F hF hdet g).source) :
    (specialFormPreservingSmoothRealChart F hF hdet h).toHomeomorphSourceTarget
        (specialFormPreservingSmoothRealChartSourceHomeomorph
          F hF hdet g h x) =
      specialFormPreservingSmoothRealChartTargetCenterHomeomorph
        F hF hdet g h
        ((specialFormPreservingSmoothRealChart
          F hF hdet g).toHomeomorphSourceTarget x) := by
  let Th :=
    specialFormPreservingSmoothRealChartTargetHomeomorph F hF hdet h
  apply Th.injective
  simp [specialFormPreservingSmoothRealChartTargetCenterHomeomorph,
    specialFormPreservingSmoothRealChartSourceHomeomorph,
    specialFormPreservingSmoothRealLeftMulChartSourceHomeomorph,
    specialFormPreservingSmoothRealChartSourceTargetHomeomorph,
    Th]

/-- The same center-change square, solved pointwise for the inverse native
chart coordinate. -/
theorem specialFormPreservingSmoothRealChartSourceHomeomorph_symm_target
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart F hF hdet g).target) :
    specialFormPreservingSmoothRealChartSourceHomeomorph
        F hF hdet g h
        ((specialFormPreservingSmoothRealChart
          F hF hdet g).toHomeomorphSourceTarget.symm y) =
      (specialFormPreservingSmoothRealChart
        F hF hdet h).toHomeomorphSourceTarget.symm
        (specialFormPreservingSmoothRealChartTargetCenterHomeomorph
          F hF hdet g h y) := by
  let A :=
    (specialFormPreservingSmoothRealChart
      F hF hdet g).toHomeomorphSourceTarget
  let B :=
    (specialFormPreservingSmoothRealChart
      F hF hdet h).toHomeomorphSourceTarget
  let E :=
    specialFormPreservingSmoothRealChartSourceHomeomorph
      F hF hdet g h
  let e :=
    specialFormPreservingSmoothRealChartTargetCenterHomeomorph
      F hF hdet g h
  apply B.injective
  change B (E (A.symm y)) = B (B.symm (e y))
  rw [B.apply_symm_apply]
  have hy :=
    specialFormPreservingSmoothRealChartSourceHomeomorph_target
      F hF hdet g h (A.symm y)
  change B (E (A.symm y)) = e (A (A.symm y)) at hy
  rwa [A.apply_symm_apply] at hy

private theorem map_map_symm_conjugate
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (A : α ≃ᵐ β) (B : γ ≃ᵐ δ) (E : α ≃ᵐ γ) (e : β ≃ᵐ δ)
    (μ : Measure β) (ν : Measure δ)
    (hcomm : ∀ y, E (A.symm y) = B.symm (e y))
    (hmap : Measure.map e μ = ν) :
    Measure.map E (Measure.map A.symm μ) = Measure.map B.symm ν := by
  calc
    Measure.map E (Measure.map A.symm μ) =
        Measure.map (E ∘ A.symm) μ := by
      rw [Measure.map_map E.measurable A.symm.measurable]
    _ = Measure.map (B.symm ∘ e) μ := by
      apply Measure.map_congr
      filter_upwards [] with y
      exact hcomm y
    _ = Measure.map B.symm (Measure.map e μ) := by
      symm
      rw [Measure.map_map B.symm.measurable e.measurable]
    _ = Measure.map B.symm ν := congrArg (Measure.map B.symm) hmap

/-- The full source-coordinate center change transports the differential
measure. Its underlying map is left multiplication by `h * g⁻¹`. -/
theorem map_specialFormPreservingSmoothRealChartSourceDensityMeasure_center
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceHomeomorph
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceDensityMeasure
          F hF hdet g) =
      specialFormPreservingSmoothRealChartSourceDensityMeasure
        F hF hdet h := by
  rw [specialFormPreservingSmoothRealChartSourceDensityMeasure,
    specialFormPreservingSmoothRealChartSourceDensityMeasure]
  exact map_map_symm_conjugate
    (specialFormPreservingSmoothRealChart
      F hF hdet g).toHomeomorphSourceTarget.toMeasurableEquiv
    (specialFormPreservingSmoothRealChart
      F hF hdet h).toHomeomorphSourceTarget.toMeasurableEquiv
    (specialFormPreservingSmoothRealChartSourceHomeomorph
      F hF hdet g h).toMeasurableEquiv
    (specialFormPreservingSmoothRealChartTargetCenterHomeomorph
      F hF hdet g h).toMeasurableEquiv
    (specialFormPreservingSmoothRealChartTargetDensityMeasure
      F hF hdet g)
    (specialFormPreservingSmoothRealChartTargetDensityMeasure
      F hF hdet h)
    (specialFormPreservingSmoothRealChartSourceHomeomorph_symm_target
      F hF hdet g h)
    (map_specialFormPreservingSmoothRealChartTargetDensityMeasure_center
      F hF hdet g h)

/-- Inside an arbitrary centered chart, every disjoint atlas contribution is
that chart's ambient differential measure restricted to the assigned piece. -/
theorem restrict_specialFormPreservingSmoothRealChartCoverPieceMeasure_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ)
    (h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealChartCoverPieceMeasure
      F hF hdet k).restrict
        (specialFormPreservingSmoothRealChart F hF hdet h).source =
      (specialFormPreservingSmoothRealChartAmbientDensityMeasure F hF hdet
        h).restrict
        (specialFormPreservingSmoothRealChartCoverPiece F hF hdet k) := by
  let g :=
    specialFormPreservingSmoothRealChartCoverCenter F hF hdet k
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

/-- The glued real differential measure restricts to every centered chart,
not only the centers selected by the countable subcover. -/
theorem restrict_specialFormPreservingSmoothRealDifferentialMeasure_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealDifferentialMeasure
      F hF hdet).restrict
        (specialFormPreservingSmoothRealChart F hF hdet h).source =
      specialFormPreservingSmoothRealChartAmbientDensityMeasure
        F hF hdet h := by
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
        restrict_specialFormPreservingSmoothRealChartCoverPieceMeasure_source
          F hF hdet k h
    _ = ν := by
      symm
      exact measure_eq_sum_restrict_of_disjoint_iUnion_eq_univ ν P
        (measurableSet_specialFormPreservingSmoothRealChartCoverPiece
          F hF hdet)
        (pairwiseDisjoint_specialFormPreservingSmoothRealChartCoverPiece
          F hF hdet)
        (iUnion_specialFormPreservingSmoothRealChartCoverPiece F hF hdet)

/-- On an exact chart source, the center change from `g` to `a * g` is
pointwise left multiplication by `a`. -/
theorem mul_left_eq_specialFormPreservingSmoothRealChartSourceHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : (specialFormPreservingSmoothRealChart F hF hdet g).source) :
    (Homeomorph.mulLeft a) x.1 =
      (specialFormPreservingSmoothRealChartSourceHomeomorph
        F hF hdet g (a * g) x).1 := by
  rw [coe_specialFormPreservingSmoothRealChartSourceHomeomorph_apply]
  simp [mul_assoc]

private theorem map_map_of_commutes
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (L : β ≃ᵐ δ) (i : α → β) (E : α ≃ᵐ γ) (j : γ → δ)
    (hi : Measurable i) (hj : Measurable j)
    (μ : Measure α) (ν : Measure γ)
    (hcomm : ∀ x, L (i x) = j (E x))
    (hmap : Measure.map E μ = ν) :
    Measure.map L (Measure.map i μ) = Measure.map j ν := by
  calc
    Measure.map L (Measure.map i μ) =
        Measure.map (L ∘ i) μ := by
      rw [Measure.map_map L.measurable hi]
    _ = Measure.map (j ∘ E) μ := by
      apply Measure.map_congr
      filter_upwards [] with x
      exact hcomm x
    _ = Measure.map j (Measure.map E μ) := by
      symm
      rw [Measure.map_map hj E.measurable]
    _ = Measure.map j ν := congrArg (Measure.map j) hmap

/-- Left multiplication transports one ambient centered chart measure to the
chart measure centered at the translated center. -/
theorem map_specialFormPreservingSmoothRealChartAmbientDensityMeasure_mul_left
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map (Homeomorph.mulLeft a)
        (specialFormPreservingSmoothRealChartAmbientDensityMeasure
          F hF hdet g) =
      specialFormPreservingSmoothRealChartAmbientDensityMeasure
        F hF hdet (a * g) := by
  rw [specialFormPreservingSmoothRealChartAmbientDensityMeasure,
    specialFormPreservingSmoothRealChartAmbientDensityMeasure]
  exact map_map_of_commutes
    (Homeomorph.mulLeft a).toMeasurableEquiv
    (Subtype.val :
      (specialFormPreservingSmoothRealChart F hF hdet g).source →
        specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (specialFormPreservingSmoothRealChartSourceHomeomorph
      F hF hdet g (a * g)).toMeasurableEquiv
    (Subtype.val :
      (specialFormPreservingSmoothRealChart
        F hF hdet (a * g)).source →
          specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    continuous_subtype_val.measurable
    continuous_subtype_val.measurable
    (specialFormPreservingSmoothRealChartSourceDensityMeasure
      F hF hdet g)
    (specialFormPreservingSmoothRealChartSourceDensityMeasure
      F hF hdet (a * g))
    (mul_left_eq_specialFormPreservingSmoothRealChartSourceHomeomorph
      F hF hdet a g)
    (map_specialFormPreservingSmoothRealChartSourceDensityMeasure_center
      F hF hdet g (a * g))

/-- The inverse image of the chart centered at `a * g` under left
multiplication by `a` is exactly the chart centered at `g`. -/
theorem preimage_mul_left_specialFormPreservingSmoothRealChart_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (Homeomorph.mulLeft a) ⁻¹'
        (specialFormPreservingSmoothRealChart
          F hF hdet (a * g)).source =
      (specialFormPreservingSmoothRealChart F hF hdet g).source := by
  ext x
  constructor
  · intro hx
    let y :
        (specialFormPreservingSmoothRealChart
          F hF hdet (a * g)).source :=
      ⟨(Homeomorph.mulLeft a) x, hx⟩
    let z :=
      specialFormPreservingSmoothRealChartSourceHomeomorph
        F hF hdet (a * g) g y
    have hz : z.1 = x := by
      rw [coe_specialFormPreservingSmoothRealChartSourceHomeomorph_apply]
      change (g * (a * g)⁻¹) * (a * x) = x
      simp
    exact hz ▸ z.2
  · intro hx
    let y :
        (specialFormPreservingSmoothRealChart F hF hdet g).source :=
      ⟨x, hx⟩
    let z :=
      specialFormPreservingSmoothRealChartSourceHomeomorph
        F hF hdet g (a * g) y
    have hz : (Homeomorph.mulLeft a) x = z.1 :=
      mul_left_eq_specialFormPreservingSmoothRealChartSourceHomeomorph
        F hF hdet a g y
    change (Homeomorph.mulLeft a) x ∈
      (specialFormPreservingSmoothRealChart F hF hdet (a * g)).source
    rw [hz]
    exact z.2

/-- The preimage formula expressed with an arbitrary target center. -/
theorem preimage_mul_left_specialFormPreservingSmoothRealChart_source'
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (Homeomorph.mulLeft a) ⁻¹'
        (specialFormPreservingSmoothRealChart F hF hdet h).source =
      (specialFormPreservingSmoothRealChart
        F hF hdet (a⁻¹ * h)).source := by
  simpa using
    preimage_mul_left_specialFormPreservingSmoothRealChart_source
      F hF hdet a (a⁻¹ * h)

/-- Every centered-chart restriction of the left-translated global measure is
the local differential measure for that center. -/
theorem restrict_map_specialFormPreservingSmoothRealDifferentialMeasure_mul_left
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (Measure.map (Homeomorph.mulLeft a)
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)).restrict
        (specialFormPreservingSmoothRealChart F hF hdet h).source =
      specialFormPreservingSmoothRealChartAmbientDensityMeasure
        F hF hdet h := by
  let L := Homeomorph.mulLeft a
  let g := a⁻¹ * h
  let U :=
    (specialFormPreservingSmoothRealChart F hF hdet h).source
  let V :=
    (specialFormPreservingSmoothRealChart F hF hdet g).source
  let μ :=
    specialFormPreservingSmoothRealDifferentialMeasure F hF hdet
  let ν :=
    specialFormPreservingSmoothRealChartAmbientDensityMeasure F hF hdet g
  change (Measure.map L μ).restrict U =
    specialFormPreservingSmoothRealChartAmbientDensityMeasure F hF hdet h
  calc
    (Measure.map L μ).restrict U =
        Measure.map L (μ.restrict (L ⁻¹' U)) := by
      exact Measure.restrict_map L.continuous.measurable
        (specialFormPreservingSmoothRealChart
          F hF hdet h).open_source.measurableSet
    _ = Measure.map L (μ.restrict V) := by
      rw [show L ⁻¹' U = V from
        preimage_mul_left_specialFormPreservingSmoothRealChart_source'
          F hF hdet a h]
    _ = Measure.map L ν := by
      rw [show μ.restrict V = ν from
        restrict_specialFormPreservingSmoothRealDifferentialMeasure_source
          F hF hdet g]
    _ = specialFormPreservingSmoothRealChartAmbientDensityMeasure
        F hF hdet (a * g) :=
      map_specialFormPreservingSmoothRealChartAmbientDensityMeasure_mul_left
        F hF hdet a g
    _ = specialFormPreservingSmoothRealChartAmbientDensityMeasure
        F hF hdet h := by
      congr 1
      simp [g]

/-- The explicitly glued real differential measure is invariant under every
left translation of the real special-orthogonal group. -/
theorem map_specialFormPreservingSmoothRealDifferentialMeasure_mul_left
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map (Homeomorph.mulLeft a)
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) =
      specialFormPreservingSmoothRealDifferentialMeasure F hF hdet := by
  apply
    measure_eq_specialFormPreservingSmoothRealDifferentialMeasure_of_selected_restrict
      F hF hdet
  intro m
  exact
    restrict_map_specialFormPreservingSmoothRealDifferentialMeasure_mul_left
      F hF hdet a
        (specialFormPreservingSmoothRealChartCoverCenter F hF hdet m)

/-- The real differential measure supplies the canonical left-invariant
measure instance required for Haar comparison. -/
instance specialFormPreservingSmoothRealDifferentialMeasure_isMulLeftInvariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure.IsMulLeftInvariant
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) where
  map_mul_left_eq_self a := by
    simpa only [Homeomorph.coe_mulLeft] using
      map_specialFormPreservingSmoothRealDifferentialMeasure_mul_left
        F hF hdet a

end PositiveDefiniteIntegralLattice
