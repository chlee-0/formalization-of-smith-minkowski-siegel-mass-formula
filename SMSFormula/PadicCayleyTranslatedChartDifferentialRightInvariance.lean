import SMSFormula.PadicCayleyTranslatedChartDifferentialRightTranslation

/-!
# Right invariance of the corrected p-adic differential

The exact right-translation covariance of each corrected Cayley chart is
promoted to the globally glued measure.  The proof first identifies the image
and inverse image of every translated target, then uses arbitrary-chart
recovery.  The measurable disjoint Cayley atlas reconstructs the global
measure from these local restrictions.

No Haar uniqueness or inversion theorem is used here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyDifferentialRightInvarianceGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyDifferentialRightInvarianceGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- Literal right multiplication maps a translated Cayley target onto the
target whose center is right multiplied by the same group element. -/
theorem image_mul_right_padicCayleySpecialOrthogonalTranslatedTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c a : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Homeomorph.mulRight a ''
        padicCayleySpecialOrthogonalTranslatedTarget F p c =
      padicCayleySpecialOrthogonalTranslatedTarget F p (c * a) := by
  let R :=
    padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph
      p n F hFsymm hF c a
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x * a ∈
      padicCayleySpecialOrthogonalTranslatedTarget F p (c * a)
    have hRy : (R ⟨x, hx⟩).1 = x * a :=
      coe_padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph_apply
        p n F hFsymm hF c a ⟨x, hx⟩
    rw [← hRy]
    exact (R ⟨x, hx⟩).2
  · intro hy
    let y' : padicCayleySpecialOrthogonalTranslatedTarget F p (c * a) :=
      ⟨y, hy⟩
    let x' := R.symm y'
    refine ⟨x'.1, x'.2, ?_⟩
    change x'.1 * a = y
    have hx :=
      coe_padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph_apply
        p n F hFsymm hF c a x'
    have hR : R x' = y' := R.apply_symm_apply y'
    rw [hR] at hx
    exact hx.symm

/-- The inverse image of the target centered at `h` under right multiplication
by `a` is the target centered at `h * a⁻¹`. -/
theorem preimage_mul_right_padicCayleySpecialOrthogonalTranslatedTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (a h : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (Homeomorph.mulRight a) ⁻¹'
        padicCayleySpecialOrthogonalTranslatedTarget F p h =
      padicCayleySpecialOrthogonalTranslatedTarget F p (h * a⁻¹) := by
  have himage :
      Homeomorph.mulRight a ''
          padicCayleySpecialOrthogonalTranslatedTarget F p (h * a⁻¹) =
        padicCayleySpecialOrthogonalTranslatedTarget F p h := by
    simpa using
      image_mul_right_padicCayleySpecialOrthogonalTranslatedTarget
        p n F hFsymm hF (h * a⁻¹) a
  ext x
  constructor
  · intro hx
    have hx' : x * a ∈ Homeomorph.mulRight a ''
        padicCayleySpecialOrthogonalTranslatedTarget F p (h * a⁻¹) := by
      rw [himage]
      exact hx
    rcases hx' with ⟨z, hz, hza⟩
    have hzx : z = x := mul_right_cancel hza
    simpa [hzx] using hz
  · intro hx
    have hx' : x * a ∈ Homeomorph.mulRight a ''
        padicCayleySpecialOrthogonalTranslatedTarget F p (h * a⁻¹) :=
      ⟨x, hx, rfl⟩
    rw [himage] at hx'
    exact hx'

/-- Every translated-target restriction of the right-translated glued measure
is the corrected ambient differential induced by that target's chart. -/
theorem
    restrict_map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_right
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (a h : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (Measure.map (Homeomorph.mulRight a)
      (padicCayleySpecialOrthogonalDifferentialMeasure
        p n F hF)).restrict
        (padicCayleySpecialOrthogonalTranslatedTarget F p h) =
      padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF h := by
  let R := Homeomorph.mulRight a
  let g := h * a⁻¹
  let U := padicCayleySpecialOrthogonalTranslatedTarget F p h
  let V := padicCayleySpecialOrthogonalTranslatedTarget F p g
  let μ := padicCayleySpecialOrthogonalDifferentialMeasure p n F hF
  let ν :=
    padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF g
  change (Measure.map R μ).restrict U =
    padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF h
  calc
    (Measure.map R μ).restrict U =
        Measure.map R (μ.restrict (R ⁻¹' U)) := by
      exact Measure.restrict_map R.continuous.measurable
        (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
          F p h).measurableSet
    _ = Measure.map R (μ.restrict V) := by
      rw [show R ⁻¹' U = V from
        preimage_mul_right_padicCayleySpecialOrthogonalTranslatedTarget
          p n F hFsymm hF a h]
    _ = Measure.map R ν := by
      rw [show μ.restrict V = ν from
        restrict_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
          p n F hFsymm hF g]
    _ = padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF (g * a) :=
      map_padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure_right
        p n F hFsymm hF g a
    _ = padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF h := by
      congr 1
      simp [g]

/-- On every disjoint atlas piece, the right-translated glued measure has the
same restriction as the original glued measure. -/
theorem
    restrict_map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_right_chartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (a : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) (k : ℕ) :
    (Measure.map (Homeomorph.mulRight a)
      (padicCayleySpecialOrthogonalDifferentialMeasure
        p n F hF)).restrict
        (padicCayleySpecialOrthogonalChartCoverPiece F p k) =
      (padicCayleySpecialOrthogonalDifferentialMeasure
        p n F hF).restrict
          (padicCayleySpecialOrthogonalChartCoverPiece F p k) := by
  let h := padicCayleySpecialOrthogonalChartCoverCenter F p k
  let U := padicCayleySpecialOrthogonalTranslatedTarget F p h
  let P := padicCayleySpecialOrthogonalChartCoverPiece F p k
  let μ := padicCayleySpecialOrthogonalDifferentialMeasure p n F hF
  let μa := Measure.map (Homeomorph.mulRight a) μ
  let ν :=
    padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF h
  have hP : MeasurableSet P :=
    measurableSet_padicCayleySpecialOrthogonalChartCoverPiece F p k
  have hPU : P ⊆ U :=
    padicCayleySpecialOrthogonalChartCoverPiece_subset_target F p k
  change μa.restrict P = μ.restrict P
  calc
    μa.restrict P = (μa.restrict U).restrict P := by
      rw [Measure.restrict_restrict hP]
      congr 1
      exact (Set.inter_eq_left.mpr hPU).symm
    _ = ν.restrict P := by
      rw [
        restrict_map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_right
          p n F hFsymm hF a h]
    _ = (μ.restrict U).restrict P := by
      rw [
        restrict_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
          p n F hFsymm hF h]
    _ = μ.restrict P := by
      rw [Measure.restrict_restrict hP]
      congr 1
      exact Set.inter_eq_left.mpr hPU

/-- The corrected p-adic differential measure glued from translated Cayley
charts is invariant under every right translation. -/
theorem map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_right
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (a : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map (Homeomorph.mulRight a)
        (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) =
      padicCayleySpecialOrthogonalDifferentialMeasure p n F hF := by
  let μ := padicCayleySpecialOrthogonalDifferentialMeasure p n F hF
  let μa := Measure.map (Homeomorph.mulRight a) μ
  let P := padicCayleySpecialOrthogonalChartCoverPiece F p
  calc
    μa = Measure.sum (fun k => μa.restrict (P k)) :=
      measure_eq_sum_restrict_of_disjoint_iUnion_eq_univ μa P
        (measurableSet_padicCayleySpecialOrthogonalChartCoverPiece F p)
        (pairwiseDisjoint_padicCayleySpecialOrthogonalChartCoverPiece F p)
        (iUnion_padicCayleySpecialOrthogonalChartCoverPiece F p)
    _ = Measure.sum (fun k => μ.restrict (P k)) := by
      congr 1
      funext k
      exact
        restrict_map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_right_chartCoverPiece
          p n F hFsymm hF a k
    _ = μ :=
      (measure_eq_sum_restrict_of_disjoint_iUnion_eq_univ μ P
        (measurableSet_padicCayleySpecialOrthogonalChartCoverPiece F p)
        (pairwiseDisjoint_padicCayleySpecialOrthogonalChartCoverPiece F p)
        (iUnion_padicCayleySpecialOrthogonalChartCoverPiece F p)).symm

/-- The corrected p-adic differential is right invariant at its fixed
invariant-differential scale. -/
instance padicCayleySpecialOrthogonalDifferentialMeasure_isMulRightInvariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    Measure.IsMulRightInvariant
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) where
  map_mul_right_eq_self a := by
    simpa only [Homeomorph.coe_mulRight] using
      map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_right
        p n F hFsymm hF a

end PositiveDefiniteIntegralLattice
