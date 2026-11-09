import SMSFormula.PadicCayleyTranslatedChartDifferentialTranslation

/-!
# Left invariance of the corrected p-adic differential

The chartwise transport theorem is promoted to the globally glued corrected
differential measure.  Left translation pulls the exact target at `h` back to
the target at `a⁻¹ * h`.  Arbitrary chart recovery and the ambient chart
transport theorem therefore identify every translated-target restriction of
the mapped global measure.

The measurable disjoint Cayley atlas then reconstructs the whole measure from
these local restrictions.  This proves left invariance and installs the
corresponding measure instance.  No Haar uniqueness or stabilizer volume is
used.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyDifferentialInvarianceGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyDifferentialInvarianceGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The inverse image of the target centered at `h` under left multiplication
by `a` is the target centered at `a⁻¹ * h`. -/
theorem preimage_mul_left_padicCayleySpecialOrthogonalTranslatedTarget
    (F : Matrix (Fin n) (Fin n) ℚ)
    (a h : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (Homeomorph.mulLeft a) ⁻¹'
        padicCayleySpecialOrthogonalTranslatedTarget F p h =
      padicCayleySpecialOrthogonalTranslatedTarget F p (a⁻¹ * h) := by
  ext x
  change
    a * x ∈ padicCayleySpecialOrthogonalTranslatedTarget F p h ↔
      x ∈
        padicCayleySpecialOrthogonalTranslatedTarget F p (a⁻¹ * h)
  rw [
    mem_padicCayleySpecialOrthogonalTranslatedTarget_iff,
    mem_padicCayleySpecialOrthogonalTranslatedTarget_iff]
  simp [mul_assoc]

/-- Every translated-target restriction of the left-translated glued measure
is the corrected ambient differential induced by that target's chart. -/
theorem
    restrict_map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_left
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (a h : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (Measure.map (Homeomorph.mulLeft a)
      (padicCayleySpecialOrthogonalDifferentialMeasure
        p n F hF)).restrict
        (padicCayleySpecialOrthogonalTranslatedTarget F p h) =
      padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF h := by
  let L := Homeomorph.mulLeft a
  let g := a⁻¹ * h
  let U := padicCayleySpecialOrthogonalTranslatedTarget F p h
  let V := padicCayleySpecialOrthogonalTranslatedTarget F p g
  let μ := padicCayleySpecialOrthogonalDifferentialMeasure p n F hF
  let ν :=
    padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF g
  change (Measure.map L μ).restrict U =
    padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF h
  calc
    (Measure.map L μ).restrict U =
        Measure.map L (μ.restrict (L ⁻¹' U)) := by
      exact Measure.restrict_map L.continuous.measurable
        (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
          F p h).measurableSet
    _ = Measure.map L (μ.restrict V) := by
      rw [show L ⁻¹' U = V from
        preimage_mul_left_padicCayleySpecialOrthogonalTranslatedTarget
          p n F a h]
    _ = Measure.map L ν := by
      rw [show μ.restrict V = ν from
        restrict_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
          p n F hFsymm hF g]
    _ = padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF (a * g) :=
      map_padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure_left
        p n F hF a g
    _ = padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF h := by
      congr 1
      simp [g]

/-- On every disjoint atlas piece, the left-translated glued measure has the
same restriction as the original glued measure. -/
theorem
    restrict_map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_left_chartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (a : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) (k : ℕ) :
    (Measure.map (Homeomorph.mulLeft a)
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
  let μa := Measure.map (Homeomorph.mulLeft a) μ
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
        restrict_map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_left
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
charts is invariant under every left translation. -/
theorem map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_left
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (a : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map (Homeomorph.mulLeft a)
        (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) =
      padicCayleySpecialOrthogonalDifferentialMeasure p n F hF := by
  let μ := padicCayleySpecialOrthogonalDifferentialMeasure p n F hF
  let μa := Measure.map (Homeomorph.mulLeft a) μ
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
        restrict_map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_left_chartCoverPiece
          p n F hFsymm hF a k
    _ = μ :=
      (measure_eq_sum_restrict_of_disjoint_iUnion_eq_univ μ P
        (measurableSet_padicCayleySpecialOrthogonalChartCoverPiece F p)
        (pairwiseDisjoint_padicCayleySpecialOrthogonalChartCoverPiece F p)
        (iUnion_padicCayleySpecialOrthogonalChartCoverPiece F p)).symm

/-- The corrected p-adic differential supplies the canonical left-invariant
measure instance needed for Haar comparison. -/
instance padicCayleySpecialOrthogonalDifferentialMeasure_isMulLeftInvariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    Measure.IsMulLeftInvariant
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) where
  map_mul_left_eq_self a := by
    simpa only [Homeomorph.coe_mulLeft] using
      map_padicCayleySpecialOrthogonalDifferentialMeasure_mul_left
        p n F hFsymm hF a

end PositiveDefiniteIntegralLattice
