import SMSFormula.PadicCayleyTranslatedChartAtlasDifferential

/-!
# Sum of corrected p-adic translated-chart atlas contributions

The corrected differential contribution of every disjoint translated Cayley
atlas piece is already a measure on the full p-adic special-orthogonal group.
This module defines their countable sum and proves that restricting the sum to
one atlas piece recovers exactly its assigned contribution.

Only countable-sum and support algebra is used.  No sigma-finiteness,
whole-chart restriction comparison, left invariance, or stabilizer volume is
introduced here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTranslatedAtlasSumGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedAtlasSumGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The corrected p-adic differential measure obtained by summing the
translated-chart contributions over the countable disjoint atlas. -/
def padicCayleySpecialOrthogonalDifferentialMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    Measure (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :=
  Measure.sum
    (padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
      p n F hF)

/-- On every measurable set, the corrected p-adic atlas sum is the series of
the selected translated-target differential masses of the internal
chart-piece intersections. -/
theorem padicCayleySpecialOrthogonalDifferentialMeasure_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    {s : Set (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))} (hs : MeasurableSet s) :
    padicCayleySpecialOrthogonalDifferentialMeasure p n F hF s =
      ∑' k,
        padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
            p n F hF
            (padicCayleySpecialOrthogonalChartCoverCenter F p k)
          (padicCayleySpecialOrthogonalChartCoverPieceWithinTarget
              p n F k ∩
            Subtype.val ⁻¹' s) := by
  rw [padicCayleySpecialOrthogonalDifferentialMeasure,
    Measure.sum_apply _ hs]
  congr 1
  funext k
  exact
    padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_apply
      p n F hF k hs

/-- Restricting the corrected p-adic atlas sum to one disjoint atlas piece
recovers exactly that piece's translated-chart contribution. -/
theorem
    restrict_padicCayleySpecialOrthogonalDifferentialMeasure_chartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) (k : ℕ) :
    (padicCayleySpecialOrthogonalDifferentialMeasure
      p n F hF).restrict
        (padicCayleySpecialOrthogonalChartCoverPiece F p k) =
      padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
        p n F hF k := by
  ext s hs
  rw [Measure.restrict_apply hs,
    padicCayleySpecialOrthogonalDifferentialMeasure,
    Measure.sum_apply _
      (hs.inter
        (measurableSet_padicCayleySpecialOrthogonalChartCoverPiece
          F p k)),
    tsum_eq_single k]
  · rw [← Measure.restrict_apply hs,
      restrict_padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure]
  · intro i hik
    exact measure_mono_null Set.inter_subset_right
      (padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_other_piece
        p n F hF hik)

/-- The corrected p-adic atlas sum and the assigned contribution have the
same mass on every disjoint atlas piece. -/
theorem padicCayleySpecialOrthogonalDifferentialMeasure_chartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) (k : ℕ) :
    padicCayleySpecialOrthogonalDifferentialMeasure p n F hF
        (padicCayleySpecialOrthogonalChartCoverPiece F p k) =
      padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
        p n F hF k
        (padicCayleySpecialOrthogonalChartCoverPiece F p k) := by
  have h := congrArg
    (fun μ : Measure (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) =>
        μ (padicCayleySpecialOrthogonalChartCoverPiece F p k))
    (restrict_padicCayleySpecialOrthogonalDifferentialMeasure_chartCoverPiece
      p n F hF k)
  simpa [Measure.restrict_apply
    (measurableSet_padicCayleySpecialOrthogonalChartCoverPiece F p k)] using h

end PositiveDefiniteIntegralLattice
