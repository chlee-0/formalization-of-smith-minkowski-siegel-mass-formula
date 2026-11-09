import SMSFormula.PadicCayleyTranslatedChartAtlas
import SMSFormula.PadicCayleyTranslatedChartDifferentialMeasure

/-!
# Corrected p-adic differential contributions on disjoint atlas pieces

The countable translated Cayley atlas assigns each disjoint measurable piece
to one exact translated target.  This module represents that piece inside its
selected target subtype, restricts the corrected translated-chart
differential measure to it, and pushes the result through the literal subtype
inclusion into the full p-adic special-orthogonal group.

Each contribution is supported on its assigned piece and vanishes on every
other atlas piece.  No countable measure sum, sigma-finiteness argument, chart
restriction recovery, or group invariance is introduced here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTranslatedAtlasDifferentialGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedAtlasDifferentialGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The `k`-th disjoint atlas piece represented inside its selected exact
translated p-adic Cayley target subtype. -/
def padicCayleySpecialOrthogonalChartCoverPieceWithinTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    Set (padicCayleySpecialOrthogonalTranslatedTarget F p
      (padicCayleySpecialOrthogonalChartCoverCenter F p k)) :=
  Subtype.val ⁻¹'
    padicCayleySpecialOrthogonalChartCoverPiece F p k

/-- The `k`-th atlas piece is measurable inside its selected target
subtype. -/
theorem measurableSet_padicCayleySpecialOrthogonalChartCoverPieceWithinTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    MeasurableSet
      (padicCayleySpecialOrthogonalChartCoverPieceWithinTarget
        p n F k) :=
  (measurableSet_padicCayleySpecialOrthogonalChartCoverPiece F p k).preimage
    continuous_subtype_val.measurable

/-- The corrected differential contribution of the `k`-th disjoint
translated Cayley atlas piece, viewed as a measure on the full p-adic
special-orthogonal group. -/
def padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) (k : ℕ) :
    Measure (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :=
  Measure.map Subtype.val
    ((padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      p n F hF
        (padicCayleySpecialOrthogonalChartCoverCenter F p k)).restrict
      (padicCayleySpecialOrthogonalChartCoverPieceWithinTarget
        p n F k))

/-- On measurable sets, a disjoint p-adic chart-piece contribution is the
selected corrected target measure of the corresponding internal
intersection. -/
theorem padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) (k : ℕ)
    {s : Set (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))} (hs : MeasurableSet s) :
    padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
        p n F hF k s =
      padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
          p n F hF
          (padicCayleySpecialOrthogonalChartCoverCenter F p k)
        (padicCayleySpecialOrthogonalChartCoverPieceWithinTarget
            p n F k ∩
          Subtype.val ⁻¹' s) := by
  let i :
      padicCayleySpecialOrthogonalTranslatedTarget F p
          (padicCayleySpecialOrthogonalChartCoverCenter F p k) →
        specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ ℚ_[p])) :=
    Subtype.val
  have hi : MeasurableEmbedding i :=
    MeasurableEmbedding.subtype_coe
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p
        (padicCayleySpecialOrthogonalChartCoverCenter F p k)).measurableSet
  change (Measure.map i
    ((padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      p n F hF
        (padicCayleySpecialOrthogonalChartCoverCenter F p k)).restrict
      (padicCayleySpecialOrthogonalChartCoverPieceWithinTarget
        p n F k))) s = _
  rw [hi.map_apply, Measure.restrict_apply
    (hs.preimage continuous_subtype_val.measurable)]
  rw [Set.inter_comm]

/-- A corrected p-adic chart-piece contribution is concentrated on its
assigned disjoint atlas piece. -/
theorem padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_compl
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) (k : ℕ) :
    padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
        p n F hF k
        (padicCayleySpecialOrthogonalChartCoverPiece F p k)ᶜ =
      0 := by
  rw [padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_apply
    p n F hF k
    (measurableSet_padicCayleySpecialOrthogonalChartCoverPiece F p k).compl]
  have hset :
      padicCayleySpecialOrthogonalChartCoverPieceWithinTarget p n F k ∩
        Subtype.val ⁻¹'
          (padicCayleySpecialOrthogonalChartCoverPiece F p k)ᶜ =
        ∅ := by
    ext x
    simp [padicCayleySpecialOrthogonalChartCoverPieceWithinTarget]
  rw [hset, measure_empty]

/-- Restricting a corrected p-adic chart-piece contribution to its assigned
disjoint atlas piece does not change it. -/
theorem
    restrict_padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) (k : ℕ) :
    (padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
      p n F hF k).restrict
        (padicCayleySpecialOrthogonalChartCoverPiece F p k) =
      padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
        p n F hF k := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact mem_ae_iff.mpr
    (padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_compl
      p n F hF k)

/-- A corrected p-adic chart-piece contribution gives zero mass to every
different disjoint atlas piece. -/
theorem
    padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_other_piece
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    {i k : ℕ} (hik : i ≠ k) :
    padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
        p n F hF i
        (padicCayleySpecialOrthogonalChartCoverPiece F p k) =
      0 := by
  apply measure_mono_null
    (t := (padicCayleySpecialOrthogonalChartCoverPiece F p i)ᶜ)
  · intro x hx hxi
    exact
      (Set.disjoint_left.mp
        (pairwiseDisjoint_padicCayleySpecialOrthogonalChartCoverPiece
          F p hik) hxi hx)
  · exact
      padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_compl
        p n F hF i

end PositiveDefiniteIntegralLattice
