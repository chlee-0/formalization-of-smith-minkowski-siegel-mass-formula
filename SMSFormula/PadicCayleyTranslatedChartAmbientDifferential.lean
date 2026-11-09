import SMSFormula.PadicCayleyTranslatedChartAtlasSum
import SMSFormula.PadicCayleyTranslatedChartDifferentialOverlap

/-!
# Ambient compatibility of corrected p-adic translated-chart differentials

Each corrected translated-target differential measure is included into the
full p-adic special-orthogonal group through the literal subtype inclusion.
The internally proved exact-overlap equality then shows that any two such
ambient chart measures agree after restriction to their common target.

The disjoint atlas contribution assigned to a selected center is also exactly
that center's ambient chart measure restricted to its assigned piece.  No
atlas-sum chart recovery, sigma-finiteness, left invariance, or stabilizer
volume is introduced here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTranslatedAmbientDifferentialGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedAmbientDifferentialGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The corrected differential measure induced by one translated p-adic
Cayley chart, included into the full special-orthogonal group. -/
def padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :=
  Measure.map Subtype.val
    (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      p n F hF c)

/-- A disjoint atlas contribution is exactly its selected ambient corrected
chart measure restricted to its assigned piece. -/
theorem
    padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_eq_restrict_ambient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) (k : ℕ) :
    padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
        p n F hF k =
      (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF
          (padicCayleySpecialOrthogonalChartCoverCenter F p k)).restrict
        (padicCayleySpecialOrthogonalChartCoverPiece F p k) := by
  symm
  exact Measure.restrict_map continuous_subtype_val.measurable
    (measurableSet_padicCayleySpecialOrthogonalChartCoverPiece F p k)

/-- Two corrected ambient translated-chart measures agree after restriction
to their explicit common target overlap. -/
theorem
    restrict_padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure_overlap
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF c).restrict
        (padicCayleySpecialOrthogonalTranslatedTarget F p d) =
      (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF d).restrict
          (padicCayleySpecialOrthogonalTranslatedTarget F p c) := by
  let μL :=
    padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromLeft
      p n F hF c d
  let μR :=
    padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromRight
      p n F hF c d
  let iL :=
    padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft
      p n F c d
  let iR :=
    padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
      p n F c d
  let jL :
      padicCayleySpecialOrthogonalTranslatedTarget F p c →
        specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ ℚ_[p])) :=
    Subtype.val
  let jR :
      padicCayleySpecialOrthogonalTranslatedTarget F p d →
        specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ ℚ_[p])) :=
    Subtype.val
  calc
    (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF c).restrict
        (padicCayleySpecialOrthogonalTranslatedTarget F p d) =
        Measure.map jL
          ((padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
            p n F hF c).restrict
              (padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinLeft
                p n F c d)) := by
      exact Measure.restrict_map continuous_subtype_val.measurable
        (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
          F p d).measurableSet
    _ = Measure.map jL (Measure.map iL μL) := by
      rw [
        map_padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromLeft]
    _ = Measure.map (jL ∘ iL) μL := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (measurableEmbedding_padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft
          p n F c d).measurable]
    _ = Measure.map
          (Subtype.val :
            padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d →
              specialFormPreservingMatrixSubgroup
                (F.map (algebraMap ℚ ℚ_[p]))) μL := by
      rfl
    _ = Measure.map
          (Subtype.val :
            padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d →
              specialFormPreservingMatrixSubgroup
                (F.map (algebraMap ℚ ℚ_[p]))) μR := by
      exact congrArg
        (Measure.map
          (Subtype.val :
            padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d →
              specialFormPreservingMatrixSubgroup
                (F.map (algebraMap ℚ ℚ_[p]))))
        (padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasure_eq
          p n F hFsymm hF c d)
    _ = Measure.map (jR ∘ iR) μR := by
      rfl
    _ = Measure.map jR (Measure.map iR μR) := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (measurableEmbedding_padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
          p n F c d).measurable]
    _ = Measure.map jR
          ((padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
            p n F hF d).restrict
              (padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinRight
                p n F c d)) := by
      rw [
        map_padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromRight]
    _ = (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF d).restrict
          (padicCayleySpecialOrthogonalTranslatedTarget F p c) := by
      symm
      exact Measure.restrict_map continuous_subtype_val.measurable
        (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
          F p c).measurableSet

/-- Two corrected ambient translated-chart measures agree on the common
target written literally as the intersection of the two translated
targets. -/
theorem
    restrict_padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure_commonTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF c).restrict
        (padicCayleySpecialOrthogonalTranslatedTarget F p c ∩
          padicCayleySpecialOrthogonalTranslatedTarget F p d) =
      (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF d).restrict
          (padicCayleySpecialOrthogonalTranslatedTarget F p c ∩
            padicCayleySpecialOrthogonalTranslatedTarget F p d) := by
  let U := padicCayleySpecialOrthogonalTranslatedTarget F p c
  let V := padicCayleySpecialOrthogonalTranslatedTarget F p d
  let W := U ∩ V
  have hW : MeasurableSet W :=
    ((isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p c).inter
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p d)).measurableSet
  have hover :
      (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF c).restrict V =
        (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF d).restrict U :=
    restrict_padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure_overlap
      p n F hFsymm hF c d
  change
    (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF c).restrict W =
      (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF d).restrict W
  calc
    (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF c).restrict W =
        ((padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF c).restrict V).restrict W := by
      rw [Measure.restrict_restrict hW]
      congr 1
      exact (Set.inter_eq_left.mpr Set.inter_subset_right).symm
    _ = ((padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF d).restrict U).restrict W :=
      congrArg (fun μ => μ.restrict W) hover
    _ = (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF d).restrict W := by
      rw [Measure.restrict_restrict hW]
      congr 1
      exact Set.inter_eq_left.mpr Set.inter_subset_left

end PositiveDefiniteIntegralLattice
