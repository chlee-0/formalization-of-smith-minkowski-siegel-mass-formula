import SMSFormula.PadicCayleyTranslatedChartAmbientDifferential

/-!
# Recovery of arbitrary corrected p-adic translated-chart differentials

The corrected p-adic atlas sum recovers not only the countably selected chart
measures, but the ambient differential measure induced by every translated
Cayley chart.  The proof uses only the established ambient overlap
compatibility, containment of each atlas piece in its assigned chart, and
countable restriction algebra.

The literal translated-target subtype pullback is then recovered from this
ambient restriction equality.  No sigma-finiteness, group invariance, or
stabilizer volume is introduced here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTranslatedRecoveryGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedRecoveryGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- Inside any translated Cayley target, every disjoint atlas contribution is
the ambient corrected measure of that chart restricted to the contribution's
atlas piece. -/
theorem
    restrict_padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_translatedTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) (k : ℕ)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
      p n F hF k).restrict
        (padicCayleySpecialOrthogonalTranslatedTarget F p c) =
      (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF c).restrict
        (padicCayleySpecialOrthogonalChartCoverPiece F p k) := by
  let g :=
    padicCayleySpecialOrthogonalChartCoverCenter F p k
  let P :=
    padicCayleySpecialOrthogonalChartCoverPiece F p k
  let U :=
    padicCayleySpecialOrthogonalTranslatedTarget F p c
  let V :=
    padicCayleySpecialOrthogonalTranslatedTarget F p g
  have hP : MeasurableSet P :=
    measurableSet_padicCayleySpecialOrthogonalChartCoverPiece F p k
  have hU : MeasurableSet U :=
    (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p c).measurableSet
  have hPV : P ⊆ V :=
    padicCayleySpecialOrthogonalChartCoverPiece_subset_target F p k
  rw [
    padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_eq_restrict_ambient]
  calc
    ((padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF g).restrict P).restrict U =
        ((padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF g).restrict U).restrict P := by
      rw [Measure.restrict_restrict hU, Measure.restrict_restrict hP]
      congr 1
      exact Set.inter_comm _ _
    _ = ((padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF c).restrict V).restrict P := by
      rw [
        restrict_padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure_overlap
          p n F hFsymm hF g c]
    _ = (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF c).restrict P := by
      rw [Measure.restrict_restrict hP]
      congr 1
      exact Set.inter_eq_left.mpr hPV

/-- The corrected p-adic atlas sum restricts to every translated Cayley
target as the corrected ambient differential measure induced by that chart. -/
theorem
    restrict_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (padicCayleySpecialOrthogonalDifferentialMeasure
      p n F hF).restrict
        (padicCayleySpecialOrthogonalTranslatedTarget F p c) =
      padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF c := by
  let U :=
    padicCayleySpecialOrthogonalTranslatedTarget F p c
  let ν :=
    padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
      p n F hF c
  let P :=
    padicCayleySpecialOrthogonalChartCoverPiece F p
  calc
    (padicCayleySpecialOrthogonalDifferentialMeasure
      p n F hF).restrict U =
        Measure.sum (fun k =>
          (padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure
            p n F hF k).restrict U) := by
      ext s hs
      rw [Measure.restrict_apply hs,
        padicCayleySpecialOrthogonalDifferentialMeasure,
        Measure.sum_apply _
          (hs.inter
            (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
              F p c).measurableSet),
        Measure.sum_apply _ hs]
      congr 1
      funext k
      rw [Measure.restrict_apply hs]
    _ = Measure.sum (fun k => ν.restrict (P k)) := by
      congr 1
      funext k
      exact
        restrict_padicCayleySpecialOrthogonalChartCoverPieceDifferentialMeasure_translatedTarget
          p n F hFsymm hF k c
    _ = ν := by
      symm
      calc
        ν = ν.restrict Set.univ := Measure.restrict_univ.symm
        _ = ν.restrict (⋃ k, P k) := by
          rw [iUnion_padicCayleySpecialOrthogonalChartCoverPiece F p]
        _ = Measure.sum (fun k => ν.restrict (P k)) :=
          Measure.restrict_iUnion
            (pairwiseDisjoint_padicCayleySpecialOrthogonalChartCoverPiece
              F p)
            (measurableSet_padicCayleySpecialOrthogonalChartCoverPiece F p)

/-- Pulling the corrected p-adic atlas sum back through the literal inclusion
of any translated Cayley target recovers that target's corrected
differential measure. -/
theorem
    comap_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.comap Subtype.val
        (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) =
      padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n F hF c := by
  let i :
      padicCayleySpecialOrthogonalTranslatedTarget F p c →
        specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ ℚ_[p])) :=
    Subtype.val
  apply
    (MeasurableEmbedding.subtype_coe
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
        F p c).measurableSet).map_injective
  calc
    Measure.map i
        (Measure.comap i
          (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF)) =
        (padicCayleySpecialOrthogonalDifferentialMeasure
          p n F hF).restrict (Set.range i) :=
      (MeasurableEmbedding.subtype_coe
        (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
          F p c).measurableSet).map_comap _
    _ = (padicCayleySpecialOrthogonalDifferentialMeasure
          p n F hF).restrict
          (padicCayleySpecialOrthogonalTranslatedTarget F p c) := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    _ = padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF c :=
      restrict_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
        p n F hFsymm hF c
    _ = Measure.map i
          (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
            p n F hF c) := by
      rfl

end PositiveDefiniteIntegralLattice
