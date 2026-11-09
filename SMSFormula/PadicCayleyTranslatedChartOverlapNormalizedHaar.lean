import SMSFormula.PadicCayleyTranslatedChartOverlapBasicBallMeasure
import SMSFormula.SkewAdjointPadicCoordinateBallMeasureDetermination

/-!
# Restricted Haar invariance of the normalized p-adic overlap

The deep-coordinate-ball determination theorem upgrades the
existing basic-ball compatibility of the derivative-normalized overlap
transition to equality of restricted coordinate Haar measures on one selected
source ball.

This module does not compose with the affine tangent map, insert the constant
reciprocal Jacobian density, or assert the raw nonlinear overlap pushforward.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

local instance padicOverlapNormalizedHaarMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicOverlapNormalizedHaarBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- On one coordinate ball inside the exact source overlap, the
derivative-normalized transition preserves restricted coordinate Haar.  On the
same ball the transition has exact self-image and constant reciprocal
determinant density. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_derivativeNormalizedTransition_map_restrict
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ∃ k,
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X) ⊆
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d ∧
      (∀ y ∈
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X),
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
              p n F hF c d y =
          skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
              p n F hF c d
              (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                p n F hF c d X)) ∧
      skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
          F p hF c d X ''
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) =
        Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X) ∧
      Measure.map
          (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
            F p hF c d X)
          ((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
            (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
              (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                p n F hF c d X))) =
        (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
          (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X)) := by
  obtain ⟨k, hkU, hkconst, hself, hinj, hbasic⟩ :=
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_derivativeNormalizedTransition_basicBallMeasure
      F p hF c d X
  let x :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let N :=
    skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
      F p hF c d X
  let B := Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x
  let μ := Matrix.skewAdjointPadicCoordinateMeasure F p
  letI : Measure.IsAddHaarMeasure μ :=
    Matrix.skewAdjointPadicCoordinateMeasure_isAddHaarMeasure F p
  letI : IsFiniteMeasureOnCompacts (μ.restrict B) :=
    ⟨fun K hK =>
      (Measure.restrict_le_self K).trans_lt hK.measure_lt_top⟩
  have hNmeas : Measurable N :=
    measurable_skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
      F p hF c d X
  change N '' B = B at hself
  refine ⟨k, hkU, hkconst, hself, ?_⟩
  apply
    (Matrix.measure_eq_of_skewAdjointPadicTranslatedUniformCoordinateBall_eq
      F p k (μ.restrict B) (Measure.map N (μ.restrict B)) ?_).symm
  intro l hkl z
  let D := Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l z
  have hDmeas : MeasurableSet D :=
    (Matrix.isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
      F p l z).2.measurableSet
  by_cases hzB : z ∈ B
  · have hzimage : z ∈ N '' B := by rwa [hself]
    obtain ⟨y, hyB, hyz⟩ := hzimage
    subst z
    exact (hbasic l hkl y hyB).2.2.symm
  · have hdisj : Disjoint B D := by
      rcases
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall_disjoint_or_subset_of_le
            F p hkl x z with h | h
      · exact h
      · exact (hzB
          (h (Matrix.mem_skewAdjointPadicTranslatedUniformCoordinateBall_self
            F p l z))).elim
    have hsourceZero : (μ.restrict B) D = 0 := by
      rw [Measure.restrict_apply hDmeas, hdisj.symm.inter_eq, measure_empty]
    have hpreEmpty : N ⁻¹' D ∩ B = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hyD, hyB⟩
      have hNyB : N y ∈ B := by
        rw [← hself]
        exact ⟨y, hyB, rfl⟩
      exact Set.disjoint_left.1 hdisj hNyB hyD
    have hmapZero : Measure.map N (μ.restrict B) D = 0 := by
      rw [Measure.map_apply hNmeas hDmeas,
        Measure.restrict_apply (hNmeas hDmeas),
        hpreEmpty, measure_empty]
    exact hsourceZero.trans hmapZero.symm

end PositiveDefiniteIntegralLattice
