import SMSFormula.PadicCayleyTranslatedChartOverlapNormalizedHaar
import SMSFormula.PadicCayleyTranslatedChartOverlapTangentHaar

/-!
# Restricted Haar scaling of the raw p-adic overlap transition

On one coordinate ball, the derivative-normalized overlap transition
preserves the fixed coordinate Haar measure.  The raw transition factors
through that normalized map and the centered affine tangent equivalence.
Composing the two already established pushforwards therefore gives the raw
transition's reciprocal-determinant scaling on the same ball.

This module does not insert a Jacobian density or glue the local statement
over a countable partition.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

local instance padicCayleyOverlapRawHaarMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapRawHaarBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- At every exact overlap point, the raw transition scales restricted
coordinate Haar on one contained coordinate ball by the reciprocal
determinant modulus of its tangent equivalence.  On the same ball the
reciprocal determinant density is constant, and its
exact raw image is the affine tangent target coset. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_rawTransition_map_restrict
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
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d ''
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) =
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
          F p hF c d X k ∧
      Measure.map
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
            p n F hF c d)
          ((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
            (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
              (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                p n F hF c d X))) =
        ‖LinearMap.det
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
            F p hF c d X).toLinearMap‖₊⁻¹ •
          (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
            (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
              F p hF c d X k) := by
  obtain ⟨k, hkU, hkconst, hnormalizedImage, hnormalized⟩ :=
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_derivativeNormalizedTransition_map_restrict
      F p hF c d X
  let T :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d
  let N :=
    skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
      F p hF c d X
  let A :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
      F p hF c d X
  let B :=
    Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d X)
  let μ := Matrix.skewAdjointPadicCoordinateMeasure F p
  have hN : Measurable N :=
    measurable_skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
      F p hF c d X
  have hA : Measurable A :=
    (continuous_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
      F p hF c d X).measurable
  have hfactor : T = A ∘ N := by
    funext y
    exact
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq_tangentAffineMap_normalized
        F p hF c d X y
  refine ⟨k, hkU, hkconst, ?_, ?_⟩
  · change T '' B = _
    calc
      T '' B = (A ∘ N) '' B :=
        congrArg (fun f => f '' B) hfactor
      _ = A '' (N '' B) := by
        apply Set.Subset.antisymm
        · rintro w ⟨y, hy, rfl⟩
          exact ⟨N y, ⟨y, hy, rfl⟩, rfl⟩
        · rintro w ⟨z, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨y, hy, rfl⟩
      _ = A '' B :=
        congrArg (Set.image A) hnormalizedImage
      _ = _ :=
        image_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap_coordinateBall
          F p hF c d X k
  change Measure.map T (μ.restrict B) = _
  rw [hfactor]
  calc
    Measure.map (A ∘ N) (μ.restrict B) =
        Measure.map A (Measure.map N (μ.restrict B)) := by
      symm
      rw [Measure.map_map hA hN]
    _ = Measure.map A (μ.restrict B) := by rw [hnormalized]
    _ = _ :=
      map_restrict_skewAdjointPadicCoordinateMeasure_translatedSourceOverlapTransitionTangentAffineMap
        F p hF c d X k

end PositiveDefiniteIntegralLattice
