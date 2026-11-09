import SMSFormula.MeasureWithDensityDisjointUnion
import SMSFormula.PadicCayleyTranslatedChartOverlapForwardWeightedTargetPairing

/-!
# Forward-weighted gluing for translated p-adic Cayley overlaps

The generic disjoint-union measure algebra is first specialized to the
correctly oriented ambient forward determinant density.  Its hypotheses keep
the countable clopen source and target partitions and every local weighted
pushforward explicit.

The second theorem supplies those hypotheses from the certified exact
source/target partition.  It proves the corrected ambient nonlinear
change-of-variables statement without transporting back to overlap subtypes or
gluing the finite differential Haar measure.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyOverlapForwardWeightedGluingMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapForwardWeightedGluingBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- A countable clopen source/target partition with exact local
forward-weighted pushforwards gives the corrected ambient overlap
pushforward. -/
theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapAmbient_forwardJacobian_of_clopenBallPartition
    {ι : Type*} [Countable ι]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (sourceBall targetBall : ι → Set
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hsourceClopen : ∀ i, IsClopen (sourceBall i))
    (htargetClopen : ∀ i, IsClopen (targetBall i))
    (hsourceDisjoint : Pairwise (Function.onFun Disjoint sourceBall))
    (htargetDisjoint : Pairwise (Function.onFun Disjoint targetBall))
    (hsourceCover :
      (⋃ i, sourceBall i) =
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d)
    (htargetCover :
      (⋃ i, targetBall i) =
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF d c)
    (hlocal : ∀ i,
      Measure.map
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
            p n F hF c d)
          (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
              (sourceBall i)).withDensity
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
              p n F hF c d)) =
        (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
          (targetBall i)) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d)
        (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
              p n F hF c d)).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
            p n F hF c d)) =
      (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF d c) := by
  rw [← hsourceCover, ← htargetCover]
  exact Measure.map_withDensity_restrict_iUnion_of_disjoint
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d)
    (Matrix.skewAdjointPadicCoordinateMeasure F p)
    (Matrix.skewAdjointPadicCoordinateMeasure F p)
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
      p n F hF c d)
    sourceBall
    targetBall
    (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d)
    hsourceDisjoint
    htargetDisjoint
    (fun i => (hsourceClopen i).2.measurableSet)
    (fun i => (htargetClopen i).2.measurableSet)
    hlocal

/-- The certified exact source/target partition proves the corrected ambient
forward-Jacobian change-of-variables theorem. -/
theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapAmbient_withDensity_forwardJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d)
        (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
              p n F hF c d)).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
            p n F hF c d)) =
      (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF d c) := by
  letI :
      Countable
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
          p n F hF c d) :=
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet_spec
      p n F hF c d).1.to_subtype
  exact
    map_skewAdjointPadicCayleyTranslatedSourceOverlapAmbient_forwardJacobian_of_clopenBallPartition
      p n F hF c d
      (fun B :
          skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
            p n F hF c d =>
        (B : Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule))
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
        p n F hF c d)
      (isClopen_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall
        p n F hF c d)
      (isClopen_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
        p n F hF c d)
      (pairwise_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall
        p n F hF c d)
      (pairwise_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
        p n F hF c d)
      (iUnion_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall
        p n F hF c d)
      (iUnion_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
        p n F hF c d)
      (map_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall_withDensity_forwardJacobian
        p n F hF c d)

end PositiveDefiniteIntegralLattice
