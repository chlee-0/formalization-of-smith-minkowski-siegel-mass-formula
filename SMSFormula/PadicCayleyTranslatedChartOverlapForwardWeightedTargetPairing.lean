import SMSFormula.PadicCayleyTranslatedChartOverlapForwardWeightedDisjointSource

/-!
# Exact target pairing for the certified p-adic source partition

Each member of the pairwise-disjoint certified source partition carries one
local analytic representative.  The raw-image fact is carried through
that representative to identify its tangent target coset with the exact image
of the source ball.

The global overlap transition is injective on `U_cd` and maps `U_cd` exactly
onto `U_dc`.  Therefore the target cosets are pairwise disjoint and cover
`U_dc`.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyOverlapForwardWeightedTargetPairingMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapForwardWeightedTargetPairingBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- Every disjoint certified source ball is clopen. -/
theorem
    isClopen_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (B :
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d) :
    IsClopen
      (B : Set (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
  rw [
    ←
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative_spec
        p n F hF c d B).2,
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_eq]
  exact
    Matrix.isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
      F p
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel
        p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative
          p n F hF c d B))
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative
        p n F hF c d B)

/-- A disjoint certified source ball is contained in the exact ambient source
overlap. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall_subset
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (B :
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d) :
    (B : Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ⊆
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d :=
  (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet_spec
    p n F hF c d).2.2.2.1 B B.property

/-- The indexed disjoint certified source balls remain pairwise disjoint after
passing from the set-valued family to its subtype. -/
theorem
    pairwise_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Pairwise
      (Function.onFun Disjoint
        (fun B :
          skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
            p n F hF c d =>
          (B : Set (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule))) := by
  intro B C hBC
  exact
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet_spec
      p n F hF c d).2.1
      B.property C.property (fun h => hBC (Subtype.ext h))

/-- The indexed disjoint certified source balls cover the exact ambient source
overlap. -/
theorem
    iUnion_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (⋃ B :
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
          p n F hF c d,
      (B : Set (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)) =
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d := by
  rw [
    ←
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet_spec
        p n F hF c d).2.2.2.2]
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨B, hxB⟩
    exact Set.mem_sUnion.mpr ⟨B, B.property, hxB⟩
  · intro hx
    rcases Set.mem_sUnion.mp hx with ⟨B, hB, hxB⟩
    exact Set.mem_iUnion.mpr ⟨⟨B, hB⟩, hxB⟩

/-- The tangent target coset is exactly the raw-transition image of
its disjoint certified source ball. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall_eq_image
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (B :
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
        p n F hF c d B =
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d ''
        (B : Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall,
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall_eq_image,
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative_spec
      p n F hF c d B).2]

/-- Every target tangent coset is clopen. -/
theorem
    isClopen_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (B :
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d) :
    IsClopen
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
        p n F hF c d B) := by
  change IsClopen
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
      F p hF c d
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedPoint
        p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative
          p n F hF c d B))
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointLevel
        p n F hF c d B))
  exact
    isClopen_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
      F p hF c d
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedPoint
        p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative
          p n F hF c d B))
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointLevel
        p n F hF c d B)

/-- Exact transition images of distinct disjoint certified source balls are
pairwise disjoint. -/
theorem
    pairwise_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Pairwise
      (Function.onFun Disjoint
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
          p n F hF c d)) := by
  intro B C hBC
  change Disjoint
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
      p n F hF c d B)
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
      p n F hF c d C)
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall_eq_image,
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall_eq_image,
    Set.disjoint_left]
  intro y hyB hyC
  obtain ⟨x, hxB, rfl⟩ := hyB
  obtain ⟨z, hzC, hxz⟩ := hyC
  have hxz' : x = z :=
    injOn_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall_subset
        p n F hF c d B hxB)
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall_subset
        p n F hF c d C hzC)
      hxz.symm
  have hdisj :=
    pairwise_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall
      p n F hF c d hBC
  change Disjoint
    (B : Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (C : Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) at hdisj
  rw [Set.disjoint_left] at hdisj
  exact hdisj hxB (hxz' ▸ hzC)

/-- The target tangent cosets cover the exact ambient target
overlap. -/
theorem
    iUnion_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (⋃ B :
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
          p n F hF c d,
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
        p n F hF c d B) =
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF d c := by
  simp_rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall_eq_image]
  rw [
    ← Set.image_iUnion,
    iUnion_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall,
    image_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition]

end PositiveDefiniteIntegralLattice
