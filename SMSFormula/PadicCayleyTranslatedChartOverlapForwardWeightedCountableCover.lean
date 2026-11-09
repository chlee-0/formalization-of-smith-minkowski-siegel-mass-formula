import SMSFormula.PadicCayleyTranslatedChartOverlapForwardWeightedLocal
import Mathlib.Topology.Compactness.Lindelof

/-!
# Countable cover by certified forward-weighted overlap balls

At every point of the open ambient translated Cayley overlap, the local
forward-weighted theorem supplies a coordinate ball and its exact target
tangent coset.  This module makes those choices pointwise and applies
hereditary Lindelöfness to select a countable subcover of the source overlap.

Every selected source ball retains its level, exact target tangent coset, and
local weighted pushforward.  No disjoint refinement, target-image partition,
or measure gluing occurs here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyOverlapForwardWeightedCoverMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapForwardWeightedCoverBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyOverlapForwardWeightedCoverSecondCountableTopology
    (F : Matrix (Fin n) (Fin n) ℚ) :
    SecondCountableTopology
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI : SecondCountableTopology (Fin n → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact TopologicalSpace.secondCountableTopology_induced
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
    (Matrix (Fin n) (Fin n) ℚ_[p])
    ((↑) : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
        Matrix (Fin n) (Fin n) ℚ_[p])

/-- Recover the exact translated-overlap point represented by an ambient
overlap point. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedPoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d :=
  Classical.choose x.property

/-- The recovered exact point includes back to the original ambient point. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion_certifiedPoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedPoint
          p n F hF c d x) =
      x := by
  exact Classical.choose_spec x.property

/-- The level of the locally certified forward-weighted coordinate ball. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    ℕ :=
  Classical.choose
    (exists_skewAdjointPadicTranslatedUniformCoordinateBall_forwardWeighted_rawTransition_map_restrict
      p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedPoint
          p n F hF c d x))

/-- The locally certified source coordinate ball at an ambient overlap point. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel
      p n F hF c d x)
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedPoint
        p n F hF c d x))

/-- The exact tangent target coset paired with a certified source ball. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
    F p hF c d
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedPoint
      p n F hF c d x)
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel
      p n F hF c d x)

private theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel_spec
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
        p n F hF c d x ⊆
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d ∧
    (∀ y ∈
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
          p n F hF c d x,
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
            p n F hF c d y =
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
            p n F hF c d
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d
              (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedPoint
                p n F hF c d x))) ∧
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d ''
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
          p n F hF c d x =
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall
        p n F hF c d x ∧
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d)
        (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
          (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
            p n F hF c d x)).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
            p n F hF c d)) =
      (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall
          p n F hF c d x) := by
  simpa [
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall,
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall,
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel] using
    (Classical.choose_spec
      (exists_skewAdjointPadicTranslatedUniformCoordinateBall_forwardWeighted_rawTransition_map_restrict
        p n F hF c d
          (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedPoint
            p n F hF c d x)))

/-- Every certified source ball lies in the ambient source overlap. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_subset
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
        p n F hF c d x ⊆
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d :=
  (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel_spec
    p n F hF c d x).1

/-- Every certified source ball is a neighborhood of its ambient center. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_mem_nhds
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
        p n F hF c d x ∈ 𝓝 (x :
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
  rw [
    ←
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion_certifiedPoint
        p n F hF c d x]
  exact Matrix.skewAdjointPadicTranslatedUniformCoordinateBall_mem_nhds
    F p
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel
      p n F hF c d x)
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedPoint
        p n F hF c d x))

/-- The paired tangent target coset is the exact raw-transition image of its
certified source ball. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall_eq_image
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall
        p n F hF c d x =
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d ''
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
          p n F hF c d x :=
  (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel_spec
    p n F hF c d x).2.2.1.symm

/-- Each certified source ball retains the exact forward-weighted local
pushforward to its paired tangent target coset. -/
theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_withDensity_forwardJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d)
        (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
          (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
            p n F hF c d x)).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
            p n F hF c d)) =
      (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall
          p n F hF c d x) :=
  (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel_spec
    p n F hF c d x).2.2.2

/-- The open ambient source overlap is covered by a countable subfamily of
the locally certified forward-weighted source balls. -/
theorem
    exists_countable_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_cover
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    ∃ t : Set {x // x ∈
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d},
      t.Countable ∧
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d =
        ⋃ x ∈ t,
          skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
            p n F hF c d x ∧
      (∀ x ∈ t,
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
            p n F hF c d x ⊆
          skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
            p n F hF c d) ∧
      ∀ x ∈ t,
        Measure.map
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
              p n F hF c d)
            (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
              (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
                p n F hF c d x)).withDensity
              (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
                p n F hF c d)) =
          (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
            (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall
              p n F hF c d x) := by
  let U :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
      p n F hF c d
  obtain ⟨t, htcount, htcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof U).elim_nhds_subcover'
      (fun x _ =>
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
          p n F hF c d ⟨x, ‹x ∈ U›⟩)
      (fun x hx =>
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_mem_nhds
          p n F hF c d ⟨x, hx⟩)
  refine ⟨t, htcount, Set.Subset.antisymm ?_ ?_, ?_, ?_⟩
  · exact htcover
  · exact Set.iUnion_subset fun x =>
      Set.iUnion_subset fun _ =>
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_subset
          p n F hF c d x
  · intro x hx
    exact
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_subset
        p n F hF c d x
  · intro x hx
    exact
      map_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_withDensity_forwardJacobian
        p n F hF c d x

end PositiveDefiniteIntegralLattice
