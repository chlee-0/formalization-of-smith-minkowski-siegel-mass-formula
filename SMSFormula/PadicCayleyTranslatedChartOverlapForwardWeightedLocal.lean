import SMSFormula.PadicCayleyTranslatedChartOverlapRawHaar
import SMSFormula.PadicCayleyTranslatedChartOverlapWeightedReduction

/-!
# Forward-weighted local p-adic overlap pushforward

The ambient transition Jacobian inverse is the reciprocal determinant modulus
of the forward tangent map.  This module defines its reciprocal, proves that
it is the measurable ambient extension of the forward determinant modulus,
and combines its local constancy with the raw restricted Haar scaling.

On the selected coordinate ball, the forward density contributes `D` while
the raw transition contributes `D⁻¹`.  Their finite nonzero product cancels,
giving the exact unscaled target-coset restriction.  No countable partition or
global chart gluing occurs here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyOverlapForwardWeightedLocalMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapForwardWeightedLocalBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The forward determinant density on the ambient tangent carrier.  Outside
the exact overlap this is the reciprocal of the zero extension and hence is
irrelevant; every use below restricts it to a ball contained in the overlap. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    ENNReal :=
  (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
    p n F hF c d x)⁻¹

/-- The ambient forward determinant density is measurable. -/
theorem
    measurable_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measurable
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
        p n F hF c d) :=
  (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
    p n F hFsymm hF c d).inv

/-- On the exact overlap, the ambient forward density is the determinant
modulus of the tangent equivalence. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
        p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
          p n F hF c d X) =
      (‖LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toLinearMap‖₊ : ENNReal) := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian,
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse_eq]
  simp [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse]

private theorem transitionDeterminantNNNorm_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ‖LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toLinearMap‖₊ ≠ 0 := by
  rw [ne_eq, nnnorm_eq_zero, ← LinearEquiv.coe_det]
  exact Units.ne_zero _

/-- Every exact overlap point has a contained coordinate ball on which the
forward determinant density is constant and the forward-weighted raw
transition pushes restricted coordinate Haar exactly to the target tangent
coset restriction. The same target coset is also the exact raw image of the
source ball. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_forwardWeighted_rawTransition_map_restrict
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
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
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
              p n F hF c d y =
          skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
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
          (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
            (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
              (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                p n F hF c d X))).withDensity
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
              p n F hF c d)) =
        (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
            F p hF c d X k) := by
  obtain ⟨k, hkU, hkinvconst, hrawImage, hraw⟩ :=
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_rawTransition_map_restrict
      F p hF c d X
  let x :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let B :=
    Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x
  let T :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d
  let J :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
      p n F hF c d
  let Dn :=
    ‖LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toLinearMap‖₊
  let D : ENNReal := Dn
  let μ := Matrix.skewAdjointPadicCoordinateMeasure F p
  let ν :=
    μ.restrict
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
        F p hF c d X k)
  have hJconst : ∀ y ∈ B, J y = J x := by
    intro y hy
    exact congrArg Inv.inv (hkinvconst y hy)
  have hJx : J x = D := by
    exact
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian_eq
        p n F hF c d X
  have hB : MeasurableSet B :=
    (Matrix.isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
      F p k x).2.measurableSet
  have hJae : J =ᵐ[μ.restrict B] (fun _ => D) := by
    filter_upwards [ae_restrict_mem hB] with y hy
    exact (hJconst y hy).trans hJx
  have hweighted : (μ.restrict B).withDensity J = D • μ.restrict B := by
    rw [withDensity_congr_ae hJae, withDensity_const]
  have hDn0 : Dn ≠ 0 :=
    transitionDeterminantNNNorm_ne_zero p n F hF c d X
  have hD0 : D ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr hDn0
  have hDtop : D ≠ ⊤ := ENNReal.coe_ne_top
  refine ⟨k, hkU, hJconst, hrawImage, ?_⟩
  change Measure.map T ((μ.restrict B).withDensity J) = ν
  rw [hweighted, Measure.map_smul, hraw]
  change D • ((↑(Dn⁻¹) : ENNReal) • ν) = ν
  rw [smul_smul]
  have hcoe : (↑(Dn⁻¹) : ENNReal) = D⁻¹ := by
    simpa [D] using ENNReal.coe_inv hDn0
  rw [hcoe, ENNReal.mul_inv_cancel hD0 hDtop, one_smul]

end PositiveDefiniteIntegralLattice
