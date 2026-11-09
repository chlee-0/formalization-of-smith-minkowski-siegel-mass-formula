import SMSFormula.PadicCayleyTranslatedChartOverlapJacobianLocalConstancy
import SMSFormula.PadicCayleyStrictDifferential
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Strict differential control for translated p-adic Cayley overlaps

The ambient forward and inverse Cayley rational maps are strictly
Fréchet-differentiable on their unit domains.  Hence so is the ambient
relative transition attached to a translated-chart overlap.

The strict derivative is then used only on the exact ambient overlap.  It
gives a uniform two-point first-order remainder bound on a sufficiently small
uniform coordinate ball.  The ball is also chosen inside the overlap and
small enough that the already constructed reciprocal determinant density is
constant there.

No ball-image identity, scaled-isometry statement, Haar scaling, measure
pushforward, or change-of-variables theorem is proved here.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- Left multiplication by a fixed relative center is strictly
Fréchet-differentiable with its defining continuous linear map. -/
theorem hasStrictFDerivAt_padicCayleyRelativeLeft
    (p : ℕ) [Fact (Nat.Prime p)]
    (W Y : Matrix (Fin n) (Fin n) ℚ_[p]) :
    HasStrictFDerivAt
      (fun Z : Matrix (Fin n) (Fin n) ℚ_[p] ↦ W * Z)
      (padicCayleyRelativeLeftDerivative p W)
      Y := by
  have hfun :
      (fun Z : Matrix (Fin n) (Fin n) ℚ_[p] ↦ W * Z) =
        (padicCayleyRelativeLeftDerivative p W :
          Matrix (Fin n) (Fin n) ℚ_[p] →
            Matrix (Fin n) (Fin n) ℚ_[p]) := by
    funext Z
    exact (padicCayleyRelativeLeftDerivative_apply p W Z).symm
  rw [hfun]
  exact (padicCayleyRelativeLeftDerivative p W).hasStrictFDerivAt

/-- The relative Cayley target map has the strict chain-rule
derivative. -/
theorem hasStrictFDerivAt_padicCayleyRelativeTarget
    (p : ℕ) [Fact (Nat.Prime p)]
    (W X : Matrix (Fin n) (Fin n) ℚ_[p])
    (hX : X ∈ Matrix.padicCayleySource p) :
    HasStrictFDerivAt
      (fun Y : Matrix (Fin n) (Fin n) ℚ_[p] ↦
        W * Matrix.padicCayleyForwardMatrix p Y)
      ((padicCayleyRelativeLeftDerivative p W).comp
        (Matrix.padicCayleyForwardDerivative p X))
      X := by
  exact
    (hasStrictFDerivAt_padicCayleyRelativeLeft p W
        (Matrix.padicCayleyForwardMatrix p X)).comp X
      (Matrix.hasStrictFDerivAt_padicCayleyForwardMatrix p X hX)

/-- The ambient relative overlap transition has the strict
chain-rule derivative. -/
theorem hasStrictFDerivAt_padicCayleyRelativeTransitionMatrix
    (p : ℕ) [Fact (Nat.Prime p)]
    (W X : Matrix (Fin n) (Fin n) ℚ_[p])
    (hX : X ∈ Matrix.padicCayleySource p)
    (hrelative :
      W * Matrix.padicCayleyForwardMatrix p X ∈
        Matrix.padicCayleyInverseDomain p) :
    HasStrictFDerivAt
      (padicCayleyRelativeTransitionMatrix p W)
      (padicCayleyRelativeTransitionDerivative p W X)
      X := by
  change HasStrictFDerivAt
    (fun Y : Matrix (Fin n) (Fin n) ℚ_[p] =>
      Matrix.padicCayleyInverseMatrix p
        (W * Matrix.padicCayleyForwardMatrix p Y))
    (padicCayleyRelativeTransitionDerivative p W X)
    X
  exact
    (Matrix.hasStrictFDerivAt_padicCayleyInverseMatrix p
      (W * Matrix.padicCayleyForwardMatrix p X) hrelative).comp X
        (hasStrictFDerivAt_padicCayleyRelativeTarget p W X hX)

/-- At every exact translated-overlap point, the ambient relative transition
has the strict chain-rule derivative. -/
theorem
    hasStrictFDerivAt_skewAdjointPadicCayleyTranslatedSourceOverlapTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    HasStrictFDerivAt
      (padicCayleyRelativeTransitionMatrix p
        (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])))
      (padicCayleyRelativeTransitionDerivative p
        (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
        (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
      (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  apply hasStrictFDerivAt_padicCayleyRelativeTransitionMatrix
  · exact X.1.2
  · rw [←
      skewAdjointPadicCayleyTranslatedRelativeTargetMatrix_eq_mul_cayley
        F p hF c d X.1]
    exact
      (mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff_relative_inverseDomain
        F p hF c d X.1).mp X.2

/-- The strict derivative gives the uniform two-point remainder estimate in
ambient matrix coordinates. -/
theorem
    eventually_norm_skewAdjointPadicCayleyTranslatedSourceOverlapTransition_remainder_le
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ YZ :
        Matrix (Fin n) (Fin n) ℚ_[p] ×
          Matrix (Fin n) (Fin n) ℚ_[p] in
      𝓝
        ((X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]),
          (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])),
      ‖padicCayleyRelativeTransitionMatrix p
            (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) YZ.1 -
          padicCayleyRelativeTransitionMatrix p
            (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) YZ.2 -
          padicCayleyRelativeTransitionDerivative p
            (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
            (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])
            (YZ.1 - YZ.2)‖ ≤
        ε * ‖YZ.1 - YZ.2‖ := by
  exact
    (hasStrictFDerivAt_skewAdjointPadicCayleyTranslatedSourceOverlapTransition
      F p hF c d X).isLittleO.bound hε

/-- Coercing the restricted transition derivative to ambient
matrices recovers the ambient relative-transition derivative. -/
theorem
    coe_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
        F p hF c d X H :
      Matrix (Fin n) (Fin n) ℚ_[p]) =
      padicCayleyRelativeTransitionDerivative p
        (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
        (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])
        (H : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  rfl

/-- On the open ambient overlap, the globally measurable transition extension
has the restricted strict derivative. -/
theorem
    hasStrictFDerivAt_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    HasStrictFDerivAt
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
        p n F hF c d)
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
        F p hF c d X)
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d X) := by
  let E :=
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
  let inclusion : E →L[ℚ_[p]] Matrix (Fin n) (Fin n) ℚ_[p] :=
    Matrix.skewAdjointPadicAmbientInclusion F p
  let x : E :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let A : E →L[ℚ_[p]] E :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
      F p hF c d X
  let T : E → E :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d
  let W : Matrix (Fin n) (Fin n) ℚ_[p] :=
    ((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])
  let D :
      Matrix (Fin n) (Fin n) ℚ_[p] →L[ℚ_[p]]
        Matrix (Fin n) (Fin n) ℚ_[p] :=
    padicCayleyRelativeTransitionDerivative p W
      (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])
  have hcomp :
      HasStrictFDerivAt
        (fun y : E =>
          padicCayleyRelativeTransitionMatrix p W
            (inclusion y))
        (D.comp inclusion)
        x := by
    exact
      (hasStrictFDerivAt_skewAdjointPadicCayleyTranslatedSourceOverlapTransition
        F p hF c d X).comp x inclusion.hasStrictFDerivAt
  have hderiv : inclusion.comp A = D.comp inclusion := by
    apply ContinuousLinearMap.ext
    intro H
    exact
      coe_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_apply
        F p hF c d X H
  have hformula :
      HasStrictFDerivAt
        (fun y : E =>
          padicCayleyRelativeTransitionMatrix p W
            (inclusion y))
        (inclusion.comp A)
        x :=
    hcomp.congr_fderiv hderiv.symm
  have hU :
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d ∈ 𝓝 x :=
    (isOpen_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
      p n F hF c d).mem_nhds ⟨X, rfl⟩
  have heq :
      (fun y : E => inclusion (T y)) =ᶠ[𝓝 x]
        (fun y : E =>
          padicCayleyRelativeTransitionMatrix p W
            (inclusion y)) := by
    filter_upwards [hU] with y hy
    rcases hy with ⟨Y, rfl⟩
    exact
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq_relativeTransition
        p n F hF c d Y
  have hinclusion :
      HasStrictFDerivAt
        (fun y : E => inclusion (T y))
        (inclusion.comp A)
        x :=
    hformula.congr_of_eventuallyEq heq.symm
  apply HasStrictFDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [hinclusion.isLittleO.bound hε] with YZ hYZ
  simpa [T, A, inclusion, ContinuousLinearMap.comp_apply] using hYZ

/-- Around every exact overlap point, one uniform coordinate ball lies in the
overlap, has constant reciprocal determinant density, and satisfies the
strict two-point remainder estimate for the actual ambient transition
extension. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_ambientOverlap_const_jacobianInverse_remainder_le
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    {ε : ℝ} (hε : 0 < ε) :
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
      ∀ y ∈
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X),
        ∀ z ∈
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X),
          ‖skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                p n F hF c d y -
              skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                p n F hF c d z -
              skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
                F p hF c d X (y - z)‖ ≤
            ε * ‖y - z‖ := by
  let E :=
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
  let x : E :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let B := fun k =>
    Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x
  have hbound :
      ∀ᶠ YZ : E × E in 𝓝 (x, x),
        ‖skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
              p n F hF c d YZ.1 -
            skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
              p n F hF c d YZ.2 -
            skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
              F p hF c d X (YZ.1 - YZ.2)‖ ≤
          ε * ‖YZ.1 - YZ.2‖ :=
    (hasStrictFDerivAt_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      F p hF c d X).isLittleO.bound hε
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hbound
  rcases hbound with ⟨pa, hpa, pb, hpb, hpab⟩
  obtain ⟨k₀, hk₀U, hk₀const⟩ :=
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_ambientOverlap_const_jacobianInverse
      F p hF c d x ⟨X, rfl⟩
  have hsmall :
      {y : E | pa y ∧ pb y ∧ y ∈ B k₀} ∈ 𝓝 x := by
    filter_upwards [
      hpa, hpb,
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall_mem_nhds
        F p k₀ x] with y hya hyb hyB
    exact ⟨hya, hyb, hyB⟩
  obtain ⟨k, hk⟩ :=
    Matrix.exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_mem_nhds
      F p x hsmall
  refine ⟨k, ?_, ?_, ?_⟩
  · intro y hy
    exact hk₀U (hk hy).2.2
  · intro y hy
    exact hk₀const y (hk hy).2.2
  · intro y hy z hz
    exact hpab (hk hy).1 (hk hz).2.1

end PositiveDefiniteIntegralLattice
