import SMSFormula.PadicCayleyTranslatedChartOverlapStrictDifferential

/-!
# Derivative-relative contraction control for p-adic Cayley overlaps

The reverse transition endomorphism is the inverse of the forward
derivative at an exact translated-overlap point.  Applying it to a transition
difference therefore turns the first-order remainder into the error from the
identity:

`A⁻¹(T y - T z) - (y - z) = A⁻¹(T y - T z - A(y - z))`.

Combining this identity with the strict remainder estimate and the operator
norm bound gives an arbitrarily small derivative-relative Lipschitz constant
on a sufficiently small uniform coordinate ball.  The ball lies
inside the exact ambient overlap and still has constant reciprocal Jacobian
density.

No exact ball-image statement, fixed-point argument, scaled isometry, Haar
scaling, measure pushforward, or change-of-variables theorem is proved here.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

local instance padicOverlapContractionOperatorNorm
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Norm
      ((skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := ℚ_[p]) (𝕜₂ := ℚ_[p])
    (σ₁₂ := RingHom.id ℚ_[p])

/-- Applying the inverse derivative to a transition difference turns the
linearized error into the image of the original first-order remainder. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverse_sub_eq_apply_remainder
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (K H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
          F p hF c d X K -
        H =
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
        F p hF c d X
        (K -
          skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
            F p hF c d X H) := by
  simp only [map_sub,
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverse_apply_forward]

/-- The operator norm of the inverse derivative converts a first-order
remainder estimate into a derivative-relative contraction estimate. -/
theorem
    norm_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverse_sub_le
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (K H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    {ε : ℝ}
    (hrem :
      ‖K -
          skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
            F p hF c d X H‖ ≤
        ε * ‖H‖) :
    ‖skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
          F p hF c d X K -
        H‖ ≤
      (‖skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
          F p hF c d X‖ * ε) * ‖H‖ := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverse_sub_eq_apply_remainder
      F p hF c d X K H]
  calc
    ‖skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
        F p hF c d X
        (K -
          skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
            F p hF c d X H)‖ ≤
        ‖skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
          F p hF c d X‖ *
          ‖K -
            skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
              F p hF c d X H‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤
        ‖skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
          F p hF c d X‖ * (ε * ‖H‖) := by
      exact mul_le_mul_of_nonneg_left hrem
        (ContinuousLinearMap.opNorm_nonneg _)
    _ =
        (‖skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
          F p hF c d X‖ * ε) * ‖H‖ := by
      rw [mul_assoc]

/-- For every positive contraction coefficient, one uniform translated
coordinate ball lies in the overlap, has constant reciprocal Jacobian
density, and supports the derivative-relative two-point contraction
estimate. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_ambientOverlap_const_jacobianInverse_reverse_contraction
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    {q : ℝ} (hq : 0 < q) :
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
          ‖skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
                F p hF c d X
                (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                    p n F hF c d y -
                  skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                    p n F hF c d z) -
              (y - z)‖ ≤
            q * ‖y - z‖ := by
  let R :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
      F p hF c d X
  let ε : ℝ := q / (‖R‖ + 1)
  have hRnonneg : 0 ≤ ‖R‖ :=
    ContinuousLinearMap.opNorm_nonneg R
  have hden : 0 < ‖R‖ + 1 := by
    linarith
  have hε : 0 < ε :=
    div_pos hq hden
  have hcoefficient : ‖R‖ * ε ≤ q := by
    calc
      ‖R‖ * ε = (‖R‖ * q) / (‖R‖ + 1) := by
        simp only [ε]
        ring
      _ ≤ q := by
        apply (div_le_iff₀ hden).2
        nlinarith
  obtain ⟨k, hkU, hkconst, hkrem⟩ :=
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_ambientOverlap_const_jacobianInverse_remainder_le
      F p hF c d X hε
  refine ⟨k, hkU, hkconst, ?_⟩
  intro y hy z hz
  have hnorm :=
    norm_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverse_sub_le
      F p hF c d X
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d y -
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d z)
      (y - z)
      (hkrem y hy z hz)
  exact hnorm.trans
    (mul_le_mul_of_nonneg_right hcoefficient (norm_nonneg (y - z)))

end PositiveDefiniteIntegralLattice
