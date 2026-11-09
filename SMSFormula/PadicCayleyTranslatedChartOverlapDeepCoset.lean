import SMSFormula.PadicCayleyTranslatedChartOverlapLocalInversion

/-!
# Deeper coordinate-coset transport for a p-adic overlap

On one selected source coordinate ball, the derivative-normalized overlap
transition has a strict two-point identity error.  The scale-uniform
coordinate-lattice absorption theorem applies that same norm estimate at every
deeper coordinate level.

After recentering at an arbitrary point of the selected ball, the generic
closed-coset contraction theorem therefore proves exact transport of every
deeper coordinate coset:

`N_X '' ball l y = ball l (N_X y)`.

This module proves no Haar invariance, equality on a generating family, or
nonlinear measure pushforward.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- At every exact overlap point, one selected coordinate ball supports exact
transport of every deeper coordinate coset by the derivative-normalized
transition.  The common contraction coefficient, overlap containment,
constant reciprocal density, and two-point norm estimate are also recorded. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_derivativeNormalizedTransition_deeper_cosets
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ∃ q : ℝ≥0, q < 1 ∧ ∃ k,
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
      (∀ y ∈
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X),
        ∀ z ∈
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X),
          ‖skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                F p hF c d X y -
              skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                F p hF c d X z -
              (y - z)‖ ≤
            (q : ℝ) * ‖y - z‖) ∧
      ∀ l, k ≤ l →
        ∀ y ∈
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X),
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l y ⊆
              Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
                (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                  p n F hF c d X) ∧
            skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                F p hF c d X ''
                Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l y =
              Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l
                (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                  F p hF c d X y) ∧
            Set.InjOn
              (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                F p hF c d X)
              (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l y) := by
  obtain ⟨q₀, hq₀, habsorb⟩ :=
    Matrix.exists_skewAdjointPadicUniformCoordinateBall_norm_absorption F p
  let qReal : ℝ := min q₀ 1 / 2
  have hqReal : 0 < qReal := by
    dsimp [qReal]
    positivity
  have hqReal_lt_one : qReal < 1 := by
    have hmin_le : min q₀ 1 ≤ 1 := min_le_right _ _
    dsimp [qReal]
    nlinarith
  let q : ℝ≥0 := ⟨qReal, le_of_lt hqReal⟩
  have hq : q < 1 := by
    exact_mod_cast hqReal_lt_one
  have hq_le_q₀ : (q : ℝ) ≤ q₀ := by
    change qReal ≤ q₀
    dsimp [qReal]
    have hmin_nonneg : 0 ≤ min q₀ 1 := le_of_lt (lt_min hq₀ one_pos)
    calc
      min q₀ 1 / 2 ≤ min q₀ 1 := by linarith
      _ ≤ q₀ := min_le_left _ _
  obtain ⟨k, hkU, hkconst, hknormRaw⟩ :=
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_ambientOverlap_const_jacobianInverse_reverse_contraction
      F p hF c d X hqReal
  let x :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let N :=
    skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
      F p hF c d X
  have hNnorm :
      ∀ y ∈ Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x,
        ∀ z ∈ Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x,
          ‖N y - N z - (y - z)‖ ≤ (q : ℝ) * ‖y - z‖ := by
    intro y hy z hz
    have herr :
        N y - N z - (y - z) =
          skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
                F p hF c d X
                (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                    p n F hF c d y -
                  skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                    p n F hF c d z) -
              (y - z) := by
      dsimp [N]
      exact
        skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition_sub_sub
          F p hF c d X y z
    calc
      ‖N y - N z - (y - z)‖ =
          ‖skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
                F p hF c d X
                (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                    p n F hF c d y -
                  skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                    p n F hF c d z) -
              (y - z)‖ := congrArg norm herr
      _ ≤ qReal * ‖y - z‖ := hknormRaw y hy z hz
      _ = (q : ℝ) * ‖y - z‖ := rfl
  refine ⟨q, hq, k, hkU, hkconst, hNnorm, ?_⟩
  intro l hkl y hy
  have hsubset :
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l y ⊆
        Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x :=
    Matrix.skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_mem
      F p hkl hy
  let L := Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup F p l
  have hball :
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l y =
        L.translatedCoset y := by
    exact skewAdjointPadicTranslatedUniformCoordinateBall_eq_translatedCoset
      F p l y
  have hL :
      IsClosed
        (↑L :
          Set
            (skewAdjointMatricesLieSubalgebra
              (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
    dsimp [L]
    rw [Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup_coe]
    exact (Matrix.isClopen_skewAdjointPadicUniformCoordinateBall F p l).1
  have hcongr :
      ∀ z ∈ L.translatedCoset y,
        ∀ w ∈ L.translatedCoset y,
          N z - N w - (z - w) ∈ L := by
    intro z hz w hw
    rw [← hball] at hz hw
    have hzw :
        z - w ∈ Matrix.skewAdjointPadicUniformCoordinateBall F p l :=
      Matrix.sub_mem_skewAdjointPadicUniformCoordinateBall_of_mem_translated
        F p l y z w hz hw
    have herrNorm :
        ‖N z - N w - (z - w)‖ ≤ q₀ * ‖z - w‖ :=
      (hNnorm z (hsubset hz) w (hsubset hw)).trans
        (mul_le_mul_of_nonneg_right hq_le_q₀ (norm_nonneg (z - w)))
    have herr :
        N z - N w - (z - w) ∈
          Matrix.skewAdjointPadicUniformCoordinateBall F p l :=
      habsorb l (z - w) (N z - N w - (z - w)) hzw herrNorm
    rw [← Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup_coe] at herr
    exact herr
  have hnorm :
      ∀ z ∈ L.translatedCoset y,
        ∀ w ∈ L.translatedCoset y,
          ‖N z - N w - (z - w)‖ ≤ (q : ℝ) * ‖z - w‖ := by
    intro z hz w hw
    rw [← hball] at hz hw
    exact hNnorm z (hsubset hz) w (hsubset hw)
  letI uniformAdd : IsUniformAddGroup
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    SeminormedAddCommGroup.to_isUniformAddGroup
  letI : IsBoundedSMul ℚ_[p]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    NormedSpace.toIsBoundedSMul
  let scalarContinuous : ContinuousSMul ℚ_[p]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    IsBoundedSMul.continuousSMul
  let complete :
      CompleteSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    @FiniteDimensional.complete ℚ_[p]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
      _ _ _ _ _ uniformAdd _ scalarContinuous _
  have htransport :=
    @AddSubgroup.image_translatedCoset_eq_translatedCoset_apply_and_injOn
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule _ _ complete
      L y hL N q hq hcongr hnorm
  refine ⟨hsubset, ?_, ?_⟩
  · change N '' Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l y =
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l (N y)
    rw [hball,
      skewAdjointPadicTranslatedUniformCoordinateBall_eq_translatedCoset
        F p l (N y)]
    exact htransport.1
  · change
      Set.InjOn N
        (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l y)
    rw [hball]
    exact htransport.2

end PositiveDefiniteIntegralLattice
