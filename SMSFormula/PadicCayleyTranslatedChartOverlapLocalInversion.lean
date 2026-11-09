import SMSFormula.AddSubgroupCosetContraction
import SMSFormula.PadicCayleyTranslatedChartOverlapContraction
import SMSFormula.SkewAdjointPadicCoordinateBallAbsorption

/-!
# Local inversion of the derivative-normalized p-adic overlap transition

The strict two-point estimate and coordinate-lattice absorption hold
simultaneously on one common translated coordinate ball with a single
contraction coefficient strictly below one.  After normalizing the nonlinear
overlap transition by the inverse derivative at the center, the resulting map
fixes the center and has exactly those two error properties.

The generic closed-coset contraction theorem therefore makes the normalized
transition a bijection of the selected coordinate ball onto itself.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- One selected source ball carries a common strict contraction coefficient,
the norm estimate, and coordinate-subgroup membership of the normalized
two-point error. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_reverse_contraction_and_error_mem
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
          ‖skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
                F p hF c d X
                (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                    p n F hF c d y -
                  skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                    p n F hF c d z) -
              (y - z)‖ ≤
            (q : ℝ) * ‖y - z‖) ∧
      ∀ y ∈
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X),
        ∀ z ∈
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X),
          skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
                F p hF c d X
                (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                    p n F hF c d y -
                  skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                    p n F hF c d z) -
              (y - z) ∈
            Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup F p k := by
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
  obtain ⟨k, hkU, hkconst, hknorm⟩ :=
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_ambientOverlap_const_jacobianInverse_reverse_contraction
      F p hF c d X hqReal
  refine ⟨q, hq, k, hkU, hkconst, hknorm, ?_⟩
  intro y hy z hz
  have hy' :
      y -
          skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X ∈
        Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup F p k :=
    (Matrix.mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup
      F p k
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d X) y).1 hy
  have hz' :
      z -
          skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X ∈
        Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup F p k :=
    (Matrix.mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup
      F p k
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d X) z).1 hz
  have hyz :
      y - z ∈ Matrix.skewAdjointPadicUniformCoordinateBall F p k := by
    rw [← Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup_coe]
    have hsub :=
      (Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup F p k).sub_mem
        hy' hz'
    have heq :
        (y -
            skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) -
          (z -
            skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) =
        y - z := by
      abel
    rwa [heq] at hsub
  have herr :
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
              F p hF c d X
              (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                  p n F hF c d y -
                skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                  p n F hF c d z) -
            (y - z) ∈
        Matrix.skewAdjointPadicUniformCoordinateBall F p k :=
    habsorb k (y - z) _ hyz
      ((hknorm y hy z hz).trans
        (mul_le_mul_of_nonneg_right hq_le_q₀ (norm_nonneg (y - z))))
  rw [← Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup_coe] at herr
  exact herr

/-- The overlap transition normalized by the inverse derivative at `X`, with
the ambient source coordinate as fixed center. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X +
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
      F p hF c d X
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d y -
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X))

@[simp]
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition_center
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
        F p hF c d X
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
          p n F hF c d X) =
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d X := by
  simp [skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition]

/-- The two-point identity error of the normalized transition is exactly the
inverse-derivative transition error. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition_sub_sub
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (y z : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
          F p hF c d X y -
        skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
          F p hF c d X z -
        (y - z) =
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
            F p hF c d X
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                p n F hF c d y -
              skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
                p n F hF c d z) -
          (y - z) := by
  simp only [
    skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition,
    map_sub]
  congr 1
  abel

/-- A translated uniform coordinate ball is definitionally the translated
coset of its zero-centered coordinate-ball additive subgroup. -/
theorem skewAdjointPadicTranslatedUniformCoordinateBall_eq_translatedCoset
    (F : Matrix (Fin n) (Fin n) ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x =
      (Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup F p k).translatedCoset
        x := by
  ext y
  rw [
    Matrix.mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup,
    AddSubgroup.mem_translatedCoset_iff]

/-- At every exact overlap point, the derivative-normalized transition is a
bijection of one selected coordinate ball onto itself.  The ball lies in the
overlap and has constant reciprocal Jacobian density. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_derivativeNormalizedTransition_bijective
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
      skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
          F p hF c d X ''
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) =
        Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X) ∧
      Set.InjOn
        (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
          F p hF c d X)
        (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X)) := by
  obtain ⟨q, hq, k, hkU, hkconst, hknorm, hkmem⟩ :=
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_reverse_contraction_and_error_mem
      F p hF c d X
  let x :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let L := Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup F p k
  let N :=
    skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
      F p hF c d X
  have hball :
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x =
        L.translatedCoset x := by
    exact skewAdjointPadicTranslatedUniformCoordinateBall_eq_translatedCoset
      F p k x
  have hL :
      IsClosed
        (↑L :
          Set
            (skewAdjointMatricesLieSubalgebra
              (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
    dsimp [L]
    rw [Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup_coe]
    exact (Matrix.isClopen_skewAdjointPadicUniformCoordinateBall F p k).1
  have hNx : N x = x := by
    exact
      skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition_center
        F p hF c d X
  have hcongr :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          N y - N z - (y - z) ∈ L := by
    intro y hy z hz
    rw [← hball] at hy hz
    dsimp [N]
    rw [
      skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition_sub_sub]
    exact hkmem y hy z hz
  have hnorm :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          ‖N y - N z - (y - z)‖ ≤ (q : ℝ) * ‖y - z‖ := by
    intro y hy z hz
    rw [← hball] at hy hz
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
      _ ≤ (q : ℝ) * ‖y - z‖ := hknorm y hy z hz
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
  have hinvert :=
    @AddSubgroup.image_translatedCoset_eq_and_injOn
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule _ _ complete
      L x hL N hNx q hq hcongr hnorm
  refine ⟨q, hq, k, hkU, hkconst, ?_, ?_⟩
  · change N '' Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x =
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x
    rw [hball]
    exact hinvert.1
  · change
      Set.InjOn N
        (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x)
    rw [hball]
    exact hinvert.2

end PositiveDefiniteIntegralLattice
