import SMSFormula.RationalSpecialOrthogonalGramFactorProduct

/-!
# Cancellation of the residual dyadic binary layer

The finite Gram-factor product leaves the reciprocal of
`sqrt (2^n)^(n-1)`.  This module evaluates that ordinary natural power using
the evenness of `n*(n-1)`, rewrites its exponent as the skew-adjoint tangent
rank, and cancels it against the certified inverse dyadic Cayley tangent
modulus.
-/

noncomputable section

open Matrix
open scoped BigOperators ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The binary square-root residual is the ordinary power with exponent
`n*(n-1)/2`.  The proof keeps the natural-number division and uses the
evenness of `n*(n-1)`. -/
theorem sqrt_two_pow_pow_pred_eq_two_pow_mul_pred_div_two (n : ℕ) :
    (Real.sqrt ((2 : ℝ) ^ n)) ^ (n - 1) =
      (2 : ℝ) ^ (n * (n - 1) / 2) := by
  apply (mul_self_inj_of_nonneg (by positivity) (by positivity)).mp
  have heven : Even (n * (n - 1)) := Nat.even_mul_pred_self n
  have hhalf :
      n * (n - 1) / 2 + n * (n - 1) / 2 = n * (n - 1) := by
    have h := Nat.div_two_mul_two_of_even heven
    omega
  calc
    (Real.sqrt ((2 : ℝ) ^ n)) ^ (n - 1) *
          (Real.sqrt ((2 : ℝ) ^ n)) ^ (n - 1) =
        ((2 : ℝ) ^ n) ^ (n - 1) := by
      rw [← mul_pow, Real.mul_self_sqrt (by positivity)]
    _ = (2 : ℝ) ^ (n * (n - 1)) := by
      rw [pow_mul]
    _ = (2 : ℝ) ^
          (n * (n - 1) / 2 + n * (n - 1) / 2) := by
      rw [hhalf]
    _ = (2 : ℝ) ^ (n * (n - 1) / 2) *
          (2 : ℝ) ^ (n * (n - 1) / 2) := by
      rw [pow_add]

/-- The same binary square-root residual with its exponent identified as the
rational skew-adjoint tangent rank. -/
theorem sqrt_two_pow_pow_pred_eq_two_pow_tangentRank
    (L : PositiveDefiniteIntegralLattice n) :
    (Real.sqrt ((2 : ℝ) ^ n)) ^ (n - 1) =
      (2 : ℝ) ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) := by
  rw [sqrt_two_pow_pow_pred_eq_two_pow_mul_pred_div_two]
  rw [← Nat.choose_two_right]
  rw [← finrank_skewAdjointMatricesLieSubalgebra_eq_choose_two
    n L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero]

/-- The reciprocal residual transported to `ENNReal` without using
`ENNReal.toReal`. -/
theorem ENNReal_ofReal_inv_sqrt_two_pow_pow_pred_eq_inv_two_pow_tangentRank
    (L : PositiveDefiniteIntegralLattice n) :
    ENNReal.ofReal (((Real.sqrt ((2 : ℝ) ^ n)) ^ (n - 1))⁻¹) =
      ((2 : ℝ≥0∞) ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix))⁻¹ := by
  rw [L.sqrt_two_pow_pow_pred_eq_two_pow_tangentRank]
  rw [ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The real form factor and inverse local Gram-factor product contribute
exactly the reciprocal dyadic tangent-rank power in `ENNReal`. -/
theorem
    ENNReal_ofReal_rationalForm_sqrt_det_pow_mul_prod_inv_gram_eq_inv_two_pow_tangentRank
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    ENNReal.ofReal
        ((Real.sqrt |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1) *
          (∏ q ∈ massBadPrimeSet L,
            (gramDetPadicNormFactorAtPrime L q)⁻¹)) =
      ((2 : ℝ≥0∞) ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix))⁻¹ := by
  rw [L.rationalForm_sqrt_det_pow_mul_prod_inv_gramDetPadicNormFactorAtPrime_bad]
  exact L.ENNReal_ofReal_inv_sqrt_two_pow_pow_pred_eq_inv_two_pow_tangentRank

/-- The reciprocal binary layer left by the real form/Gram product cancels
the certified inverse dyadic Cayley tangent modulus exactly. -/
theorem
    ENNReal_ofReal_rationalForm_sqrt_det_pow_mul_prod_inv_gram_mul_inv_dyadicCayleyTangentModulus_eq_one
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    ENNReal.ofReal
          ((Real.sqrt |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1) *
            (∏ q ∈ massBadPrimeSet L,
              (gramDetPadicNormFactorAtPrime L q)⁻¹)) *
        (↑(‖LinearMap.det
          (skewAdjointPadicCayleyTangentFactor
            L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹ =
      1 := by
  rw [L.ENNReal_ofReal_rationalForm_sqrt_det_pow_mul_prod_inv_gram_eq_inv_two_pow_tangentRank]
  rw [L.ENNReal_inv_dyadicCayleyTangentModulus_eq_two_pow_tangentRank]
  exact ENNReal.inv_mul_cancel (by positivity) (by simp)

end PositiveDefiniteIntegralLattice
