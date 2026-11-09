import SMSFormula.PadicCayleyTangentNorm

/-!
# Nonnegative modulus of the p-adic Cayley tangent determinant

The nonnegative norm of the intrinsic Cayley tangent determinant is
`‖2‖₊ ^ d`. Its inverse modulus is one at odd primes and is `2 ^ d` at the
dyadic place.

No top-form or measure transport, chart gluing, or stabilizer-volume
calculation is introduced.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator NNReal Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The nonnegative norm of the intrinsic Cayley tangent determinant is the
corresponding power of the nonnegative p-adic norm of `2`. -/
theorem nnnorm_det_skewAdjointPadicCayleyTangentFactor
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor F p).toLinearMap‖₊ =
      ‖(2 : ℚ_[p])‖₊ ^
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  apply NNReal.eq
  simpa only [coe_nnnorm, NNReal.coe_pow] using
    norm_det_skewAdjointPadicCayleyTangentFactor F p

/-- The inverse nonnegative modulus is the corresponding power of the inverse
nonnegative p-adic norm of `2`. -/
theorem inv_nnnorm_det_skewAdjointPadicCayleyTangentFactor
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor F p).toLinearMap‖₊⁻¹ =
      ‖(2 : ℚ_[p])‖₊⁻¹ ^
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  rw [nnnorm_det_skewAdjointPadicCayleyTangentFactor, inv_pow]

/-- The nonnegative p-adic norm of `2` is one away from the dyadic place. -/
theorem nnnorm_two_padic_eq_one_of_ne_two
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    ‖(2 : ℚ_[p])‖₊ = 1 := by
  apply NNReal.eq
  simpa only [coe_nnnorm, NNReal.coe_one] using
    norm_two_padic_eq_one_of_ne_two p hp_two

/-- At every odd prime, the intrinsic Cayley tangent determinant has
nonnegative norm one. -/
theorem nnnorm_det_skewAdjointPadicCayleyTangentFactor_of_ne_two
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor F p).toLinearMap‖₊ = 1 := by
  rw [nnnorm_det_skewAdjointPadicCayleyTangentFactor,
    nnnorm_two_padic_eq_one_of_ne_two p hp_two, one_pow]

/-- At every odd prime, the inverse modulus of the intrinsic Cayley tangent
determinant is one. -/
theorem inv_nnnorm_det_skewAdjointPadicCayleyTangentFactor_of_ne_two
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor F p).toLinearMap‖₊⁻¹ = 1 := by
  rw [nnnorm_det_skewAdjointPadicCayleyTangentFactor_of_ne_two F p hp_two,
    inv_one]

/-- The nonnegative dyadic norm of `2` is `2⁻¹`. -/
theorem nnnorm_two_dyadic :
    ‖(2 : ℚ_[2])‖₊ = (2 : ℝ≥0)⁻¹ := by
  apply NNReal.eq
  simpa only [coe_nnnorm, NNReal.coe_inv, NNReal.coe_ofNat] using
    norm_two_dyadic

/-- At the dyadic place, the intrinsic Cayley tangent determinant has
nonnegative norm `(2⁻¹)^d`. -/
theorem nnnorm_det_skewAdjointPadicCayleyTangentFactor_two
    (F : Matrix ι ι ℚ) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor F 2).toLinearMap‖₊ =
      ((2 : ℝ≥0)⁻¹) ^
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  rw [nnnorm_det_skewAdjointPadicCayleyTangentFactor, nnnorm_two_dyadic]

/-- At the dyadic place, the inverse modulus of the intrinsic Cayley tangent
determinant is `2^d`. -/
theorem inv_nnnorm_det_skewAdjointPadicCayleyTangentFactor_two
    (F : Matrix ι ι ℚ) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor F 2).toLinearMap‖₊⁻¹ =
      (2 : ℝ≥0) ^
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  rw [nnnorm_det_skewAdjointPadicCayleyTangentFactor_two, inv_pow, inv_inv]

end Matrix
