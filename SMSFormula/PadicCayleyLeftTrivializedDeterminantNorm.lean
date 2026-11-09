import SMSFormula.PadicCayleyLeftTrivializedInversePowerDeterminant

/-!
# Norm of the p-adic left-trivialized Cayley determinant

Taking the p-adic norm of the full determinant formula gives the
product of the scalar tangent norm and the inverse denominator-determinant
norm power.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The norm of the full intrinsic left-trivialized Cayley differential
determinant is `‖2‖^d * (‖det(1-X)‖^(n-1))⁻¹`. -/
theorem
    norm_det_skewAdjointPadicCayleyLeftTrivializedEndomorphism
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap‖ =
      ‖(2 : ℚ_[p])‖ ^
          Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) *
        (‖Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))‖ ^ (n - 1))⁻¹ := by
  rw [
    det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_eq_two_pow_mul_det_pow_inv
      p n F hF hdet X hX,
    norm_mul,
    norm_pow,
    norm_inv,
    norm_pow]

end Matrix
