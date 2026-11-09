import SMSFormula.PadicCayleyLeftTrivializedInverseDeterminant

/-!
# Inverse-power form of the p-adic Cayley determinant

The power of the inverse Cayley denominator determinant is the inverse of its
power. Applying this scalar identity to the full left-trivialized
determinant formula exposes one inverse outside the denominator power.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The full intrinsic left-trivialized Cayley differential has determinant
`2^d * (det(1-X)^(n-1))⁻¹`. -/
theorem
    det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_eq_two_pow_mul_det_pow_inv
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap =
      (2 : ℚ_[p]) ^
          Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) *
        (Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p])) ^ (n - 1))⁻¹ := by
  rw [
    det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_eq_two_pow_mul_inv_det_pow
      p n F hF hdet X hX,
    ← inv_pow]

end Matrix
