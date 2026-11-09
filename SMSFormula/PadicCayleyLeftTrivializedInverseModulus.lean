import SMSFormula.PadicCayleyLeftTrivializedDeterminantModulus

/-!
# Inverse modulus of the p-adic Cayley determinant

Inverting the nonnegative modulus formula gives the scalar inverse
tangent modulus times the denominator-determinant norm power.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator NNReal Topology

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The inverse nonnegative modulus of the full intrinsic left-trivialized
Cayley differential determinant is
`(‖2‖₊⁻¹)^d * ‖det(1-X)‖₊^(n-1)`. -/
theorem
    inv_nnnorm_det_skewAdjointPadicCayleyLeftTrivializedEndomorphism
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap‖₊⁻¹ =
      ‖(2 : ℚ_[p])‖₊⁻¹ ^
          Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) *
        ‖Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^ (n - 1) := by
  rw [
    nnnorm_det_skewAdjointPadicCayleyLeftTrivializedEndomorphism
      p n F hF hdet X hX,
    mul_inv,
    inv_inv,
    inv_pow]

end Matrix
