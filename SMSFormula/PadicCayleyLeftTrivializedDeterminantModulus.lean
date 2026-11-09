import SMSFormula.PadicCayleyLeftTrivializedDeterminantNorm

/-!
# Nonnegative modulus of the p-adic Cayley determinant

The real-valued norm formula for the full left-trivialized Cayley determinant
lifts directly to a nonnegative-real modulus identity.

This file does not pull back determinant forms, transport measures, or glue
charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator NNReal Topology

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The nonnegative modulus of the full intrinsic left-trivialized Cayley
differential determinant is `‖2‖₊^d * (‖det(1-X)‖₊^(n-1))⁻¹`. -/
theorem
    nnnorm_det_skewAdjointPadicCayleyLeftTrivializedEndomorphism
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap‖₊ =
      ‖(2 : ℚ_[p])‖₊ ^
          Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) *
        (‖Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^ (n - 1))⁻¹ := by
  apply NNReal.eq
  simpa only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv] using
    norm_det_skewAdjointPadicCayleyLeftTrivializedEndomorphism
      p n F hF hdet X hX

end Matrix
