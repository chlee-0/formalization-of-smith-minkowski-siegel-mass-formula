import SMSFormula.PadicCayleyDenominatorDeterminant

/-!
# Determinant of the p-adic left-trivialized Cayley differential

Substituting the closed intrinsic denominator-action determinant into the
scalar-factor decomposition evaluates the full left-trivialized Cayley
differential determinant.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The full intrinsic left-trivialized Cayley differential has determinant
`2^d det((1-X)⁻¹)^(n-1)`. -/
theorem
    det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_eq_two_pow_mul_det_inv_pow
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap =
      (2 : ℚ_[p]) ^
          Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) *
        Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹ ^ (n - 1) := by
  rw [det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_eq_two_pow_mul,
    det_skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism_eq_det_inv_pow
      p n F hF hdet X hX]

end Matrix
