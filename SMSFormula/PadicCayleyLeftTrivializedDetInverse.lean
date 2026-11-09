import SMSFormula.PadicCayleyLeftTrivializedDetNonzero

/-!
# Inverse determinant identities for the p-adic Cayley differential

At every point of the explicit Cayley source for a nonsingular rational
form, the determinants of the intrinsic left-trivialized derivative and its
explicit inverse are mutual inverses and multiply to one.

This file does not evaluate either determinant, compute a determinant norm,
pull back a determinant form, transport a measure, or glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of the explicit inverse is the inverse determinant of
the intrinsic left-trivialized derivative. -/
theorem det_skewAdjointPadicCayleyLeftTrivializedInverse_eq_inv
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedInverse F p X).toLinearMap =
      (LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap)⁻¹ := by
  change LinearMap.det
      (skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv
        F p hF X hX).toLinearEquiv.symm.toLinearMap =
    (LinearMap.det
      (skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv
        F p hF X hX).toLinearEquiv.toLinearMap)⁻¹
  exact LinearEquiv.det_coe_symm _

/-- The determinant of the intrinsic left-trivialized derivative is the
inverse determinant of its explicit inverse. -/
theorem det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_eq_inv
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap =
      (LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedInverse F p X).toLinearMap)⁻¹ := by
  rw [det_skewAdjointPadicCayleyLeftTrivializedInverse_eq_inv
    F p hF X hX]
  rw [inv_inv]

/-- The determinants of the intrinsic left-trivialized derivative and its
explicit inverse multiply to one. -/
theorem det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_mul_inverse
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    LinearMap.det
          (skewAdjointPadicCayleyLeftTrivializedEndomorphism
            F p X hX).toLinearMap *
        LinearMap.det
          (skewAdjointPadicCayleyLeftTrivializedInverse F p X).toLinearMap =
      1 := by
  rw [det_skewAdjointPadicCayleyLeftTrivializedInverse_eq_inv
    F p hF X hX]
  exact mul_inv_cancel₀
    (det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_ne_zero
      F p hF X hX)

end Matrix
