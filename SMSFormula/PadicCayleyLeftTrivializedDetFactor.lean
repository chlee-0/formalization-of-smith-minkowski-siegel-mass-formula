import SMSFormula.PadicCayleyLeftTrivializedDetInverse
import SMSFormula.PadicCayleyTangentFactor

/-!
# Determinant factorization for the p-adic Cayley differential

The intrinsic left-trivialized Cayley differential factors into its scalar
identity tangent factor and the unscaled two-sided denominator action. Taking
determinants isolates the known factor `2^d` from the still unevaluated
denominator-action determinant.

This file does not evaluate the denominator-action determinant, compute a
determinant norm or determinant-form pullback, transport a measure, or glue
charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unscaled two-sided denominator action in the left-trivialized Cayley
differential. -/
def skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (2 : ℚ_[p])⁻¹ •
    skewAdjointPadicCayleyLeftTrivializedEndomorphism F p X hX

/-- The unscaled intrinsic endomorphism has the literal two-sided
inverse-denominator matrix formula. -/
@[simp]
theorem coe_skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism
        F p X hX H : Matrix ι ι ℚ_[p]) =
      (1 + (X : Matrix ι ι ℚ_[p]))⁻¹ *
        (H : Matrix ι ι ℚ_[p]) *
        (1 - (X : Matrix ι ι ℚ_[p]))⁻¹ := by
  change
    (2 : ℚ_[p])⁻¹ •
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX H : Matrix ι ι ℚ_[p]) =
      _
  rw [coe_skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply,
    two_nsmul, ← two_smul ℚ_[p], smul_smul]
  norm_num

/-- The intrinsic left-trivialized derivative is the identity tangent factor
composed with the unscaled denominator action. -/
theorem skewAdjointPadicCayleyLeftTrivializedEndomorphism_factor
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyLeftTrivializedEndomorphism F p X hX =
      (skewAdjointPadicCayleyTangentFactor F p).comp
        (skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism
          F p X hX) := by
  apply ContinuousLinearMap.ext
  intro H
  apply Subtype.ext
  rw [coe_skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply]
  simp

/-- The determinant of the intrinsic left-trivialized derivative is the
product of the scalar tangent determinant and the unscaled denominator-action
determinant. -/
theorem det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_factor
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap =
      LinearMap.det
          (skewAdjointPadicCayleyTangentFactor F p).toLinearMap *
        LinearMap.det
          (skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism
            F p X hX).toLinearMap := by
  rw [skewAdjointPadicCayleyLeftTrivializedEndomorphism_factor]
  exact LinearMap.det_comp _ _

/-- Expanding the scalar tangent determinant isolates the known factor
`2^d`, leaving the denominator-action determinant unevaluated. -/
theorem det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_eq_two_pow_mul
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap =
      (2 : ℚ_[p]) ^
          Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) *
        LinearMap.det
          (skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism
            F p X hX).toLinearMap := by
  rw [det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_factor,
    det_skewAdjointPadicCayleyTangentFactor]

end Matrix
