import SMSFormula.PadicCayleyLeftTrivializedInverse

/-!
# Nonvanishing of the left-trivialized p-adic Cayley determinant

For a nonsingular rational form and a point in the explicit Cayley source,
the intrinsic left-trivialized derivative and its explicit inverse
form a continuous linear equivalence. Its algebraic determinant is therefore
nonzero.

This file does not evaluate that determinant or its norm, pull back a
determinant form, transport a measure, or glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The intrinsic left-trivialized p-adic Cayley derivative as a continuous
linear equivalence at every source point for a nonsingular rational form. -/
def skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ContinuousLinearEquiv.mk
    (LinearEquiv.mk
      (skewAdjointPadicCayleyLeftTrivializedEndomorphism
        F p X hX).toLinearMap
      (skewAdjointPadicCayleyLeftTrivializedInverse F p X)
      (fun H =>
        skewAdjointPadicCayleyLeftTrivializedInverse_apply_endomorphism
          F p hF X H hX)
      (fun K =>
        skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply_inverse
          F p hF X K hX))
    (skewAdjointPadicCayleyLeftTrivializedEndomorphism
      F p X hX).continuous
    (skewAdjointPadicCayleyLeftTrivializedInverse F p X).continuous

/-- The continuous linear equivalence has the intrinsic derivative as its
forward map. -/
@[simp]
theorem skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv
        F p hF X hX H =
      skewAdjointPadicCayleyLeftTrivializedEndomorphism F p X hX H :=
  rfl

/-- The inverse continuous linear equivalence is the explicit inverse
endomorphism. -/
@[simp]
theorem skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv_symm_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X K : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv
        F p hF X hX).symm K =
      skewAdjointPadicCayleyLeftTrivializedInverse F p X K :=
  rfl

/-- The intrinsic left-trivialized derivative has nonzero algebraic
determinant at every source point for a nonsingular rational form. -/
theorem det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_ne_zero
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap ≠ 0 := by
  change LinearMap.det
      (skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv
        F p hF X hX).toLinearEquiv.toLinearMap ≠ 0
  rw [← LinearEquiv.coe_det]
  exact Units.ne_zero _

end Matrix
