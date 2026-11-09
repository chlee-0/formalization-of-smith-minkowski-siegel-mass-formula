import SMSFormula.PadicCayleyLeftTrivializedSkewAdjoint

/-!
# Intrinsic left-trivialized p-adic Cayley differential

At a point of the explicit Cayley source, skew-adjoint closure lets the
ambient left-trivialized derivative be codomain-restricted to a continuous
linear endomorphism of the transported skew-adjoint model.

This file does not compute its determinant or determinant form, transport a
measure, or glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The left-trivialized pointwise Cayley derivative as a continuous linear
endomorphism of the transported skew-adjoint model. -/
def skewAdjointPadicCayleyLeftTrivializedEndomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointPadicCayleyLeftTrivializedDerivative F p X).codRestrict _
    (fun H =>
      skewAdjointPadicCayleyLeftTrivializedDerivative_mem F p X H hX)

/-- Applying the intrinsic endomorphism gives the packaged tangent point. -/
@[simp]
theorem skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyLeftTrivializedEndomorphism F p X hX H =
      skewAdjointPadicCayleyLeftTrivializedPoint F p X H hX :=
  rfl

/-- The intrinsic endomorphism is given by the left-trivialized ambient matrix
formula. -/
@[simp]
theorem coe_skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicCayleyLeftTrivializedEndomorphism F p X hX H :
        Matrix ι ι ℚ_[p]) =
      2 • ((1 + (X : Matrix ι ι ℚ_[p]))⁻¹ *
        (H : Matrix ι ι ℚ_[p]) *
        (1 - (X : Matrix ι ι ℚ_[p]))⁻¹) :=
  coe_skewAdjointPadicCayleyLeftTrivializedPoint F p X H hX

/-- Composing the intrinsic endomorphism with the canonical ambient
inclusion recovers the ambient left-trivialized derivative. -/
theorem skewAdjointPadicAmbientInclusion_comp_cayleyLeftTrivializedEndomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicAmbientInclusion F p).comp
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism F p X hX) =
      skewAdjointPadicCayleyLeftTrivializedDerivative F p X :=
  rfl

end Matrix
