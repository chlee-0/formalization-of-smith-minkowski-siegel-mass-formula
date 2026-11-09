import SMSFormula.PadicCayleyPointwiseDifferential

/-!
# Restricted pointwise differential of the p-adic Cayley map

At every point of the transported skew-adjoint Cayley source, composing the
ambient pointwise derivative with the canonical skew-adjoint inclusion gives
the derivative of the restricted forward map.

No left translation, determinant, measure transport, chart gluing, or
stabilizer-volume calculation is introduced.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pointwise ambient Cayley derivative restricted to the transported
skew-adjoint model. -/
def skewAdjointPadicCayleyForwardDerivative
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
        Matrix ι ι ℚ_[p] :=
  (padicCayleyForwardDerivative p X).comp
    (skewAdjointPadicAmbientInclusion F p)

@[simp]
theorem skewAdjointPadicCayleyForwardDerivative_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyForwardDerivative F p X H =
      2 • ((1 - (X : Matrix ι ι ℚ_[p]))⁻¹ *
        (H : Matrix ι ι ℚ_[p]) *
        (1 - (X : Matrix ι ι ℚ_[p]))⁻¹) := by
  rfl

/-- The restricted p-adic Cayley forward map has the explicit pointwise
derivative obtained by composing the ambient derivative with the canonical
skew-adjoint inclusion. -/
theorem hasFDerivAt_skewAdjointPadicCayleyForwardMatrix
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    HasFDerivAt
      (skewAdjointPadicCayleyForwardMatrix F p)
      (skewAdjointPadicCayleyForwardDerivative F p X)
      X := by
  have hcomp :=
    (hasFDerivAt_padicCayleyForwardMatrix p
      (X : Matrix ι ι ℚ_[p]) hX).comp
        X (skewAdjointPadicAmbientInclusion F p).hasFDerivAt
  convert hcomp using 1

end Matrix
