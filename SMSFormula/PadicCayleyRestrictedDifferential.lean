import SMSFormula.PadicCayleyIdentityDifferential

/-!
# Restricted differential of the p-adic Cayley map

The transported skew-adjoint model includes continuously and linearly into
the ambient p-adic matrix space. Composing this inclusion with the ambient
Cayley differential identifies the derivative of the restricted forward map
at zero as twice that inclusion.

No determinant, top-form or measure transport, chart gluing, or
stabilizer-volume calculation is introduced.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The continuous linear inclusion of the transported skew-adjoint model
into the ambient p-adic matrix space. -/
def skewAdjointPadicAmbientInclusion
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
        Matrix ι ι ℚ_[p] :=
  (skewAdjointMatricesLieSubalgebra
    (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule.subtypeL

@[simp]
theorem skewAdjointPadicAmbientInclusion_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicAmbientInclusion F p X =
      (X : Matrix ι ι ℚ_[p]) :=
  rfl

/-- The derivative at zero of the p-adic Cayley forward map restricted to
the transported skew-adjoint model is twice its ambient inclusion. -/
theorem hasFDerivAt_skewAdjointPadicCayleyForwardMatrix_zero
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    HasFDerivAt
      (skewAdjointPadicCayleyForwardMatrix F p)
      ((2 : ℚ_[p]) • skewAdjointPadicAmbientInclusion F p)
      0 := by
  have hcomp :=
    (hasFDerivAt_padicCayleyForwardMatrix_zero (ι := ι) p).comp
      0 (skewAdjointPadicAmbientInclusion F p).hasFDerivAt
  convert hcomp using 1

end Matrix
