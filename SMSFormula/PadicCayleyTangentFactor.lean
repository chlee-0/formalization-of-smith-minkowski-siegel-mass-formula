import SMSFormula.PadicCayleyRestrictedDifferential
import Mathlib.LinearAlgebra.Determinant

/-!
# Intrinsic tangent factor of the p-adic Cayley map

The identity differential of the p-adic Cayley map acts intrinsically on the
transported skew-adjoint tangent model as `2 • id`. Its composition with the
ambient inclusion is the restricted derivative, and its determinant
is `2` raised to the fixed rational skew-adjoint rank.

No determinant norm, top-form or measure transport, chart gluing, or
stabilizer-volume calculation is introduced.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The p-adic scalar extension has the rank of the fixed rational
skew-adjoint model. -/
theorem finrank_skewAdjointScalarExtension_padic
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Module.finrank ℚ_[p]
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule =
      Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis
      (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) F)

/-- The intrinsic tangent factor of the p-adic Cayley map at the identity. -/
def skewAdjointPadicCayleyTangentFactor
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (2 : ℚ_[p]) • ContinuousLinearMap.id ℚ_[p]
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule

@[simp]
theorem skewAdjointPadicCayleyTangentFactor_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyTangentFactor F p X = 2 • X := by
  rfl

/-- Intrinsic multiplication by `2`, followed by the ambient inclusion, is
the restricted Cayley derivative. -/
theorem skewAdjointPadicAmbientInclusion_comp_cayleyTangentFactor
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointPadicAmbientInclusion F p).comp
        (skewAdjointPadicCayleyTangentFactor F p) =
      (2 : ℚ_[p]) • skewAdjointPadicAmbientInclusion F p := by
  ext X i j
  simp

/-- The intrinsic p-adic Cayley tangent factor has determinant `2^d`, where
`d` is the fixed rational skew-adjoint rank. -/
theorem det_skewAdjointPadicCayleyTangentFactor
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    LinearMap.det
        (skewAdjointPadicCayleyTangentFactor F p).toLinearMap =
      (2 : ℚ_[p]) ^
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  change LinearMap.det
      ((2 : ℚ_[p]) •
        (LinearMap.id :
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →ₗ[ℚ_[p]]
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)) = _
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one,
    finrank_skewAdjointScalarExtension_padic F p]

end Matrix
