import SMSFormula.SkewSymmetricPadicGeneralCongruenceCharacter
import SMSFormula.PadicCayleyLeftTrivializedInversePowerDeterminant
import SMSFormula.SkewAdjointPadicMeasureGeneralTransport
import SMSFormula.PadicCayleyLeftTrivializedInverseModulus

/-!
# P-adic Cayley coordinate Jacobian density

The explicit inverse determinant modulus of the full intrinsic
left-trivialized Cayley differential defines a scalar density on the
transported skew-adjoint coordinate space. Its formula is continuous before
any restriction to the Cayley source.

This file does not apply `Measure.withDensity`, construct a Cayley-chart
measure, move a measure to the orthogonal group, or glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator NNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The explicit nonnegative coordinate Jacobian density of the full intrinsic
left-trivialized p-adic Cayley differential. -/
def skewAdjointPadicCayleyCoordinateJacobianDensity
    (F : Matrix (Fin n) (Fin n) ℚ)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) : ℝ≥0 :=
  ‖(2 : ℚ_[p])‖₊⁻¹ ^
      Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) *
    ‖Matrix.det
      (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^ (n - 1)

/-- The explicit p-adic Cayley coordinate Jacobian density is continuous on
the full transported skew-adjoint coordinate space. -/
theorem continuous_skewAdjointPadicCayleyCoordinateJacobianDensity
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Continuous (skewAdjointPadicCayleyCoordinateJacobianDensity p n F) := by
  unfold skewAdjointPadicCayleyCoordinateJacobianDensity
  fun_prop

end Matrix
