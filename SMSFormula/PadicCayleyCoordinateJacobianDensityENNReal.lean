import SMSFormula.PadicCayleyCoordinateJacobianDensityPositive

/-!
# Extended p-adic Cayley coordinate Jacobian density

The continuous nonnegative p-adic Cayley coordinate Jacobian density is
coerced to the nonnegative extended reals. The resulting function is
continuous, hence measurable, on the full transported skew-adjoint coordinate
space.

This file does not apply `Measure.withDensity`, construct a Cayley-chart
measure, move a measure to the orthogonal group, or glue charts.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance skewAdjointPadicCayleyJacobianDensityMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicCayleyJacobianDensityBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The explicit p-adic Cayley coordinate Jacobian density in the nonnegative
extended reals, as required by `Measure.withDensity`. -/
def skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) : ℝ≥0∞ :=
  skewAdjointPadicCayleyCoordinateJacobianDensity p n F X

/-- The extended p-adic Cayley coordinate Jacobian density is continuous on
the full transported skew-adjoint coordinate space. -/
theorem continuous_skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Continuous
      (skewAdjointPadicCayleyCoordinateJacobianDensityENNReal p n F) :=
  ENNReal.continuous_coe.comp
    (continuous_skewAdjointPadicCayleyCoordinateJacobianDensity p n F)

/-- The extended p-adic Cayley coordinate Jacobian density is measurable on
the full transported skew-adjoint coordinate space. -/
theorem measurable_skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Measurable
      (skewAdjointPadicCayleyCoordinateJacobianDensityENNReal p n F) :=
  (continuous_skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
    p n F).measurable

end Matrix
