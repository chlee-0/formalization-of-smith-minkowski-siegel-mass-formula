import SMSFormula.PadicCayleyCoordinateJacobianDensityENNReal

/-!
# Positivity of the extended p-adic Cayley coordinate Jacobian density

The strict positivity of the nonnegative p-adic Cayley coordinate Jacobian
density on the Cayley source persists under its coercion to the nonnegative
extended reals.

This file does not apply `Measure.withDensity`, construct a Cayley-chart
measure, move a measure to the orthogonal group, or glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The extended p-adic Cayley coordinate Jacobian density is strictly
positive at every point of the transported skew-adjoint Cayley source. -/
theorem skewAdjointPadicCayleyCoordinateJacobianDensityENNReal_pos
    (F : Matrix (Fin n) (Fin n) ℚ)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    0 < skewAdjointPadicCayleyCoordinateJacobianDensityENNReal p n F X := by
  change
    (0 : ℝ≥0∞) <
      (skewAdjointPadicCayleyCoordinateJacobianDensity p n F X : ℝ≥0∞)
  exact_mod_cast
    skewAdjointPadicCayleyCoordinateJacobianDensity_pos p n F X hX

end Matrix
