import SMSFormula.PadicCayleyCoordinateJacobianDensity

/-!
# Positivity of the p-adic Cayley coordinate Jacobian density

On the Cayley source, the denominator matrix `1-X` is a unit, so its
determinant norm is positive. The scalar tangent factor is also positive,
hence the explicit coordinate Jacobian density is strictly positive.

This file does not coerce the density to `ℝ≥0∞`, apply
`Measure.withDensity`, construct a Cayley-chart measure, move a measure to the
orthogonal group, or glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator NNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The explicit p-adic Cayley coordinate Jacobian density is strictly
positive at every point of the transported skew-adjoint Cayley source. -/
theorem skewAdjointPadicCayleyCoordinateJacobianDensity_pos
    (F : Matrix (Fin n) (Fin n) ℚ)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    0 < skewAdjointPadicCayleyCoordinateJacobianDensity p n F X := by
  have htwo : (2 : ℚ_[p]) ≠ 0 := by
    norm_num
  have hdet :
      Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p])) ≠
        0 :=
    isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det
        (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))).mp hX)
  unfold skewAdjointPadicCayleyCoordinateJacobianDensity
  exact mul_pos
    (pow_pos (inv_pos.mpr (nnnorm_pos.mpr htwo)) _)
    (pow_pos (nnnorm_pos.mpr hdet) _)

end Matrix
