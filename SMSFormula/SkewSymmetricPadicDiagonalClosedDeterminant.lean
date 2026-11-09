import SMSFormula.SkewSymmetricPadicDiagonalDeterminant
import SMSFormula.StrictUpperPairProduct

/-!
# Closed determinant of p-adic diagonal congruence

The determinant of diagonal congruence on skew-symmetric matrices is the
`(n - 1)`st power of the product of the diagonal entries. Equivalently, it is
the same power of the determinant of the original diagonal matrix.

This file does not compute a determinant norm or determinant-form action,
transport a measure, or glue charts.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ}

/-- The determinant of p-adic diagonal congruence is the `(n - 1)`st power
of the product of the diagonal entries. -/
theorem skewSymmetricPadicDiagonalCoordinateEndomorphism_det_closed
    (hchar : ringChar ℚ_[p] ≠ 2) (d : Fin n → ℚ_[p]) :
    LinearMap.det
        (skewSymmetricPadicDiagonalCoordinateEndomorphism p hchar d) =
      (∏ i : Fin n, d i) ^ (n - 1) := by
  rw [skewSymmetricPadicDiagonalCoordinateEndomorphism_det,
    StrictUpperPair.prod_endpoint_mul]

/-- Equivalently, the congruence determinant is the `(n - 1)`st power of the
determinant of the original diagonal matrix. -/
theorem skewSymmetricPadicDiagonalCoordinateEndomorphism_det_diagonal
    (hchar : ringChar ℚ_[p] ≠ 2) (d : Fin n → ℚ_[p]) :
    LinearMap.det
        (skewSymmetricPadicDiagonalCoordinateEndomorphism p hchar d) =
      Matrix.det (diagonal d) ^ (n - 1) := by
  rw [skewSymmetricPadicDiagonalCoordinateEndomorphism_det_closed,
    Matrix.det_diagonal]

end Matrix
