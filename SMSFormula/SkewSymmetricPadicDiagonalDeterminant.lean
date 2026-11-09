import SMSFormula.SkewSymmetricPadicDiagonalCoordinates

/-!
# Determinant of p-adic diagonal congruence coordinates

The strict-upper coordinate matrix of diagonal congruence is diagonal, with
entry `d i * d j` at the coordinate indexed by `i < j`. Its determinant is
therefore the product of those entries.

This file does not simplify that product, compute a determinant norm or
determinant-form action, transport a measure, or glue charts.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ}

/-- The matrix of the p-adic diagonal congruence coordinate endomorphism in
the canonical function basis is diagonal. -/
theorem toMatrix_skewSymmetricPadicDiagonalCoordinateEndomorphism
    (hchar : ringChar ℚ_[p] ≠ 2) (d : Fin n → ℚ_[p]) :
    LinearMap.toMatrix (Pi.basisFun ℚ_[p] (StrictUpperPair n))
        (Pi.basisFun ℚ_[p] (StrictUpperPair n))
        (skewSymmetricPadicDiagonalCoordinateEndomorphism p hchar d) =
      diagonal (fun q : StrictUpperPair n => d q.1.1 * d q.1.2) := by
  ext i j
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr,
    skewSymmetricPadicDiagonalCoordinateEndomorphism_apply_apply]
  by_cases hij : i = j
  · subst i
    rw [Matrix.diagonal_apply_eq]
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    simp [hij]

/-- The determinant of p-adic diagonal congruence in strict-upper
coordinates is the unsimplified product of its coordinate multipliers. -/
theorem skewSymmetricPadicDiagonalCoordinateEndomorphism_det
    (hchar : ringChar ℚ_[p] ≠ 2) (d : Fin n → ℚ_[p]) :
    LinearMap.det
        (skewSymmetricPadicDiagonalCoordinateEndomorphism p hchar d) =
      ∏ q : StrictUpperPair n, d q.1.1 * d q.1.2 := by
  rw [← LinearMap.det_toMatrix
    (Pi.basisFun ℚ_[p] (StrictUpperPair n))]
  rw [toMatrix_skewSymmetricPadicDiagonalCoordinateEndomorphism,
    Matrix.det_diagonal]

end Matrix
