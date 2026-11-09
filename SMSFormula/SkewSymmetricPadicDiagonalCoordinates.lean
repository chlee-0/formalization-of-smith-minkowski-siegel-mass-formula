import SMSFormula.SkewSymmetricMatrixBasis

/-!
# Strict-upper coordinates for p-adic diagonal congruence

Conjugating the p-adic diagonal congruence endomorphism by the
strict-upper coordinate equivalence gives pointwise multiplication:
the coordinate indexed by `i < j` is multiplied by `d i * d j`.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ}

/-- The p-adic diagonal congruence endomorphism conjugated to
strict-upper coordinates. -/
def skewSymmetricPadicDiagonalCoordinateEndomorphism
    (hchar : ringChar ℚ_[p] ≠ 2) (d : Fin n → ℚ_[p]) :
    (StrictUpperPair n → ℚ_[p]) →ₗ[ℚ_[p]]
      (StrictUpperPair n → ℚ_[p]) :=
  (skewSymmetricUpperCoordinateEquiv hchar).toLinearMap.comp <|
    (skewSymmetricPadicCongruenceEndomorphism p (diagonal d)).toLinearMap.comp
      (skewSymmetricUpperCoordinateEquiv hchar).symm.toLinearMap

theorem skewSymmetricPadicDiagonalCoordinateEndomorphism_apply
    (hchar : ringChar ℚ_[p] ≠ 2) (d : Fin n → ℚ_[p])
    (c : StrictUpperPair n → ℚ_[p]) :
    skewSymmetricPadicDiagonalCoordinateEndomorphism p hchar d c =
      skewSymmetricUpperCoordinateEquiv hchar
        (skewSymmetricPadicCongruenceEndomorphism p (diagonal d)
          ((skewSymmetricUpperCoordinateEquiv hchar).symm c)) :=
  rfl

/-- In strict-upper coordinates, diagonal congruence is pointwise
multiplication by `q ↦ d q.1 * d q.2`. -/
@[simp]
theorem skewSymmetricPadicDiagonalCoordinateEndomorphism_apply_apply
    (hchar : ringChar ℚ_[p] ≠ 2) (d : Fin n → ℚ_[p])
    (c : StrictUpperPair n → ℚ_[p]) (q : StrictUpperPair n) :
    skewSymmetricPadicDiagonalCoordinateEndomorphism p hchar d c q =
      d q.1.1 * d q.1.2 * c q := by
  change
    ((diagonal d)ᵀ * skewSymmetricMatrixOfUpperCoordinates c *
        diagonal d) q.1.1 q.1.2 =
      d q.1.1 * d q.1.2 * c q
  simp [q.2, Matrix.diagonal_transpose,
    skewSymmetricMatrixOfUpperCoordinates]
  ring

end Matrix
