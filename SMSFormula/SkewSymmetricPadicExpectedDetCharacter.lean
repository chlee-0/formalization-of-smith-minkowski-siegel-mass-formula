import SMSFormula.SkewSymmetricPadicCongruenceDetCharacter
import SMSFormula.SkewSymmetricPadicDiagonalClosedDeterminant
import Mathlib.Algebra.Group.Pi.Units

/-!
# The expected p-adic skew-symmetric congruence determinant character

The expected character on `GL_n(Q_p)` is the `(n - 1)`st power of the usual
matrix determinant. It agrees with the congruence determinant
character on diagonal matrices with unit-valued entries.

This file does not prove equality of the two characters on general matrices.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The expected determinant character for congruence on skew-symmetric
`n × n` matrices. -/
def skewSymmetricPadicExpectedCongruenceDetCharacter :
    GL (Fin n) ℚ_[p] →* ℚ_[p]ˣ where
  toFun W := Matrix.GeneralLinearGroup.det W ^ (n - 1)
  map_one' := by simp
  map_mul' W Z := by
    rw [map_mul, mul_pow]

/-- The underlying scalar of the expected character is
`det(W) ^ (n - 1)`. -/
@[simp]
theorem coe_skewSymmetricPadicExpectedCongruenceDetCharacter_apply
    (W : GL (Fin n) ℚ_[p]) :
    (skewSymmetricPadicExpectedCongruenceDetCharacter p n W : ℚ_[p]) =
      Matrix.det (W : Matrix (Fin n) (Fin n) ℚ_[p]) ^ (n - 1) :=
  rfl

/-- The general-linear diagonal matrix associated to unit-valued entries. -/
def skewSymmetricPadicDiagonalGeneralLinear
    (d : Fin n → ℚ_[p]ˣ) :
    GL (Fin n) ℚ_[p] :=
  Units.map (Matrix.diagonalRingHom (Fin n) ℚ_[p])
    ((MulEquiv.piUnits :
      (Fin n → ℚ_[p])ˣ ≃* (Fin n → ℚ_[p]ˣ)).symm d)

/-- The underlying matrix of the diagonal general-linear element is the
diagonal matrix of the underlying scalar entries. -/
@[simp]
theorem coe_skewSymmetricPadicDiagonalGeneralLinear
    (d : Fin n → ℚ_[p]ˣ) :
    (skewSymmetricPadicDiagonalGeneralLinear p n d :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      diagonal (fun i => (d i : ℚ_[p])) :=
  rfl

/-- Passing from skew-symmetric matrices to strict-upper coordinates does not
change the determinant of diagonal congruence. -/
theorem det_skewSymmetricPadicCongruenceEndomorphism_diagonal
    (hchar : ringChar ℚ_[p] ≠ 2) (d : Fin n → ℚ_[p]) :
    LinearMap.det
        (skewSymmetricPadicCongruenceEndomorphism
          p (diagonal d)).toLinearMap =
      Matrix.det (diagonal d) ^ (n - 1) := by
  have hconj :
      LinearMap.det
          (skewSymmetricPadicDiagonalCoordinateEndomorphism
            p hchar d) =
        LinearMap.det
          (skewSymmetricPadicCongruenceEndomorphism
            p (diagonal d)).toLinearMap := by
    simpa only [skewSymmetricPadicDiagonalCoordinateEndomorphism,
      LinearMap.comp_assoc] using
      LinearMap.det_conj
        (skewSymmetricPadicCongruenceEndomorphism
          p (diagonal d)).toLinearMap
        (skewSymmetricUpperCoordinateEquiv hchar)
  rw [← hconj]
  exact skewSymmetricPadicDiagonalCoordinateEndomorphism_det_diagonal
    p hchar d

/-- The congruence determinant character agrees with the expected determinant
power character on diagonal matrices with unit-valued entries. -/
theorem skewSymmetricPadicCongruenceDetCharacter_diagonal_eq_expected
    (hchar : ringChar ℚ_[p] ≠ 2) (d : Fin n → ℚ_[p]ˣ) :
    skewSymmetricPadicCongruenceDetCharacter p
        (skewSymmetricPadicDiagonalGeneralLinear p n d) =
      skewSymmetricPadicExpectedCongruenceDetCharacter p n
        (skewSymmetricPadicDiagonalGeneralLinear p n d) := by
  apply Units.ext
  change LinearMap.det
      (skewSymmetricPadicCongruenceEndomorphism
        p (diagonal (fun i => (d i : ℚ_[p])))).toLinearMap =
    Matrix.det (diagonal (fun i => (d i : ℚ_[p]))) ^ (n - 1)
  exact det_skewSymmetricPadicCongruenceEndomorphism_diagonal
    p n hchar _

end Matrix
