import SMSFormula.SkewSymmetricPadicCongruenceEquiv

/-!
# The p-adic skew-symmetric congruence determinant character

The nonzero determinant of congruence by a p-adic matrix unit defines a
multiplicative character from the general linear group to p-adic units.

This file does not compare the character with a power of the matrix
determinant, take norms, pull back determinant forms, transport measures, or
glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The unit-valued determinant character of congruence on skew-symmetric
matrices. -/
def skewSymmetricPadicCongruenceDetCharacter :
    GL ι ℚ_[p] →* ℚ_[p]ˣ where
  toFun W :=
    Units.mk0
      (LinearMap.det
        (skewSymmetricPadicCongruenceEndomorphism
          p (W : Matrix ι ι ℚ_[p])).toLinearMap)
      (det_skewSymmetricPadicCongruenceEndomorphism_ne_zero p W)
  map_one' := by
    apply Units.ext
    change LinearMap.det
        (skewSymmetricPadicCongruenceEndomorphism
          p ((1 : GL ι ℚ_[p]) : Matrix ι ι ℚ_[p])).toLinearMap =
      (1 : ℚ_[p])
    rw [Matrix.GeneralLinearGroup.coe_one,
      skewSymmetricPadicCongruenceEndomorphism_one]
    exact LinearMap.det_id
  map_mul' W Z := by
    apply Units.ext
    change LinearMap.det
        (skewSymmetricPadicCongruenceEndomorphism
          p ((W * Z : GL ι ℚ_[p]) : Matrix ι ι ℚ_[p])).toLinearMap =
      LinearMap.det
          (skewSymmetricPadicCongruenceEndomorphism
            p (W : Matrix ι ι ℚ_[p])).toLinearMap *
        LinearMap.det
          (skewSymmetricPadicCongruenceEndomorphism
            p (Z : Matrix ι ι ℚ_[p])).toLinearMap
    rw [Matrix.GeneralLinearGroup.coe_mul]
    exact det_skewSymmetricPadicCongruenceEndomorphism_mul p _ _

/-- The underlying p-adic scalar of the determinant character is the
algebraic determinant of the congruence endomorphism. -/
@[simp]
theorem coe_skewSymmetricPadicCongruenceDetCharacter_apply
    (W : GL ι ℚ_[p]) :
    (skewSymmetricPadicCongruenceDetCharacter p W : ℚ_[p]) =
      LinearMap.det
        (skewSymmetricPadicCongruenceEndomorphism
          p (W : Matrix ι ι ℚ_[p])).toLinearMap :=
  rfl

/-- The determinant character sends an inverse matrix unit to the inverse
unit value. -/
@[simp]
theorem skewSymmetricPadicCongruenceDetCharacter_inv
    (W : GL ι ℚ_[p]) :
    skewSymmetricPadicCongruenceDetCharacter p W⁻¹ =
      (skewSymmetricPadicCongruenceDetCharacter p W)⁻¹ :=
  map_inv (skewSymmetricPadicCongruenceDetCharacter p) W

end Matrix
