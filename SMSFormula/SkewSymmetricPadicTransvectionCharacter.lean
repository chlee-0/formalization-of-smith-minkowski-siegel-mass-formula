import SMSFormula.SkewSymmetricPadicExpectedDetCharacter
import SMSFormula.PadicMatrixSingleElimination

/-!
# P-adic skew-symmetric congruence characters on transvections

Both the congruence determinant character and the expected
determinant-power character take the value one on a single general-linear
transvection.

This file does not handle lists of transvections or prove general character
equality, take norms, pull back determinant forms, transport measures, or
glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

private def padicTwoUnit : ℚ_[p]ˣ :=
  Units.mk0 2 (by norm_num)

/-- Conjugating a transvection by the coordinate unit `2` at its source
index gives the square of that transvection. -/
private theorem coordinateUnit_two_conj_transvection
    (t : TransvectionStruct (Fin n) ℚ_[p]) :
    Matrix.GeneralLinearGroup.coordinateUnit t.i (padicTwoUnit p) *
          t.toGeneralLinearGroup *
        (Matrix.GeneralLinearGroup.coordinateUnit
          t.i (padicTwoUnit p))⁻¹ =
      t.toGeneralLinearGroup * t.toGeneralLinearGroup := by
  apply Units.ext
  ext a b
  simp only [Matrix.GeneralLinearGroup.coe_mul,
    Matrix.TransvectionStruct.coe_toGeneralLinearGroup]
  rw [show t.toMatrix = Matrix.transvection t.i t.j t.c by rfl]
  rw [show
    (Matrix.GeneralLinearGroup.coordinateUnit
      t.i (padicTwoUnit p) :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      diagonal (fun j => if j = t.i then
        (padicTwoUnit p : ℚ_[p]) else 1) by rfl]
  rw [show
    (↑((Matrix.GeneralLinearGroup.coordinateUnit
      t.i (padicTwoUnit p))⁻¹) :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      diagonal (fun j => if j = t.i then
        (((padicTwoUnit p)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) else 1) by rfl]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Matrix.transvection_mul_transvection_same
    t.i t.j t.hij t.c t.c]
  have hij : t.i ≠ t.j := t.hij
  by_cases hai : t.i = a <;>
    by_cases hbj : t.j = b <;>
    by_cases hab : b = a <;>
    by_cases hbi : t.i = b <;>
    simp_all [Matrix.transvection, Matrix.single, padicTwoUnit, eq_comm] ; ring

/-- The congruence determinant character is one on every transvection. -/
theorem skewSymmetricPadicCongruenceDetCharacter_transvection
    (t : TransvectionStruct (Fin n) ℚ_[p]) :
    skewSymmetricPadicCongruenceDetCharacter p
        t.toGeneralLinearGroup =
      1 := by
  let χ := skewSymmetricPadicCongruenceDetCharacter
    (ι := Fin n) p
  let D :=
    Matrix.GeneralLinearGroup.coordinateUnit t.i (padicTwoUnit p)
  let T := t.toGeneralLinearGroup
  have hconj : D * T * D⁻¹ = T * T :=
    coordinateUnit_two_conj_transvection p n t
  have hclass : χ (D * T * D⁻¹) = χ T := by
    rw [map_mul, map_mul, map_inv]
    calc
      χ D * χ T * (χ D)⁻¹ =
          χ T * (χ D * (χ D)⁻¹) := by ac_rfl
      _ = χ T := by simp
  have hidem : χ T = χ T * χ T := by
    calc
      χ T = χ (D * T * D⁻¹) := hclass.symm
      _ = χ (T * T) := congrArg χ hconj
      _ = χ T * χ T := map_mul χ T T
  apply mul_left_cancel (a := χ T)
  simpa using hidem.symm

/-- The expected determinant-power character is one on every transvection. -/
theorem skewSymmetricPadicExpectedCongruenceDetCharacter_transvection
    (t : TransvectionStruct (Fin n) ℚ_[p]) :
    skewSymmetricPadicExpectedCongruenceDetCharacter p n
        t.toGeneralLinearGroup =
      1 := by
  apply Units.ext
  change Matrix.det t.toMatrix ^ (n - 1) = (1 : ℚ_[p])
  rw [t.det]
  simp

end Matrix
