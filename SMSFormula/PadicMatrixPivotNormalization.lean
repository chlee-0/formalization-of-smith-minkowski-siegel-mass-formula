import SMSFormula.PadicMatrixPivot
import Mathlib.LinearAlgebra.Matrix.Swap

/-!
# Integral normalization of a p-adic matrix pivot

For a supplied minimum-valuation pivot of a nonempty square p-adic matrix,
integral row and column swaps move the pivot to coordinate `(0, 0)`. An
integral one-coordinate diagonal factor removes its unit part, leaving exactly
the signed power of `p` determined by the pivot valuation.

No other row or column entry is cleared, and no matrix decomposition is
asserted.
-/

noncomputable section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The integral general-linear element that scales one coordinate by a
unit. -/
def coordinateUnit (i : n) (u : Rˣ) : GL n R where
  val := Matrix.diagonal fun j => if j = i then (u : R) else 1
  inv := Matrix.diagonal fun j => if j = i then (u⁻¹ : Rˣ) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr with j
    by_cases h : j = i <;> simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr with j
    by_cases h : j = i <;> simp [h]

@[simp]
theorem coordinateUnit_apply (i j k : n) (u : Rˣ) :
    (coordinateUnit i u : Matrix n n R) j k =
      if j = k then if j = i then (u : R) else 1 else 0 := by
  by_cases h : j = k <;> simp [coordinateUnit, h]

end Matrix.GeneralLinearGroup

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- The integral row swap that moves the pivot row to row zero. -/
def rowSwap (P : PadicPivot p A) : GL (Fin (d + 1)) ℤ_[p] :=
  GeneralLinearGroup.swap ℤ_[p] 0 P.row

/-- The integral column swap that moves the pivot column to column zero. -/
def colSwap (P : PadicPivot p A) : GL (Fin (d + 1)) ℤ_[p] :=
  GeneralLinearGroup.swap ℤ_[p] 0 P.col

/-- Scale row zero by the inverse of the integral unit part of the pivot. -/
def pivotUnitScale (P : PadicPivot p A) : GL (Fin (d + 1)) ℤ_[p] :=
  GeneralLinearGroup.coordinateUnit 0
    (Padic.integralUnitPart p (A P.row P.col) P.ne_zero)⁻¹

/-- The integral left factor that first swaps the pivot row to zero and then
removes the pivot's unit part. -/
def leftNormalization (P : PadicPivot p A) : GL (Fin (d + 1)) ℤ_[p] :=
  P.pivotUnitScale * P.rowSwap

/-- The integral right factor that swaps the pivot column to zero. -/
def rightNormalization (P : PadicPivot p A) : GL (Fin (d + 1)) ℤ_[p] :=
  P.colSwap

/-- Apply the integral pivot-normalization factors after extending them from
`Z_p` to `Q_p`. -/
def normalizedMatrix (P : PadicPivot p A) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p] :=
  (GeneralLinearGroup.map PadicInt.Coe.ringHom P.leftNormalization :
      GL (Fin (d + 1)) ℚ_[p]) *
    A *
  (GeneralLinearGroup.map PadicInt.Coe.ringHom P.rightNormalization :
      GL (Fin (d + 1)) ℚ_[p])

/-- Integral row/column permutation and unit scaling normalize the supplied
pivot to its signed prime-power part at coordinate `(0, 0)`. -/
theorem normalizedMatrix_zero_zero (P : PadicPivot p A) :
    P.normalizedMatrix 0 0 =
      (p : ℚ_[p]) ^ (A P.row P.col).valuation := by
  simp [normalizedMatrix, leftNormalization, pivotUnitScale, rowSwap,
    rightNormalization, colSwap, GeneralLinearGroup.coordinateUnit]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul,
    Matrix.swap_mul_apply_left]
  let x : ℚ_[p] := A P.row P.col
  let u : ℤ_[p]ˣ := Padic.integralUnitPart p x P.ne_zero
  have hfactor :
      ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ x.valuation = x :=
    Padic.integralUnitPart_mul_p_zpow p x P.ne_zero
  change (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * x =
    (p : ℚ_[p]) ^ x.valuation
  calc
    (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * x =
        (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
          (((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ x.valuation) :=
      congrArg
        (fun y : ℚ_[p] => (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * y)
        hfactor.symm
    _ = (p : ℚ_[p]) ^ x.valuation := by
      rw [← mul_assoc]
      have hu :
          (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
              (((u : ℤ_[p]) : ℚ_[p])) = 1 := by
        change PadicInt.Coe.ringHom ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
            PadicInt.Coe.ringHom (u : ℤ_[p]) = 1
        rw [← map_mul]
        simp
      rw [hu, one_mul]

end Matrix.PadicPivot
