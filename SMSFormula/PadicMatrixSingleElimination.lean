import SMSFormula.PadicMatrixPivotNormalization
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# One integral p-adic matrix elimination step

For a supplied nonzero-index row, one integral transvection clears that row's
first-column entry of the normalized pivot matrix. The coefficient is built
from the integral entry-to-pivot ratio and the pivot's
integral unit part. The operation preserves the normalized `(0, 0)` pivot.
-/

noncomputable section

open Matrix

namespace Matrix

@[simp]
theorem map_transvection
    {n R S : Type*} [DecidableEq n] [CommRing R] [CommRing S]
    (f : R →+* S) (i j : n) (c : R) :
    (transvection i j c).map f = transvection i j (f c) := by
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases hia : i = a <;> by_cases hja : j = a <;>
      simp [transvection, Matrix.single, hia, hja]
  · by_cases hia : i = a <;> by_cases hjb : j = b <;>
      simp [transvection, Matrix.single, hab, hia, hjb]

end Matrix

namespace Matrix.TransvectionStruct

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A transvection structure as an element of the general linear group. -/
def toGeneralLinearGroup (t : TransvectionStruct n R) : GL n R where
  val := t.toMatrix
  inv := t.inv.toMatrix
  val_inv := t.mul_inv
  inv_val := t.inv_mul

@[simp]
theorem coe_toGeneralLinearGroup (t : TransvectionStruct n R) :
    (t.toGeneralLinearGroup : Matrix n n R) = t.toMatrix :=
  rfl

end Matrix.TransvectionStruct

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

theorem normalizedMatrix_firstColumn
    (P : PadicPivot p A) (i : Fin (d + 1)) (hi : i ≠ 0) :
    P.normalizedMatrix i 0 =
      A ((Equiv.swap 0 P.row) i) P.col := by
  simp [normalizedMatrix, leftNormalization, pivotUnitScale, rowSwap,
    rightNormalization, colSwap, GeneralLinearGroup.coordinateUnit]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul]
  simp only [hi, ↓reduceIte, PadicInt.coe_one, one_mul]
  change (Matrix.swap ℚ_[p] 0 P.row * A) i P.col =
    A ((Equiv.swap 0 P.row) i) P.col
  simp [Matrix.swap, PEquiv.toMatrix_toPEquiv_mul]

/-- The integral coefficient that clears one nonzero-index first-column
entry of the normalized matrix. -/
def firstColumnEliminationCoefficient
    (P : PadicPivot p A) (i : Fin (d + 1)) : ℤ_[p] :=
  -(P.integralRatioMatrix ((Equiv.swap 0 P.row) i) P.col *
    (Padic.integralUnitPart p (A P.row P.col) P.ne_zero : ℤ_[p]))

theorem normalizedMatrix_add_coefficient_mul_pivot
    (P : PadicPivot p A) (i : Fin (d + 1)) (hi : i ≠ 0) :
    P.normalizedMatrix i 0 +
        (P.firstColumnEliminationCoefficient i : ℚ_[p]) *
          P.normalizedMatrix 0 0 = 0 := by
  rw [P.normalizedMatrix_firstColumn i hi, P.normalizedMatrix_zero_zero]
  let r : ℤ_[p] :=
    P.integralRatioMatrix ((Equiv.swap 0 P.row) i) P.col
  let u : ℤ_[p]ˣ :=
    Padic.integralUnitPart p (A P.row P.col) P.ne_zero
  have hpivot :
      ((u : ℤ_[p]) : ℚ_[p]) *
          (p : ℚ_[p]) ^ (A P.row P.col).valuation =
        A P.row P.col :=
    Padic.integralUnitPart_mul_p_zpow p (A P.row P.col) P.ne_zero
  have hentry :
      ((r : ℤ_[p]) : ℚ_[p]) * A P.row P.col =
        A ((Equiv.swap 0 P.row) i) P.col :=
    P.coe_integralRatioMatrix_mul_pivot
      ((Equiv.swap 0 P.row) i) P.col
  change A ((Equiv.swap 0 P.row) i) P.col +
      ((-(r * (u : ℤ_[p])) : ℤ_[p]) : ℚ_[p]) *
        (p : ℚ_[p]) ^ (A P.row P.col).valuation = 0
  have hcoeff :
      ((-(r * (u : ℤ_[p])) : ℤ_[p]) : ℚ_[p]) =
        -((r : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p])) := by
    change PadicInt.Coe.ringHom (-(r * (u : ℤ_[p]))) =
      -(PadicInt.Coe.ringHom r * PadicInt.Coe.ringHom (u : ℤ_[p]))
    rw [map_neg, map_mul]
  rw [hcoeff]
  calc
    A ((Equiv.swap 0 P.row) i) P.col +
        (-((r : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]))) *
          (p : ℚ_[p]) ^ (A P.row P.col).valuation =
      A ((Equiv.swap 0 P.row) i) P.col -
        ((r : ℚ_[p]) *
          (((u : ℤ_[p]) : ℚ_[p]) *
            (p : ℚ_[p]) ^ (A P.row P.col).valuation)) := by ring
    _ = A ((Equiv.swap 0 P.row) i) P.col -
        ((r : ℚ_[p]) * A P.row P.col) := by rw [hpivot]
    _ = 0 := by rw [hentry, sub_self]

/-- The integral transvection that clears one selected first-column entry. -/
def firstColumnEliminationTransvection
    (P : PadicPivot p A) (i : Fin (d + 1)) (hi : i ≠ 0) :
    GL (Fin (d + 1)) ℤ_[p] :=
  let t : TransvectionStruct (Fin (d + 1)) ℤ_[p] :=
    { i := i
      j := 0
      hij := hi
      c := P.firstColumnEliminationCoefficient i }
  t.toGeneralLinearGroup

/-- Apply one integral row transvection to the normalized matrix. -/
def singleFirstColumnEntryEliminatedMatrix
    (P : PadicPivot p A) (i : Fin (d + 1)) (hi : i ≠ 0) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p] :=
  (GeneralLinearGroup.map PadicInt.Coe.ringHom
      (P.firstColumnEliminationTransvection i hi) :
        GL (Fin (d + 1)) ℚ_[p]) *
    P.normalizedMatrix

@[simp]
theorem singleFirstColumnEntryEliminatedMatrix_apply
    (P : PadicPivot p A) (i : Fin (d + 1)) (hi : i ≠ 0) :
    P.singleFirstColumnEntryEliminatedMatrix i hi i 0 = 0 := by
  rw [show P.singleFirstColumnEntryEliminatedMatrix i hi =
      Matrix.transvection i 0
          (P.firstColumnEliminationCoefficient i : ℚ_[p]) *
        P.normalizedMatrix by
    simp [singleFirstColumnEntryEliminatedMatrix,
      firstColumnEliminationTransvection,
      TransvectionStruct.toGeneralLinearGroup,
      TransvectionStruct.toMatrix]]
  rw [Matrix.transvection_mul_apply_same]
  exact P.normalizedMatrix_add_coefficient_mul_pivot i hi

@[simp]
theorem singleFirstColumnEntryEliminatedMatrix_zero_zero
    (P : PadicPivot p A) (i : Fin (d + 1)) (hi : i ≠ 0) :
    P.singleFirstColumnEntryEliminatedMatrix i hi 0 0 =
      (p : ℚ_[p]) ^ (A P.row P.col).valuation := by
  rw [show P.singleFirstColumnEntryEliminatedMatrix i hi =
      Matrix.transvection i 0
          (P.firstColumnEliminationCoefficient i : ℚ_[p]) *
        P.normalizedMatrix by
    simp [singleFirstColumnEntryEliminatedMatrix,
      firstColumnEliminationTransvection,
      TransvectionStruct.toGeneralLinearGroup,
      TransvectionStruct.toMatrix]]
  rw [Matrix.transvection_mul_apply_of_ne i 0 0 0 (Ne.symm hi)]
  exact P.normalizedMatrix_zero_zero

end Matrix.PadicPivot
