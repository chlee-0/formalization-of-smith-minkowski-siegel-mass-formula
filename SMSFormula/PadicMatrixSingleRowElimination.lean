import SMSFormula.PadicMatrixFirstColumnElimination

/-!
# One integral p-adic first-row elimination step

For a supplied nonzero-index column, one integral right transvection clears
that entry of the first-column-eliminated matrix. The operation preserves the
entire cleared first column and its normalized pivot.

No finite first-row transvection product, block extraction, dimension
induction, or matrix decomposition is constructed here.
-/

noncomputable section

open Matrix

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- The normalized first row is the pivot row after column permutation,
scaled by the inverse integral unit part of the pivot. -/
theorem normalizedMatrix_firstRow
    (P : PadicPivot p A) (j : Fin (d + 1)) :
    P.normalizedMatrix 0 j =
      (((Padic.integralUnitPart p (A P.row P.col) P.ne_zero)⁻¹ :
          ℤ_[p]ˣ) : ℤ_[p]) *
        A P.row ((Equiv.swap 0 P.col) j) := by
  simp only [normalizedMatrix, leftNormalization, pivotUnitScale, rowSwap,
    rightNormalization, colSwap, GeneralLinearGroup.coordinateUnit,
    Matrix.GeneralLinearGroup.map_mul,
    Matrix.GeneralLinearGroup.map_swap]
  change
    ((Matrix.diagonal (fun m : Fin (d + 1) =>
          if m = 0 then
            (((Padic.integralUnitPart p (A P.row P.col) P.ne_zero)⁻¹ :
                ℤ_[p]ˣ) : ℤ_[p])
          else 1) |>.map PadicInt.Coe.ringHom) *
        Matrix.swap ℚ_[p] 0 P.row * A *
        Matrix.swap ℚ_[p] 0 P.col) 0 j = _
  rw [Matrix.diagonal_map (map_zero _)]
  simp
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul]
  simp [Matrix.swap, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]

/-- The complete first-column operation leaves the normalized first row
unchanged. -/
theorem firstColumnEliminatedMatrix_zero_row
    (P : PadicPivot p A) (j : Fin (d + 1)) :
    P.firstColumnEliminatedMatrix 0 j = P.normalizedMatrix 0 j := by
  rw [P.firstColumnEliminatedMatrix_eq]
  have hzero :=
    P.firstColumnEliminationMatrices_mul_zero_row_drop
      (j := j) (k := 0) (Nat.zero_le d)
  simpa using hzero

/-- The integral coefficient clearing one nonzero-index first-row entry. -/
def firstRowEliminationCoefficient
    (P : PadicPivot p A) (j : Fin (d + 1)) : ℤ_[p] :=
  -P.integralRatioMatrix P.row ((Equiv.swap 0 P.col) j)

theorem firstColumnEliminatedMatrix_add_firstRowCoefficient_mul_pivot
    (P : PadicPivot p A) (j : Fin (d + 1)) :
    P.firstColumnEliminatedMatrix 0 j +
        (P.firstRowEliminationCoefficient j : ℚ_[p]) *
          P.firstColumnEliminatedMatrix 0 0 = 0 := by
  rw [P.firstColumnEliminatedMatrix_zero_row j,
    P.firstColumnEliminatedMatrix_zero_row 0,
    P.normalizedMatrix_firstRow j, P.normalizedMatrix_firstRow 0]
  simp only [Equiv.swap_apply_left]
  let r : ℤ_[p] :=
    P.integralRatioMatrix P.row ((Equiv.swap 0 P.col) j)
  let uinv : ℤ_[p] :=
    ((Padic.integralUnitPart p (A P.row P.col) P.ne_zero)⁻¹ :
      ℤ_[p]ˣ)
  have hentry :
      ((r : ℤ_[p]) : ℚ_[p]) * A P.row P.col =
        A P.row ((Equiv.swap 0 P.col) j) :=
    P.coe_integralRatioMatrix_mul_pivot
      P.row ((Equiv.swap 0 P.col) j)
  change
    (uinv : ℚ_[p]) * A P.row ((Equiv.swap 0 P.col) j) +
      ((-r : ℤ_[p]) : ℚ_[p]) *
        ((uinv : ℚ_[p]) * A P.row P.col) = 0
  have hneg : ((-r : ℤ_[p]) : ℚ_[p]) = -(r : ℚ_[p]) := by
    change PadicInt.Coe.ringHom (-r) = -PadicInt.Coe.ringHom r
    rw [map_neg]
  rw [hneg, ← hentry]
  ring

/-- The integral right transvection clearing one selected first-row entry. -/
def firstRowEliminationTransvection
    (P : PadicPivot p A) (j : Fin (d + 1)) (hj : j ≠ 0) :
    GL (Fin (d + 1)) ℤ_[p] :=
  let t : TransvectionStruct (Fin (d + 1)) ℤ_[p] :=
    { i := 0
      j := j
      hij := Ne.symm hj
      c := P.firstRowEliminationCoefficient j }
  t.toGeneralLinearGroup

/-- Apply one integral right transvection to the first-column-eliminated
matrix. -/
def singleFirstRowEntryEliminatedMatrix
    (P : PadicPivot p A) (j : Fin (d + 1)) (hj : j ≠ 0) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p] :=
  P.firstColumnEliminatedMatrix *
    (GeneralLinearGroup.map PadicInt.Coe.ringHom
      (P.firstRowEliminationTransvection j hj) :
        GL (Fin (d + 1)) ℚ_[p])

theorem singleFirstRowEntryEliminatedMatrix_eq
    (P : PadicPivot p A) (j : Fin (d + 1)) (hj : j ≠ 0) :
    P.singleFirstRowEntryEliminatedMatrix j hj =
      P.firstColumnEliminatedMatrix *
        Matrix.transvection 0 j
          (P.firstRowEliminationCoefficient j : ℚ_[p]) := by
  simp [singleFirstRowEntryEliminatedMatrix,
    firstRowEliminationTransvection,
    TransvectionStruct.toGeneralLinearGroup,
    TransvectionStruct.toMatrix]

@[simp]
theorem singleFirstRowEntryEliminatedMatrix_zero_apply
    (P : PadicPivot p A) (j : Fin (d + 1)) (hj : j ≠ 0) :
    P.singleFirstRowEntryEliminatedMatrix j hj 0 j = 0 := by
  rw [P.singleFirstRowEntryEliminatedMatrix_eq,
    Matrix.mul_transvection_apply_same]
  exact
    P.firstColumnEliminatedMatrix_add_firstRowCoefficient_mul_pivot j

theorem singleFirstRowEntryEliminatedMatrix_apply_zero
    (P : PadicPivot p A) (j : Fin (d + 1)) (hj : j ≠ 0)
    (i : Fin (d + 1)) :
    P.singleFirstRowEntryEliminatedMatrix j hj i 0 =
      P.firstColumnEliminatedMatrix i 0 := by
  rw [P.singleFirstRowEntryEliminatedMatrix_eq,
    Matrix.mul_transvection_apply_of_ne 0 j i 0 (Ne.symm hj)]

theorem singleFirstRowEntryEliminatedMatrix_apply_zero_of_ne
    (P : PadicPivot p A) (j : Fin (d + 1)) (hj : j ≠ 0)
    (i : Fin (d + 1)) (hi : i ≠ 0) :
    P.singleFirstRowEntryEliminatedMatrix j hj i 0 = 0 := by
  rw [P.singleFirstRowEntryEliminatedMatrix_apply_zero]
  exact P.firstColumnEliminatedMatrix_apply_zero_of_ne i hi

@[simp]
theorem singleFirstRowEntryEliminatedMatrix_zero_zero
    (P : PadicPivot p A) (j : Fin (d + 1)) (hj : j ≠ 0) :
    P.singleFirstRowEntryEliminatedMatrix j hj 0 0 =
      (p : ℚ_[p]) ^ (A P.row P.col).valuation := by
  rw [P.singleFirstRowEntryEliminatedMatrix_apply_zero]
  exact P.firstColumnEliminatedMatrix_zero_zero

end Matrix.PadicPivot
