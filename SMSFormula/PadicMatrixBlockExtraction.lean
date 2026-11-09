import SMSFormula.PadicMatrixFirstRowElimination

/-!
# First p-adic matrix block extraction

After the first column and first row have been cleared, reindexing
`Fin (d + 1)` as `Unit ⊕ Fin d` identifies the transformed matrix with a
block diagonal matrix. Its upper-left block is the normalized signed
prime-power pivot and its lower-right block holds the remaining entries.
-/

noncomputable section

open Matrix

namespace Matrix

/-- Split `Fin (d + 1)` into its zero coordinate and its successor
coordinates. -/
def finZeroSuccEquiv (d : ℕ) : Fin (d + 1) ≃ Unit ⊕ Fin d where
  toFun := Fin.cases (Sum.inl ()) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv i := by
    rcases i with i | i
    · cases i
      rfl
    · rfl

@[simp]
theorem finZeroSuccEquiv_zero (d : ℕ) :
    finZeroSuccEquiv d 0 = Sum.inl () :=
  rfl

@[simp]
theorem finZeroSuccEquiv_succ (i : Fin d) :
    finZeroSuccEquiv d i.succ = Sum.inr i :=
  rfl

@[simp]
theorem finZeroSuccEquiv_symm_inl (i : Unit) :
    (finZeroSuccEquiv d).symm (Sum.inl i) = 0 := by
  cases i
  rfl

@[simp]
theorem finZeroSuccEquiv_symm_inr (i : Fin d) :
    (finZeroSuccEquiv d).symm (Sum.inr i) = i.succ :=
  rfl

namespace PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- The completely first-row/first-column-eliminated matrix, reindexed by
the first coordinate and the remaining coordinates. -/
def firstRowEliminatedReindexedMatrix
    (P : PadicPivot p A) :
    Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℚ_[p] :=
  Matrix.reindex (finZeroSuccEquiv d) (finZeroSuccEquiv d)
    P.firstRowEliminatedMatrix

/-- The normalized one-by-one pivot block. -/
def firstRowEliminatedPivotBlock
    (P : PadicPivot p A) : Matrix Unit Unit ℚ_[p] :=
  fun _ _ => (p : ℚ_[p]) ^ (A P.row P.col).valuation

/-- The lower-right block remaining after first-row and first-column
elimination. -/
def firstRowEliminatedLowerRightBlock
    (P : PadicPivot p A) : Matrix (Fin d) (Fin d) ℚ_[p] :=
  fun i j => P.firstRowEliminatedMatrix i.succ j.succ

/-- Reindexing the completely cleared first row and column gives the exact
block diagonal matrix with the normalized pivot and the remaining lower-right
block. -/
theorem firstRowEliminatedReindexedMatrix_eq_fromBlocks
    (P : PadicPivot p A) :
    P.firstRowEliminatedReindexedMatrix =
      Matrix.fromBlocks P.firstRowEliminatedPivotBlock 0 0
        P.firstRowEliminatedLowerRightBlock := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · cases i
    cases j
    simp [firstRowEliminatedReindexedMatrix,
      firstRowEliminatedPivotBlock, Matrix.reindex]
  · cases i
    simp [firstRowEliminatedReindexedMatrix, Matrix.reindex,
      P.firstRowEliminatedMatrix_zero_apply_succ]
  · cases j
    simp [firstRowEliminatedReindexedMatrix, Matrix.reindex,
      P.firstRowEliminatedMatrix_apply_zero_of_ne]
  · rfl

end PadicPivot

end Matrix
