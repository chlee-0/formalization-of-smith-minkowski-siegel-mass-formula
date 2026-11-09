import SMSFormula.PadicMatrixConditionalOriginalFactorization

/-!
# Successor p-adic signed diagonal

The normalized pivot exponent and the recursive lower-block exponents combine
into one exponent vector on `Fin (d + 1)`. The reindexed pivot-plus-lower
middle block is exactly the corresponding signed prime-power diagonal matrix.

No lower-block factorization or dimension induction is constructed.
-/

noncomputable section

open Matrix

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- Prepend the normalized pivot valuation to the recursive lower-block
exponents. -/
def successorSignedDiagonalExponents
    (P : PadicPivot p A) (z : Fin d → ℤ) :
    Fin (d + 1) → ℤ :=
  Fin.cases (A P.row P.col).valuation z

@[simp]
theorem successorSignedDiagonalExponents_zero
    (P : PadicPivot p A) (z : Fin d → ℤ) :
    P.successorSignedDiagonalExponents z 0 =
      (A P.row P.col).valuation :=
  rfl

@[simp]
theorem successorSignedDiagonalExponents_succ
    (P : PadicPivot p A) (z : Fin d → ℤ) (i : Fin d) :
    P.successorSignedDiagonalExponents z i.succ = z i :=
  rfl

/-- The original-index middle block is a single signed prime-power
diagonal matrix on the successor coordinate type. -/
theorem firstRowEliminatedOriginalIndexDiagonalBlock_eq
    (P : PadicPivot p A) (z : Fin d → ℤ) :
    P.firstRowEliminatedOriginalIndexDiagonalBlock z =
      padicSignedPrimePowerDiagonalMatrix p
        (P.successorSignedDiagonalExponents z) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · simp [firstRowEliminatedOriginalIndexDiagonalBlock,
      firstRowEliminatedPivotBlock,
      padicSignedPrimePowerDiagonalMatrix,
      successorSignedDiagonalExponents,
      Matrix.reindex, Matrix.fromBlocks]
  · have hzero : (0 : Fin (d + 1)) ≠ j.succ :=
      ne_of_lt (Fin.succ_pos j)
    simp [firstRowEliminatedOriginalIndexDiagonalBlock,
      padicSignedPrimePowerDiagonalMatrix,
      successorSignedDiagonalExponents,
      Matrix.reindex, Matrix.fromBlocks, hzero]
  all_goals
    simp [firstRowEliminatedOriginalIndexDiagonalBlock,
      padicSignedPrimePowerDiagonalMatrix,
      successorSignedDiagonalExponents,
      Matrix.reindex, Matrix.fromBlocks, Matrix.diagonal_apply]

end Matrix.PadicPivot
