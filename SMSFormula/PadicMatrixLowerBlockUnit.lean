import SMSFormula.PadicMatrixBlockExtraction

/-!
# Invertibility of the first p-adic lower block

If the original square `Q_p` matrix is a unit, all integral normalization and
transvection factors preserve that property. The extracted block-diagonal
identity then forces the lower-right block to have nonzero
determinant and hence to be a matrix unit.
-/

noncomputable section

open Matrix

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- Integral normalization and elimination factors preserve matrix-unit
status after extension to `Q_p`. -/
theorem firstRowEliminatedMatrix_isUnit
    (P : PadicPivot p A) (hA : IsUnit A) :
    IsUnit P.firstRowEliminatedMatrix := by
  rw [firstRowEliminatedMatrix, firstColumnEliminatedMatrix,
    normalizedMatrix]
  apply IsUnit.mul
  · apply IsUnit.mul
    · exact Units.isUnit _
    · apply IsUnit.mul
      · apply IsUnit.mul
        · exact Units.isUnit _
        · exact hA
      · exact Units.isUnit _
  · exact Units.isUnit _

/-- The determinant of the lower-right block is nonzero whenever
the original matrix is a unit. -/
theorem firstRowEliminatedLowerRightBlock_det_ne_zero
    (P : PadicPivot p A) (hA : IsUnit A) :
    P.firstRowEliminatedLowerRightBlock.det ≠ 0 := by
  have hdetFull : P.firstRowEliminatedMatrix.det ≠ 0 :=
    isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (P.firstRowEliminatedMatrix_isUnit hA))
  have hdetReindexed : P.firstRowEliminatedReindexedMatrix.det ≠ 0 := by
    rw [firstRowEliminatedReindexedMatrix, Matrix.det_reindex_self]
    exact hdetFull
  rw [P.firstRowEliminatedReindexedMatrix_eq_fromBlocks,
    Matrix.det_fromBlocks_zero₂₁] at hdetReindexed
  intro hlower
  apply hdetReindexed
  rw [hlower, mul_zero]

/-- The lower-right block is a matrix unit whenever the original
matrix is a unit. -/
theorem firstRowEliminatedLowerRightBlock_isUnit
    (P : PadicPivot p A) (hA : IsUnit A) :
    IsUnit P.firstRowEliminatedLowerRightBlock :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr
      (P.firstRowEliminatedLowerRightBlock_det_ne_zero hA))

end Matrix.PadicPivot
