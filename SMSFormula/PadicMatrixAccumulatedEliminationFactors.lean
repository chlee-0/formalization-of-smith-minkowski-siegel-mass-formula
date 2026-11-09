import SMSFormula.PadicMatrixConditionalProductReindex

/-!
# Accumulated p-adic matrix elimination factors

The pivot-normalization, first-column elimination, and first-row
elimination factors are combined into one integral factor on each side of the
original matrix. Their scalar extensions give the completely eliminated
matrix.

No recursive diagonal product is substituted and no dimension induction is
performed.
-/

noncomputable section

open Matrix

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- The total integral left factor: normalize the pivot, then clear its
column. -/
def accumulatedLeftEliminationFactor
    (P : PadicPivot p A) : GL (Fin (d + 1)) ℤ_[p] :=
  P.firstColumnEliminationFactor * P.leftNormalization

/-- The total integral right factor: normalize the pivot column, then clear
the pivot row. -/
def accumulatedRightEliminationFactor
    (P : PadicPivot p A) : GL (Fin (d + 1)) ℤ_[p] :=
  P.rightNormalization * P.firstRowEliminationFactor

/-- The completely first-row/first-column-eliminated matrix is obtained from
the original matrix by the scalar extensions of the accumulated integral
factors. -/
theorem firstRowEliminatedMatrix_eq_map_accumulated_mul
    (P : PadicPivot p A) :
    P.firstRowEliminatedMatrix =
      (GeneralLinearGroup.map PadicInt.Coe.ringHom
            P.accumulatedLeftEliminationFactor :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
        A *
      (GeneralLinearGroup.map PadicInt.Coe.ringHom
            P.accumulatedRightEliminationFactor :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) := by
  rw [firstRowEliminatedMatrix, firstColumnEliminatedMatrix,
    normalizedMatrix, accumulatedLeftEliminationFactor,
    accumulatedRightEliminationFactor,
    GeneralLinearGroup.map_mul, GeneralLinearGroup.map_mul]
  simp only [GeneralLinearGroup.coe_mul, Matrix.mul_assoc]

end Matrix.PadicPivot
