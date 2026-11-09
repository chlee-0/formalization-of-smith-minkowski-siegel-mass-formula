import SMSFormula.PadicMatrixRecursiveFactorReindex

/-!
# Reindexing the conditional p-adic block product

The conditional recursive block factorization is transported from
`Unit ⊕ Fin d` back to the original `Fin (d + 1)` coordinates. The resulting
outer factors are scalar extensions of integral general-linear matrices.

No pivot-normalization or elimination factors are combined here, and no
lower-dimensional factorization or dimension induction is constructed.
-/

noncomputable section

open Matrix

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- The pivot-plus-signed-diagonal middle block, transported back to the
original successor coordinates. -/
def firstRowEliminatedOriginalIndexDiagonalBlock
    (P : PadicPivot p A) (z : Fin d → ℤ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p] :=
  Matrix.reindex (finZeroSuccEquiv d).symm
    (finZeroSuccEquiv d).symm
    (Matrix.fromBlocks P.firstRowEliminatedPivotBlock 0 0
      (padicSignedPrimePowerDiagonalMatrix p z))

/-- Inverse reindexing recovers the completely first-row/first-column
eliminated matrix. -/
theorem reindex_firstRowEliminatedReindexedMatrix
    (P : PadicPivot p A) :
    Matrix.reindex (finZeroSuccEquiv d).symm
        (finZeroSuccEquiv d).symm
        P.firstRowEliminatedReindexedMatrix =
      P.firstRowEliminatedMatrix := by
  change
    (Matrix.reindex (finZeroSuccEquiv d) (finZeroSuccEquiv d)).symm
        (Matrix.reindex (finZeroSuccEquiv d) (finZeroSuccEquiv d)
          P.firstRowEliminatedMatrix) =
      P.firstRowEliminatedMatrix
  exact Equiv.symm_apply_apply _ _

/-- A supplied lower integral--diagonal--integral factorization gives the
exact product for the eliminated matrix in its original `Fin (d + 1)`
coordinates. -/
theorem firstRowEliminatedMatrix_eq_integralDiagonalIntegral_of_lower
    (P : PadicPivot p A) (U V : GL (Fin d) ℤ_[p]) (z : Fin d → ℤ)
    (hLower :
      P.firstRowEliminatedLowerRightBlock =
        (GeneralLinearGroup.map PadicInt.Coe.ringHom U :
            Matrix (Fin d) (Fin d) ℚ_[p]) *
          padicSignedPrimePowerDiagonalMatrix p z *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom V :
            Matrix (Fin d) (Fin d) ℚ_[p])) :
    P.firstRowEliminatedMatrix =
      (GeneralLinearGroup.map PadicInt.Coe.ringHom
            (GeneralLinearGroup.reindex (finZeroSuccEquiv d).symm
              (GeneralLinearGroup.inrBlock U)) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
        P.firstRowEliminatedOriginalIndexDiagonalBlock z *
      (GeneralLinearGroup.map PadicInt.Coe.ringHom
            (GeneralLinearGroup.reindex (finZeroSuccEquiv d).symm
              (GeneralLinearGroup.inrBlock V)) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) := by
  let e := finZeroSuccEquiv d
  let L : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℚ_[p] :=
    GeneralLinearGroup.map PadicInt.Coe.ringHom
      (GeneralLinearGroup.inrBlock U)
  let D : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℚ_[p] :=
    Matrix.fromBlocks P.firstRowEliminatedPivotBlock 0 0
      (padicSignedPrimePowerDiagonalMatrix p z)
  let R : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℚ_[p] :=
    GeneralLinearGroup.map PadicInt.Coe.ringHom
      (GeneralLinearGroup.inrBlock V)
  have hBlock : P.firstRowEliminatedReindexedMatrix = L * D * R := by
    exact
      P.firstRowEliminatedReindexedMatrix_eq_integralDiagonalIntegralBlocks
        U V z hLower
  calc
    P.firstRowEliminatedMatrix =
        Matrix.reindex e.symm e.symm
          P.firstRowEliminatedReindexedMatrix :=
      P.reindex_firstRowEliminatedReindexedMatrix.symm
    _ = Matrix.reindex e.symm e.symm (L * D * R) :=
      congrArg (Matrix.reindex e.symm e.symm) hBlock
    _ = Matrix.reindex e.symm e.symm L *
          Matrix.reindex e.symm e.symm D *
        Matrix.reindex e.symm e.symm R := by
      change Matrix.reindexAlgEquiv ℚ_[p] ℚ_[p] e.symm (L * D * R) = _
      rw [map_mul, map_mul]
      simp only [Matrix.reindexAlgEquiv_apply]
    _ =
        (GeneralLinearGroup.map PadicInt.Coe.ringHom
              (GeneralLinearGroup.reindex e.symm
                (GeneralLinearGroup.inrBlock U)) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
          P.firstRowEliminatedOriginalIndexDiagonalBlock z *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom
              (GeneralLinearGroup.reindex e.symm
                (GeneralLinearGroup.inrBlock V)) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) := by
      simp only [e, L, D, R, firstRowEliminatedOriginalIndexDiagonalBlock]
      rw [← coe_map_reindex_finZeroSucc
          (p := p) (GeneralLinearGroup.inrBlock U),
        ← coe_map_reindex_finZeroSucc
          (p := p) (GeneralLinearGroup.inrBlock V)]

end Matrix.PadicPivot
