import SMSFormula.PadicMatrixRecursiveFactorLift

/-!
# Conditional p-adic block-factor assembly

Given a supplied integral--diagonal--integral factorization of the extracted
lower-right block, the recursive lifts assemble it around the one-by-one
normalized pivot block. This is only the algebraic successor step: no
lower-dimensional factorization is constructed and no dimension induction
is performed.
-/

noncomputable section

open Matrix

namespace Matrix

/-- The diagonal `Q_p` matrix with signed prime-power entries. -/
def padicSignedPrimePowerDiagonalMatrix
    (p : ℕ) [Fact p.Prime] (z : Fin d → ℤ) :
    Matrix (Fin d) (Fin d) ℚ_[p] :=
  Matrix.diagonal fun i => (p : ℚ_[p]) ^ z i

namespace GeneralLinearGroup

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

/-- Lower-block lifts assemble around an arbitrary middle block while leaving
the distinguished upper-left block unchanged. -/
theorem coe_inrBlock_mul_fromBlocks_mul_coe_inrBlock
    (U V : GL n R) (P : Matrix Unit Unit R) (D : Matrix n n R) :
    (inrBlock U : Matrix (Unit ⊕ n) (Unit ⊕ n) R) *
          Matrix.fromBlocks P 0 0 D *
        (inrBlock V : Matrix (Unit ⊕ n) (Unit ⊕ n) R) =
      Matrix.fromBlocks P 0 0
        ((U : Matrix n n R) * D * (V : Matrix n n R)) := by
  rw [coe_inrBlock_mul_fromBlocks, fromBlocks_mul_coe_inrBlock]

end GeneralLinearGroup

namespace PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- A supplied integral--diagonal--integral factorization of the extracted
lower block assembles to the exact full pivot-block product. -/
theorem firstRowEliminatedReindexedMatrix_eq_integralDiagonalIntegralBlocks
    (P : PadicPivot p A) (U V : GL (Fin d) ℤ_[p]) (z : Fin d → ℤ)
    (hLower :
      P.firstRowEliminatedLowerRightBlock =
        (GeneralLinearGroup.map PadicInt.Coe.ringHom U :
            Matrix (Fin d) (Fin d) ℚ_[p]) *
          padicSignedPrimePowerDiagonalMatrix p z *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom V :
            Matrix (Fin d) (Fin d) ℚ_[p])) :
    P.firstRowEliminatedReindexedMatrix =
      (GeneralLinearGroup.map PadicInt.Coe.ringHom
            (GeneralLinearGroup.inrBlock U) :
          Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℚ_[p]) *
        Matrix.fromBlocks P.firstRowEliminatedPivotBlock 0 0
          (padicSignedPrimePowerDiagonalMatrix p z) *
      (GeneralLinearGroup.map PadicInt.Coe.ringHom
            (GeneralLinearGroup.inrBlock V) :
          Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℚ_[p]) := by
  rw [P.firstRowEliminatedReindexedMatrix_eq_fromBlocks, hLower,
    GeneralLinearGroup.map_inrBlock, GeneralLinearGroup.map_inrBlock]
  exact
    (GeneralLinearGroup.coe_inrBlock_mul_fromBlocks_mul_coe_inrBlock
      (GeneralLinearGroup.map PadicInt.Coe.ringHom U)
      (GeneralLinearGroup.map PadicInt.Coe.ringHom V)
      P.firstRowEliminatedPivotBlock
      (padicSignedPrimePowerDiagonalMatrix p z)).symm

end PadicPivot

end Matrix
