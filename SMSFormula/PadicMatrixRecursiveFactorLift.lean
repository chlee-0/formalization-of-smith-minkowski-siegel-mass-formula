import SMSFormula.PadicMatrixLowerBlockUnit

/-!
# Recursive p-adic matrix factor lifts

A general-linear factor on the lower-right block lifts integrally to the
block-diagonal factor with identity on the distinguished first coordinate.
Scalar extension preserves this block form, and multiplication on either side
leaves the distinguished pivot block unchanged.

No dimension induction or full matrix decomposition is constructed here.
-/

noncomputable section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [DecidableEq n] [Fintype n]
  {R S : Type*} [CommRing R] [CommRing S]

/-- Embed a general-linear matrix as the lower-right block, fixing one
distinguished coordinate. -/
def inrBlock (U : GL n R) : GL (Unit ⊕ n) R where
  val := Matrix.fromBlocks 1 0 0 (U : Matrix n n R)
  inv := Matrix.fromBlocks 1 0 0 (↑(U⁻¹) : Matrix n n R)
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp

@[simp]
theorem coe_inrBlock (U : GL n R) :
    (inrBlock U : Matrix (Unit ⊕ n) (Unit ⊕ n) R) =
      Matrix.fromBlocks 1 0 0 (U : Matrix n n R) :=
  rfl

/-- The lower-right block lift remembers the supplied general-linear
factor. -/
theorem inrBlock_injective : Function.Injective (inrBlock : GL n R → GL (Unit ⊕ n) R) := by
  intro U V h
  apply Units.ext
  ext i j
  have hij := congrArg
    (fun W : GL (Unit ⊕ n) R =>
      (W : Matrix (Unit ⊕ n) (Unit ⊕ n) R) (Sum.inr i) (Sum.inr j)) h
  simpa [inrBlock, Matrix.fromBlocks] using hij

/-- Ring-homomorphism transport commutes with the lower-right block lift. -/
@[simp]
theorem map_inrBlock (f : R →+* S) (U : GL n R) :
    map f (inrBlock U) = inrBlock (map f U) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · cases i
    cases j
    simp [inrBlock, Matrix.fromBlocks]
  · cases i
    simp [inrBlock, Matrix.fromBlocks]
  · cases j
    simp [inrBlock, Matrix.fromBlocks]
  · simp [map_apply, inrBlock, Matrix.fromBlocks]

/-- The scalar extension of an integral lower-block lift has the expected
block-diagonal matrix. -/
theorem coe_map_inrBlock (f : R →+* S) (U : GL n R) :
    (map f (inrBlock U) : Matrix (Unit ⊕ n) (Unit ⊕ n) S) =
      Matrix.fromBlocks 1 0 0
        (map f U : Matrix n n S) := by
  rw [map_inrBlock, coe_inrBlock]

/-- Left multiplication by a lower-block lift preserves the upper-left
pivot block. -/
theorem coe_inrBlock_mul_fromBlocks
    (U : GL n R) (P : Matrix Unit Unit R) (D : Matrix n n R) :
    (inrBlock U : Matrix (Unit ⊕ n) (Unit ⊕ n) R) *
        Matrix.fromBlocks P 0 0 D =
      Matrix.fromBlocks P 0 0 ((U : Matrix n n R) * D) := by
  rw [coe_inrBlock, Matrix.fromBlocks_multiply]
  simp

/-- Right multiplication by a lower-block lift preserves the upper-left
pivot block. -/
theorem fromBlocks_mul_coe_inrBlock
    (U : GL n R) (P : Matrix Unit Unit R) (D : Matrix n n R) :
    Matrix.fromBlocks P 0 0 D *
        (inrBlock U : Matrix (Unit ⊕ n) (Unit ⊕ n) R) =
      Matrix.fromBlocks P 0 0 (D * (U : Matrix n n R)) := by
  rw [coe_inrBlock, Matrix.fromBlocks_multiply]
  simp

end Matrix.GeneralLinearGroup

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- An integral lower-block factor acts on the left of the extracted p-adic
block without changing its normalized pivot. -/
theorem map_inrBlock_mul_firstRowEliminatedReindexedMatrix
    (P : PadicPivot p A) (U : GL (Fin d) ℤ_[p]) :
    (GeneralLinearGroup.map PadicInt.Coe.ringHom
          (GeneralLinearGroup.inrBlock U) :
        Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℚ_[p]) *
        P.firstRowEliminatedReindexedMatrix =
      Matrix.fromBlocks P.firstRowEliminatedPivotBlock 0 0
        ((GeneralLinearGroup.map PadicInt.Coe.ringHom U :
            Matrix (Fin d) (Fin d) ℚ_[p]) *
          P.firstRowEliminatedLowerRightBlock) := by
  rw [P.firstRowEliminatedReindexedMatrix_eq_fromBlocks,
    GeneralLinearGroup.map_inrBlock,
    GeneralLinearGroup.coe_inrBlock_mul_fromBlocks]

/-- An integral lower-block factor acts on the right of the extracted p-adic
block without changing its normalized pivot. -/
theorem firstRowEliminatedReindexedMatrix_mul_map_inrBlock
    (P : PadicPivot p A) (U : GL (Fin d) ℤ_[p]) :
    P.firstRowEliminatedReindexedMatrix *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom
            (GeneralLinearGroup.inrBlock U) :
          Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℚ_[p]) =
      Matrix.fromBlocks P.firstRowEliminatedPivotBlock 0 0
        (P.firstRowEliminatedLowerRightBlock *
          (GeneralLinearGroup.map PadicInt.Coe.ringHom U :
            Matrix (Fin d) (Fin d) ℚ_[p])) := by
  rw [P.firstRowEliminatedReindexedMatrix_eq_fromBlocks,
    GeneralLinearGroup.map_inrBlock,
    GeneralLinearGroup.fromBlocks_mul_coe_inrBlock]

end Matrix.PadicPivot
