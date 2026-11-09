import SMSFormula.PadicMatrixConditionalBlockFactorAssembly

/-!
# Reindexing recursive p-adic matrix factors

General-linear matrices transport along an equivalence of their finite index
types. This file specializes that transport to move a recursive lower-block
factor from `Unit ⊕ Fin d` back to the original `Fin (d + 1)` coordinates.

No original-index elimination factors or dimension induction are assembled.
-/

noncomputable section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {n m : Type*} [DecidableEq n] [Fintype n]
  [DecidableEq m] [Fintype m]
  {R S : Type*} [CommRing R] [CommRing S]

/-- Reindex general-linear matrices along an equivalence of finite index
types. -/
def reindex (e : n ≃ m) : GL n R ≃* GL m R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R e).toMulEquiv

@[simp]
theorem coe_reindex (e : n ≃ m) (U : GL n R) :
    (reindex e U : Matrix m m R) =
      Matrix.reindex e e (U : Matrix n n R) :=
  rfl

/-- Coefficient transport commutes with reindexing a general-linear
matrix. -/
theorem map_reindex (f : R →+* S) (e : n ≃ m) (U : GL n R) :
    map f (reindex e U) = reindex e (map f U) := by
  ext i j
  rfl

/-- The scalar extension of a reindexed integral factor is the reindexing of
its scalar extension. -/
theorem coe_map_reindex (f : R →+* S) (e : n ≃ m) (U : GL n R) :
    (map f (reindex e U) : Matrix m m S) =
      Matrix.reindex e e (map f U : Matrix n n S) := by
  rw [map_reindex, coe_reindex]

end Matrix.GeneralLinearGroup

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]

/-- After moving a recursive integral factor back to the original successor
coordinates and extending scalars, its matrix is the corresponding
reindexing. -/
theorem coe_map_reindex_finZeroSucc
    (W : GL (Unit ⊕ Fin d) ℤ_[p]) :
    (GeneralLinearGroup.map PadicInt.Coe.ringHom
          (GeneralLinearGroup.reindex (finZeroSuccEquiv d).symm W) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) =
      Matrix.reindex (finZeroSuccEquiv d).symm
        (finZeroSuccEquiv d).symm
        (GeneralLinearGroup.map PadicInt.Coe.ringHom W :
          Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℚ_[p]) :=
  GeneralLinearGroup.coe_map_reindex _ _ _

/-- In particular, a recursive lower-block lift becomes the
reindexed matrix `fromBlocks 1 0 0 U` in the original successor
coordinates. -/
theorem coe_map_reindex_finZeroSucc_inrBlock
    (U : GL (Fin d) ℤ_[p]) :
    (GeneralLinearGroup.map PadicInt.Coe.ringHom
          (GeneralLinearGroup.reindex (finZeroSuccEquiv d).symm
            (GeneralLinearGroup.inrBlock U)) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) =
      Matrix.reindex (finZeroSuccEquiv d).symm
        (finZeroSuccEquiv d).symm
        (Matrix.fromBlocks 1 0 0
          (GeneralLinearGroup.map PadicInt.Coe.ringHom U :
            Matrix (Fin d) (Fin d) ℚ_[p])) := by
  rw [GeneralLinearGroup.map_reindex, GeneralLinearGroup.coe_reindex,
    GeneralLinearGroup.map_inrBlock, GeneralLinearGroup.coe_inrBlock]

end Matrix.PadicPivot
