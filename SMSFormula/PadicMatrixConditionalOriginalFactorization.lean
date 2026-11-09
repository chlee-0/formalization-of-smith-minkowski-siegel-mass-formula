import SMSFormula.PadicMatrixAccumulatedEliminationFactors

/-!
# Conditional p-adic factorization of the original matrix

A supplied integral--diagonal--integral factorization of the recursive lower
block gives an exact factorization of the original matrix. The accumulated
normalization and elimination factors are cancelled inside the integral
general-linear group.

The lower-block factorization is a hypothesis. No dimension induction or
full Cartan decomposition is constructed.
-/

noncomputable section

open Matrix

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- The conditional integral left factor for the original matrix. -/
def conditionalOriginalLeftFactor
    (P : PadicPivot p A) (U : GL (Fin d) ℤ_[p]) :
    GL (Fin (d + 1)) ℤ_[p] :=
  P.accumulatedLeftEliminationFactor⁻¹ *
    GeneralLinearGroup.reindex (finZeroSuccEquiv d).symm
      (GeneralLinearGroup.inrBlock U)

/-- The conditional integral right factor for the original matrix. -/
def conditionalOriginalRightFactor
    (P : PadicPivot p A) (V : GL (Fin d) ℤ_[p]) :
    GL (Fin (d + 1)) ℤ_[p] :=
  GeneralLinearGroup.reindex (finZeroSuccEquiv d).symm
      (GeneralLinearGroup.inrBlock V) *
    P.accumulatedRightEliminationFactor⁻¹

/-- A supplied factorization of the recursive lower block yields the exact
integral--diagonal--integral factorization of the original matrix. -/
theorem matrix_eq_integralDiagonalIntegral_of_lower
    (P : PadicPivot p A) (U V : GL (Fin d) ℤ_[p]) (z : Fin d → ℤ)
    (hLower :
      P.firstRowEliminatedLowerRightBlock =
        (GeneralLinearGroup.map PadicInt.Coe.ringHom U :
            Matrix (Fin d) (Fin d) ℚ_[p]) *
          padicSignedPrimePowerDiagonalMatrix p z *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom V :
            Matrix (Fin d) (Fin d) ℚ_[p])) :
    A =
      (GeneralLinearGroup.map PadicInt.Coe.ringHom
            (P.conditionalOriginalLeftFactor U) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
        P.firstRowEliminatedOriginalIndexDiagonalBlock z *
      (GeneralLinearGroup.map PadicInt.Coe.ringHom
            (P.conditionalOriginalRightFactor V) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) := by
  let L₀ := P.accumulatedLeftEliminationFactor
  let R₀ := P.accumulatedRightEliminationFactor
  let L₁ :=
    GeneralLinearGroup.reindex (finZeroSuccEquiv d).symm
      (GeneralLinearGroup.inrBlock U)
  let R₁ :=
    GeneralLinearGroup.reindex (finZeroSuccEquiv d).symm
      (GeneralLinearGroup.inrBlock V)
  let D := P.firstRowEliminatedOriginalIndexDiagonalBlock z
  have hEq :
      (GeneralLinearGroup.map PadicInt.Coe.ringHom L₀ :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
          A *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom R₀ :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) =
      (GeneralLinearGroup.map PadicInt.Coe.ringHom L₁ :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
          D *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom R₁ :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) := by
    exact
      P.firstRowEliminatedMatrix_eq_map_accumulated_mul.symm.trans
        (P.firstRowEliminatedMatrix_eq_integralDiagonalIntegral_of_lower
          U V z hLower)
  have hLeftCancel :
      (GeneralLinearGroup.map PadicInt.Coe.ringHom L₀⁻¹ :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom L₀ :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) = 1 := by
    rw [← GeneralLinearGroup.coe_mul]
    simp
  have hRightCancel :
      (GeneralLinearGroup.map PadicInt.Coe.ringHom R₀ :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom R₀⁻¹ :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) = 1 := by
    rw [← GeneralLinearGroup.coe_mul]
    simp
  calc
    A =
        (GeneralLinearGroup.map PadicInt.Coe.ringHom L₀⁻¹ :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
          ((GeneralLinearGroup.map PadicInt.Coe.ringHom L₀ :
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
            A *
          (GeneralLinearGroup.map PadicInt.Coe.ringHom R₀ :
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p])) *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom R₀⁻¹ :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) := by
      symm
      calc
        (GeneralLinearGroup.map PadicInt.Coe.ringHom L₀⁻¹ :
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
            ((GeneralLinearGroup.map PadicInt.Coe.ringHom L₀ :
                Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
              A *
            (GeneralLinearGroup.map PadicInt.Coe.ringHom R₀ :
                Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p])) *
          (GeneralLinearGroup.map PadicInt.Coe.ringHom R₀⁻¹ :
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) =
            ((GeneralLinearGroup.map PadicInt.Coe.ringHom L₀⁻¹ :
                Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
              (GeneralLinearGroup.map PadicInt.Coe.ringHom L₀ :
                Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p])) *
              A *
            ((GeneralLinearGroup.map PadicInt.Coe.ringHom R₀ :
                Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
              (GeneralLinearGroup.map PadicInt.Coe.ringHom R₀⁻¹ :
                Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p])) := by
          noncomm_ring
        _ = A := by rw [hLeftCancel, hRightCancel, one_mul, mul_one]
    _ =
        (GeneralLinearGroup.map PadicInt.Coe.ringHom L₀⁻¹ :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
          ((GeneralLinearGroup.map PadicInt.Coe.ringHom L₁ :
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
            D *
          (GeneralLinearGroup.map PadicInt.Coe.ringHom R₁ :
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p])) *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom R₀⁻¹ :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) :=
      congrArg
        (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p] =>
          (GeneralLinearGroup.map PadicInt.Coe.ringHom L₀⁻¹ :
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
            M *
          (GeneralLinearGroup.map PadicInt.Coe.ringHom R₀⁻¹ :
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]))
        hEq
    _ =
        (GeneralLinearGroup.map PadicInt.Coe.ringHom (L₀⁻¹ * L₁) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
          D *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom (R₁ * R₀⁻¹) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) := by
      rw [GeneralLinearGroup.map_mul, GeneralLinearGroup.map_mul]
      simp only [GeneralLinearGroup.coe_mul, Matrix.mul_assoc]
    _ =
        (GeneralLinearGroup.map PadicInt.Coe.ringHom
              (P.conditionalOriginalLeftFactor U) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) *
          P.firstRowEliminatedOriginalIndexDiagonalBlock z *
        (GeneralLinearGroup.map PadicInt.Coe.ringHom
              (P.conditionalOriginalRightFactor V) :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) := by
      rfl

end Matrix.PadicPivot
