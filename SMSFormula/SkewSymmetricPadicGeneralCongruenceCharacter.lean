import SMSFormula.SkewSymmetricPadicTransvectionCharacter

/-!
# The general p-adic skew-symmetric congruence determinant character

Mathlib's invertible diagonal--transvection induction extends the
diagonal and transvection computations to every element of `GL_n(Q_p)`.
Consequently, the determinant of congruence on skew-symmetric matrices is the
`(n - 1)`st power of the usual matrix determinant.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The congruence determinant character equals the expected
determinant-power character when the scalar field does not have
characteristic two. -/
theorem skewSymmetricPadicCongruenceDetCharacter_eq_expected_of_ringChar_ne_two
    (hchar : ringChar ℚ_[p] ≠ 2) (W : GL (Fin n) ℚ_[p]) :
    skewSymmetricPadicCongruenceDetCharacter p W =
      skewSymmetricPadicExpectedCongruenceDetCharacter p n W := by
  let P : Matrix (Fin n) (Fin n) ℚ_[p] → Prop :=
    fun M => ∀ hM : Matrix.det M ≠ 0,
      skewSymmetricPadicCongruenceDetCharacter p
          (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM) =
        skewSymmetricPadicExpectedCongruenceDetCharacter p n
          (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)
  have hWdet :
      Matrix.det (W : Matrix (Fin n) (Fin n) ℚ_[p]) ≠ 0 := by
    change
      ((Matrix.GeneralLinearGroup.det W : ℚ_[p]ˣ) : ℚ_[p]) ≠ 0
    exact Units.ne_zero _
  have hP : P (W : Matrix (Fin n) (Fin n) ℚ_[p]) := by
    apply Matrix.diagonal_transvection_induction_of_det_ne_zero
      P (W : Matrix (Fin n) (Fin n) ℚ_[p]) hWdet
    · intro D hDdet
      dsimp only [P]
      intro hD
      have hDi : ∀ i, D i ≠ 0 := by
        rw [Matrix.det_diagonal] at hDdet
        intro i hi
        exact hDdet (Finset.prod_eq_zero (Finset.mem_univ i) hi)
      let d : Fin n → ℚ_[p]ˣ :=
        fun i => Units.mk0 (D i) (hDi i)
      have hmk :
          Matrix.GeneralLinearGroup.mkOfDetNeZero
              (Matrix.diagonal D) hD =
            skewSymmetricPadicDiagonalGeneralLinear p n d := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
          coe_skewSymmetricPadicDiagonalGeneralLinear]
        simp [d]
      rw [hmk]
      exact skewSymmetricPadicCongruenceDetCharacter_diagonal_eq_expected
        p n hchar d
    · intro t
      dsimp only [P]
      intro ht
      have hmk :
          Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix ht =
            t.toGeneralLinearGroup := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
          Matrix.TransvectionStruct.coe_toGeneralLinearGroup]
      rw [hmk,
        skewSymmetricPadicCongruenceDetCharacter_transvection p n t,
        skewSymmetricPadicExpectedCongruenceDetCharacter_transvection p n t]
    · intro A B hA hB hPA hPB
      dsimp only [P] at hPA hPB ⊢
      intro hAB
      have hmk :
          Matrix.GeneralLinearGroup.mkOfDetNeZero (A * B) hAB =
            Matrix.GeneralLinearGroup.mkOfDetNeZero A hA *
              Matrix.GeneralLinearGroup.mkOfDetNeZero B hB := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
          Matrix.GeneralLinearGroup.coe_mul,
          Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
          Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      rw [hmk, map_mul, map_mul, hPA hA, hPB hB]
  dsimp only [P] at hP
  have hmkW :
      Matrix.GeneralLinearGroup.mkOfDetNeZero
          (W : Matrix (Fin n) (Fin n) ℚ_[p]) hWdet =
        W := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  rw [← hmkW]
  exact hP hWdet

/-- The congruence determinant character equals the expected
determinant-power character on every p-adic general-linear element. -/
theorem skewSymmetricPadicCongruenceDetCharacter_eq_expected
    (W : GL (Fin n) ℚ_[p]) :
    skewSymmetricPadicCongruenceDetCharacter p W =
      skewSymmetricPadicExpectedCongruenceDetCharacter p n W := by
  apply
    skewSymmetricPadicCongruenceDetCharacter_eq_expected_of_ringChar_ne_two
      p n
  rw [ringChar.eq_zero]
  norm_num

/-- The underlying scalar of the congruence determinant character is
the `(n - 1)`st power of the usual matrix determinant. -/
theorem det_skewSymmetricPadicCongruenceEndomorphism_eq_det_pow
    (W : GL (Fin n) ℚ_[p]) :
    LinearMap.det
        (skewSymmetricPadicCongruenceEndomorphism
          p (W : Matrix (Fin n) (Fin n) ℚ_[p])).toLinearMap =
      Matrix.det (W : Matrix (Fin n) (Fin n) ℚ_[p]) ^ (n - 1) := by
  rw [← coe_skewSymmetricPadicCongruenceDetCharacter_apply]
  rw [skewSymmetricPadicCongruenceDetCharacter_eq_expected p n W]
  exact coe_skewSymmetricPadicExpectedCongruenceDetCharacter_apply p n W

end Matrix
