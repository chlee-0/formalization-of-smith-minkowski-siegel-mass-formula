import SMSFormula.FiniteOrthogonalGroupGeneralRepresentation

/-!
# Determinant-controlled prescribed-head splitting

The arbitrary-rank prescribed-head congruence is strengthened by retaining its
exact determinant identity.  No factor is cancelled.  At head norm one, the
tail determinant is exhibited as the original determinant times the literal
nonzero square of the change-of-basis determinant.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Taking determinants of a literal prescribed-head Gram congruence retains
the multiplication orientation on both sides. -/
lemma det_mul_det_mul_det_eq_of_congr_finSuccGramBlock
    {K : Type*} [Field K]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (C : Matrix (Fin n) (Fin n) K)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (c : K)
    (hP : Matrix.transpose P * A * P = finSuccGramBlock c C) :
    P.det * A.det * P.det = c * C.det := by
  have hdet := congrArg Matrix.det hP
  simpa only [Matrix.det_mul, Matrix.det_transpose, finSuccGramBlock_det]
    using hdet

/-- Square-oriented form of the prescribed-head determinant identity.  It is
obtained only by reassociation and commutation, without cancelling `c`. -/
lemma mul_det_eq_det_sq_mul_det_of_congr_finSuccGramBlock
    {K : Type*} [Field K]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (C : Matrix (Fin n) (Fin n) K)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (c : K)
    (hP : Matrix.transpose P * A * P = finSuccGramBlock c C) :
    c * C.det = P.det ^ 2 * A.det := by
  rw [← det_mul_det_mul_det_eq_of_congr_finSuccGramBlock A C P c hP]
  ring

/-- The general prescribed-head split, strengthened by its exact determinant
identity. -/
theorem exists_gramMatrix_congr_finSuccBlock_with_det_of_rank_add_two
    {K : Type*} [Field K] [Fintype K]
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (c : K) (hc : c ≠ 0) :
    ∃ (x : Fin (n + 2) → K)
        (C : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
        (P : Matrix.GeneralLinearGroup (Fin (n + 2)) K),
      gramQuadraticValue A x = c ∧ C.IsSymm ∧ C.det ≠ 0 ∧
        Matrix.mulVec (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
          finSuccHeadVector = x ∧
        (Matrix.transpose (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K) * A *
            (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K) =
          finSuccGramBlock c C) ∧
        (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K).det * A.det *
            (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K).det =
          c * C.det := by
  obtain ⟨x, C, P, hx, hC_symm, hC_det, hPhead, hP⟩ :=
    exists_gramMatrix_congr_finSuccBlock_of_rank_add_two
      A hA_symm hA_det hchar c hc
  refine ⟨x, C, P, hx, hC_symm, hC_det, hPhead, hP, ?_⟩
  exact det_mul_det_mul_det_eq_of_congr_finSuccGramBlock
    A C (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K) c hP

/-- At head norm one, the tail determinant is the original determinant times
the nonzero square of the change-of-basis determinant. -/
theorem exists_gramMatrix_congr_finSuccBlock_one_with_det_square_of_rank_add_two
    {K : Type*} [Field K] [Fintype K]
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (x : Fin (n + 2) → K)
        (C : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
        (P : Matrix.GeneralLinearGroup (Fin (n + 2)) K),
      gramQuadraticValue A x = 1 ∧ C.IsSymm ∧ C.det ≠ 0 ∧
        Matrix.mulVec (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
          finSuccHeadVector = x ∧
        (Matrix.transpose (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K) * A *
            (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K) =
          finSuccGramBlock 1 C) ∧
        (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K).det ≠ 0 ∧
        C.det =
          (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K).det ^ 2 * A.det := by
  obtain ⟨x, C, P, hx, hC_symm, hC_det, hPhead, hP, hdet⟩ :=
    exists_gramMatrix_congr_finSuccBlock_with_det_of_rank_add_two
      A hA_symm hA_det hchar 1 one_ne_zero
  let U : Matrix (Fin (n + 2)) (Fin (n + 2)) K := P
  have hUunit : IsUnit U := P.isUnit
  have hUdet : U.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det U).mp hUunit)
  have htail : C.det = U.det ^ 2 * A.det := by
    calc
      C.det = 1 * C.det := by simp
      _ = U.det * A.det * U.det := by simpa [U] using hdet.symm
      _ = U.det ^ 2 * A.det := by ring
  exact ⟨x, C, P, hx, hC_symm, hC_det, hPhead, hP, hUdet, htail⟩

end PositiveDefiniteIntegralLattice
