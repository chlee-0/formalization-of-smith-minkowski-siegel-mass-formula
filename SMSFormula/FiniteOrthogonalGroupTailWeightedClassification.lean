import SMSFormula.FiniteOrthogonalGroupTailWeightedIdentity

/-!
# Classification by a tail-weighted identity model

Every nonsingular symmetric form of positive dimension over an odd finite
field is explicitly congruent to a Gram matrix with leading unit entries and
one final weight.  The proof starts from the one-dimensional
identity congruence and iterates the completed unit-head split.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The literal rank-one base of the tail-weighted classification. -/
lemma exists_congr_tailWeightedIdentityGramMatrix_rank_one
    {K : Type*} [Field K]
    (A : Matrix (Fin 1) (Fin 1) K) (hA_det : A.det ≠ 0) :
    ∃ (d : K) (P : Matrix.GeneralLinearGroup (Fin 1) K),
      d ≠ 0 ∧
        Matrix.transpose (P : Matrix (Fin 1) (Fin 1) K) * A *
            (P : Matrix (Fin 1) (Fin 1) K) =
          tailWeightedIdentityGramMatrix 0 d := by
  refine ⟨A.det, (1 : Matrix.GeneralLinearGroup (Fin 1) K), hA_det, ?_⟩
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one,
    one_mul, mul_one]
  ext i j
  fin_cases i
  fin_cases j
  simp [tailWeightedIdentityGramMatrix]

/-- Every nonsingular symmetric positive-dimensional Gram matrix over an odd
finite field is explicitly congruent to a tail-weighted identity model. -/
theorem exists_congr_tailWeightedIdentityGramMatrix
    {K : Type*} [Field K] [Fintype K]
    (n : ℕ) (hchar : ringChar K ≠ 2)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0) :
    ∃ (d : K) (P : Matrix.GeneralLinearGroup (Fin (n + 1)) K),
      d ≠ 0 ∧
        Matrix.transpose
            (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K) * A *
              (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
          tailWeightedIdentityGramMatrix n d := by
  induction n with
  | zero =>
      exact exists_congr_tailWeightedIdentityGramMatrix_rank_one A hA_det
  | succ n ih =>
      obtain ⟨x, C, P, hx, hC_symm, hC_det, hPhead, hP,
          hPdet, hCdet⟩ :=
        exists_gramMatrix_congr_finSuccBlock_one_with_det_square_of_rank_add_two
          A hA_symm hA_det hchar
      obtain ⟨d, Q, hd, hQ⟩ := ih C hC_symm hC_det
      refine ⟨d, P * finSuccGeneralLinearBlock Q, hd, ?_⟩
      exact congr_tailWeightedIdentityGramMatrix_succ A C P Q d hP hQ

/-- The final weight differs from the original determinant by the
nonzero square of the same change-of-basis determinant. -/
theorem exists_congr_tailWeightedIdentityGramMatrix_with_det_square
    {K : Type*} [Field K] [Fintype K]
    (n : ℕ) (hchar : ringChar K ≠ 2)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0) :
    ∃ (d s : K) (P : Matrix.GeneralLinearGroup (Fin (n + 1)) K),
      d ≠ 0 ∧ s ≠ 0 ∧
        Matrix.transpose
            (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K) * A *
              (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
          tailWeightedIdentityGramMatrix n d ∧
        d = s ^ 2 * A.det := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_congr_tailWeightedIdentityGramMatrix n hchar A hA_symm hA_det
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) K := P
  have hUunit : IsUnit U := P.isUnit
  have hUdet : U.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det U).mp hUunit)
  have hdet := congrArg Matrix.det hP
  have hdet' : U.det * A.det * U.det = d := by
    simpa only [Matrix.det_mul, Matrix.det_transpose,
      tailWeightedIdentityGramMatrix_det] using hdet
  have hd_square : d = U.det ^ 2 * A.det := by
    rw [← hdet']
    ring
  exact ⟨d, U.det, P, hd, hUdet, hP, hd_square⟩

end PositiveDefiniteIntegralLattice
