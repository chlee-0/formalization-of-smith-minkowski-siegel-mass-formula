import SMSFormula.FiniteOrthogonalGroupIdentityOrder

/-!
# Nonzero representation and prescribed-head splitting in arbitrary rank

Every nonsingular symmetric form of dimension at least two over an odd finite
field represents every nonzero scalar.  The proof diagonalizes the form, uses
only the first two diagonal coordinates and the completed binary
representation theorem, and transports the resulting vector back through the
actual congruence matrix.  The represented vector then supplies a literal
prescribed-head block splitting.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- A nonsingular symmetric form in dimension `n+2` over an odd finite field
represents every nonzero scalar. -/
theorem exists_vector_gramQuadraticValue_eq_of_rank_add_two
    {K : Type*} [Field K] [Fintype K]
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (c : K) (hc : c ≠ 0) :
    ∃ v : Fin (n + 2) → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  let B : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![d 0, d 1]
  have hB_symm : B.IsSymm := by simp [B]
  have hB_det : B.det ≠ 0 := by
    simp [B, Matrix.det_diagonal, Fin.prod_univ_two, hd]
  obtain ⟨z, hz⟩ :=
    exists_binaryVector_gramQuadraticValue_eq
      B hB_symm hB_det hchar c hc
  let w : Fin (n + 2) → K :=
    Fin.cons (z 0) (Fin.cons (z 1) (0 : Fin n → K))
  refine ⟨Matrix.mulVec (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K) w, ?_⟩
  rw [gramQuadraticValue_mulVec_of_congr A (Matrix.diagonal d) P hP]
  calc
    gramQuadraticValue (Matrix.diagonal d) w =
        gramQuadraticValue B z := by
      simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Matrix.diagonal,
        B, w, Fin.sum_univ_succ]
    _ = c := hz

/-- A nonsingular symmetric form in dimension `n+2` admits a prescribed-head
block splitting with any chosen nonzero head norm.  The represented vector and
the change-of-basis matrix are given explicitly. -/
theorem exists_gramMatrix_congr_finSuccBlock_of_rank_add_two
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
          finSuccGramBlock c C) := by
  obtain ⟨x, hx⟩ :=
    exists_vector_gramQuadraticValue_eq_of_rank_add_two
      A hA_symm hA_det hchar c hc
  obtain ⟨C, P, hC_symm, hC_det, hPhead, hP⟩ :=
    exists_gramMatrix_congr_finSuccBlock_with_head
      A hA_symm hA_det hchar x (hx.symm ▸ hc)
  refine ⟨x, C, P, hx, hC_symm, hC_det, hPhead, ?_⟩
  simpa only [hx] using hP

end PositiveDefiniteIntegralLattice
