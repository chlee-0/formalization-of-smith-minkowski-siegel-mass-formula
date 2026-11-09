import SMSFormula.FiniteOrthogonalGroupTailWeightedClassification

/-!
# Moving the final finite-field weight from tail to head

The cyclic coordinate equivalence sends the final coordinate to zero and all
earlier coordinates to their successors.  This module constructs its
permutation matrix together with the inverse matrix, and proves that congruence by
that matrix is exactly simultaneous matrix reindexing.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Cyclically move the final coordinate of `Fin (n+1)` to the head. -/
def tailToHeadEquiv (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := Fin.lastCases 0 (fun i => i.succ)
  invFun := Fin.cases (Fin.last n) (fun i => i.castSucc)
  left_inv i := by
    cases i using Fin.lastCases <;> simp
  right_inv i := by
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- The recursive tail-weighted model is the diagonal with the tail
coefficient at the final coordinate. -/
lemma tailWeightedIdentityGramMatrix_eq_diagonal_last
    {K : Type*} [Field K] (n : ℕ) (d : K) :
    tailWeightedIdentityGramMatrix n d =
      Matrix.diagonal (fun i => if i = Fin.last n then d else 1) := by
  induction n with
  | zero =>
      ext i j
      fin_cases i
      fin_cases j
      simp [tailWeightedIdentityGramMatrix, Matrix.diagonal]
  | succ n ih =>
      change finSuccGramBlock 1 (tailWeightedIdentityGramMatrix n d) = _
      rw [ih]
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;>
        refine Fin.cases ?_ (fun j => ?_) j
      · simp [finSuccGramBlock, Matrix.diagonal]
      · have hne : (0 : Fin (n + 2)) ≠ j.succ := by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
        simp [finSuccGramBlock, Matrix.diagonal, hne]
      · simp [finSuccGramBlock, Matrix.diagonal]
      · simp [finSuccGramBlock, Matrix.diagonal]

/-- Reindexing by the tail-to-head cycle gives the existing head-weighted
identity Gram matrix literally. -/
lemma reindex_tailWeightedIdentityGramMatrix_tailToHeadEquiv
    {K : Type*} [Field K] (n : ℕ) (d : K) :
    Matrix.reindex (tailToHeadEquiv n) (tailToHeadEquiv n)
        (tailWeightedIdentityGramMatrix n d) =
      finSuccIdentityGramMatrix (n := n) d := by
  rw [tailWeightedIdentityGramMatrix_eq_diagonal_last]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp [Matrix.reindex, tailToHeadEquiv,
    finSuccIdentityGramMatrix, finSuccGramBlock, Matrix.diagonal,
    Matrix.one_apply, eq_comm]

/-- The permutation matrix whose `j`th column is the standard basis vector at
`e.symm j`. -/
def equivPermutationMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (e : ι ≃ ι) : Matrix ι ι K :=
  fun i j => if i = e.symm j then 1 else 0

@[simp] lemma equivPermutationMatrix_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (e : ι ≃ ι) :
    Matrix.transpose (equivPermutationMatrix (K := K) e) =
      equivPermutationMatrix e.symm := by
  ext i j
  change (if j = e.symm i then 1 else 0) =
    if i = e j then 1 else 0
  by_cases h : i = e j
  · have h' : j = e.symm i := by rw [h]; simp
    rw [if_pos h, if_pos h']
  · have h' : j ≠ e.symm i := by
      intro hij
      apply h
      rw [hij]
      simp
    rw [if_neg h, if_neg h']

@[simp] lemma equivPermutationMatrix_mul_symm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (e : ι ≃ ι) :
    equivPermutationMatrix (K := K) e * equivPermutationMatrix e.symm = 1 := by
  ext i j
  simp [equivPermutationMatrix, Matrix.mul_apply, Matrix.one_apply]

@[simp] lemma equivPermutationMatrix_symm_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (e : ι ≃ ι) :
    equivPermutationMatrix (K := K) e.symm * equivPermutationMatrix e = 1 := by
  simpa using equivPermutationMatrix_mul_symm (K := K) e.symm

/-- The general-linear permutation matrix, together with its inverse matrix. -/
def equivPermutationGeneralLinear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (e : ι ≃ ι) :
    Matrix.GeneralLinearGroup ι K :=
  ⟨equivPermutationMatrix e, equivPermutationMatrix e.symm,
    equivPermutationMatrix_mul_symm e,
    equivPermutationMatrix_symm_mul e⟩

@[simp] lemma equivPermutationGeneralLinear_coe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (e : ι ≃ ι) :
    (equivPermutationGeneralLinear (K := K) e : Matrix ι ι K) =
      equivPermutationMatrix e := rfl

@[simp] lemma equivPermutationMatrix_mul_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (e : ι ≃ ι) (A : Matrix ι ι K) (i j : ι) :
    (equivPermutationMatrix (K := K) e * A) i j = A (e i) j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (e i)]
  · simp [equivPermutationMatrix]
  · intro b hb
    have hne : i ≠ e.symm b := by
      intro h
      apply hb
      simpa using (congrArg e h).symm
    simp [equivPermutationMatrix, hne]

@[simp] lemma mul_equivPermutationMatrix_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (A : Matrix ι ι K) (e : ι ≃ ι) (i j : ι) :
    (A * equivPermutationMatrix (K := K) e) i j = A i (e.symm j) := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (e.symm j)]
  · simp [equivPermutationMatrix]
  · intro b hb
    simp [equivPermutationMatrix, hb]

/-- Congruence by the permutation matrix is exactly simultaneous reindexing. -/
lemma equivPermutationMatrix_transpose_mul_mul_eq_reindex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (e : ι ≃ ι) (A : Matrix ι ι K) :
    Matrix.transpose (equivPermutationMatrix e) * A *
        equivPermutationMatrix e =
      Matrix.reindex e e A := by
  ext i j
  rw [mul_equivPermutationMatrix_apply,
    equivPermutationMatrix_transpose,
    equivPermutationMatrix_mul_apply]
  rfl

/-- The tail coefficient is moved to the head by an explicit
general-linear permutation congruence. -/
lemma tailWeightedIdentityGramMatrix_congr_finSuccIdentityGramMatrix
    {K : Type*} [Field K] (n : ℕ) (d : K) :
    Matrix.transpose
          (equivPermutationGeneralLinear (K := K) (tailToHeadEquiv n) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        tailWeightedIdentityGramMatrix n d *
          (equivPermutationGeneralLinear (K := K) (tailToHeadEquiv n) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      finSuccIdentityGramMatrix (n := n) d := by
  rw [equivPermutationGeneralLinear_coe,
    equivPermutationMatrix_transpose_mul_mul_eq_reindex,
    reindex_tailWeightedIdentityGramMatrix_tailToHeadEquiv]

end PositiveDefiniteIntegralLattice
