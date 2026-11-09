import SMSFormula.FiniteOrthogonalGroupDeterminantControlledHeadSplit

/-!
# Tail-weighted identity Gram matrices

This module defines the recursive standard model with leading unit entries
and one final weight.  It also proves that a prescribed-head Gram
congruence composes with a lower-dimensional congruence to this model through
the block extension of the lower change of basis.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The diagonal Gram matrix with `n` leading unit entries and final entry
`d`.  The recursive definition makes adjoining another leading unit block
literal. -/
def tailWeightedIdentityGramMatrix {K : Type*} [Field K] :
    (n : ℕ) → K → Matrix (Fin (n + 1)) (Fin (n + 1)) K
  | 0, d => Matrix.diagonal (fun _ : Fin 1 => d)
  | n + 1, d => finSuccGramBlock 1 (tailWeightedIdentityGramMatrix n d)

@[simp] lemma tailWeightedIdentityGramMatrix_zero
    {K : Type*} [Field K] (d : K) :
    tailWeightedIdentityGramMatrix 0 d =
      Matrix.diagonal (fun _ : Fin 1 => d) := rfl

/-- Adjoining a leading unit block advances the recursive standard model. -/
@[simp] lemma finSuccGramBlock_tailWeightedIdentityGramMatrix
    {K : Type*} [Field K] (n : ℕ) (d : K) :
    finSuccGramBlock 1 (tailWeightedIdentityGramMatrix n d) =
      tailWeightedIdentityGramMatrix (n + 1) d := rfl

/-- The tail-weighted identity Gram matrix is symmetric. -/
lemma tailWeightedIdentityGramMatrix_isSymm
    {K : Type*} [Field K] (n : ℕ) (d : K) :
    (tailWeightedIdentityGramMatrix n d).IsSymm := by
  induction n with
  | zero => simp [tailWeightedIdentityGramMatrix]
  | succ n ih =>
      exact finSuccGramBlock_isSymm 1
        (tailWeightedIdentityGramMatrix n d) ih

/-- The tail weight is exactly the determinant of the recursive standard
model. -/
@[simp] lemma tailWeightedIdentityGramMatrix_det
    {K : Type*} [Field K] (n : ℕ) (d : K) :
    (tailWeightedIdentityGramMatrix n d).det = d := by
  induction n with
  | zero => simp [tailWeightedIdentityGramMatrix]
  | succ n ih =>
      change (finSuccGramBlock 1
        (tailWeightedIdentityGramMatrix n d)).det = d
      rw [finSuccGramBlock_det, ih]
      simp

/-- A prescribed-head congruence composes with a congruence of its tail by
extending the lower change of basis as a literal general-linear block. -/
lemma congr_tailWeightedIdentityGramMatrix_succ
    {K : Type*} [Field K]
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (P : Matrix.GeneralLinearGroup (Fin (n + 2)) K)
    (Q : Matrix.GeneralLinearGroup (Fin (n + 1)) K)
    (d : K)
    (hP : Matrix.transpose
          (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K) * A *
          (P : Matrix (Fin (n + 2)) (Fin (n + 2)) K) =
        finSuccGramBlock 1 C)
    (hQ : Matrix.transpose
          (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) K) * C *
          (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        tailWeightedIdentityGramMatrix n d) :
    Matrix.transpose
          ((P * finSuccGeneralLinearBlock Q :
              Matrix.GeneralLinearGroup (Fin (n + 2)) K) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) K) * A *
        ((P * finSuccGeneralLinearBlock Q :
              Matrix.GeneralLinearGroup (Fin (n + 2)) K) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) K) =
      tailWeightedIdentityGramMatrix (n + 1) d := by
  let R : Matrix.GeneralLinearGroup (Fin (n + 2)) K :=
    finSuccGeneralLinearBlock Q
  let X : Matrix (Fin (n + 2)) (Fin (n + 2)) K := P
  let Y : Matrix (Fin (n + 2)) (Fin (n + 2)) K := R
  change Matrix.transpose (X * Y) * A * (X * Y) = _
  rw [Matrix.transpose_mul]
  calc
    (Matrix.transpose Y * Matrix.transpose X) * A * (X * Y) =
        Matrix.transpose Y * (Matrix.transpose X * A * X) * Y := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.transpose Y * finSuccGramBlock 1 C * Y := by
          rw [hP]
    _ = finSuccGramBlock 1
        (Matrix.transpose
            (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) K) * C *
          (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) := by
          change Matrix.transpose
                (finSuccMatrixBlock
                  (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) *
              finSuccGramBlock 1 C *
                finSuccMatrixBlock
                  (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = _
          exact finSuccMatrixBlock_congr 1 C
            (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    _ = finSuccGramBlock 1 (tailWeightedIdentityGramMatrix n d) := by
          rw [hQ]
    _ = tailWeightedIdentityGramMatrix (n + 1) d := by
          rfl

end PositiveDefiniteIntegralLattice
