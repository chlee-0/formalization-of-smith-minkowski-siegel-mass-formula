import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# Gram-matrix reflections

This module contains the field-linear reflection algebra used both by the
finite-field counting layer and by the Hasse--Minkowski development.  It is a
separate module so that local-global arguments do not depend
on the product-formula module.
-/

noncomputable section

open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The scalar-valued quadratic function represented by a Gram matrix. -/
def gramQuadraticValue
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : K :=
  v ⬝ᵥ A *ᵥ v

/-- Reflection in `w` for the symmetric Gram matrix `A`. The formula is
`I - (2/Q_A(w)) w (Aw)ᵀ`. -/
def gramReflectionMatrix
    {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K)
    (w : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  1 - (2 / gramQuadraticValue A w) •
    Matrix.vecMulVec w (Matrix.mulVec A w)

private lemma vecMul_eq_mulVec_of_isSymm
    {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K)
    (hA : A.IsSymm) (w : Fin n → K) :
    Matrix.vecMul w A = Matrix.mulVec A w := by
  funext i
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  have hji : A j i = A i j := congrFun (congrFun hA i) j
  rw [hji]
  ring

private lemma gramRankOne_transpose_mul
    {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K)
    (hA : A.IsSymm) (w : Fin n → K) :
    Matrix.transpose (Matrix.vecMulVec w (Matrix.mulVec A w)) * A =
      Matrix.vecMulVec (Matrix.mulVec A w) (Matrix.mulVec A w) := by
  rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul,
    vecMul_eq_mulVec_of_isSymm A hA w]

private lemma gram_mul_gramRankOne
    {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K)
    (w : Fin n → K) :
    A * Matrix.vecMulVec w (Matrix.mulVec A w) =
      Matrix.vecMulVec (Matrix.mulVec A w) (Matrix.mulVec A w) := by
  rw [Matrix.mul_vecMulVec]

private lemma gramRankOne_quadruple
    {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K)
    (hA : A.IsSymm) (w : Fin n → K) :
    Matrix.transpose (Matrix.vecMulVec w (Matrix.mulVec A w)) * A *
        Matrix.vecMulVec w (Matrix.mulVec A w) =
      gramQuadraticValue A w •
        Matrix.vecMulVec (Matrix.mulVec A w) (Matrix.mulVec A w) := by
  rw [gramRankOne_transpose_mul A hA w,
    Matrix.vecMulVec_mul_vecMulVec]
  rw [dotProduct_comm]
  ext i j
  simp [gramQuadraticValue]

/-- A reflection in a vector of nonzero Gram norm preserves its symmetric
Gram matrix. -/
lemma gramReflectionMatrix_preserves
    {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K)
    (hA : A.IsSymm) (w : Fin n → K)
    (hw : gramQuadraticValue A w ≠ 0) :
    Matrix.transpose (gramReflectionMatrix A w) * A *
        gramReflectionMatrix A w = A := by
  let q := gramQuadraticValue A w
  let a := 2 / q
  let R := Matrix.vecMulVec w (Matrix.mulVec A w)
  let S := Matrix.vecMulVec (Matrix.mulVec A w) (Matrix.mulVec A w)
  have hRtA : Matrix.transpose R * A = S :=
    gramRankOne_transpose_mul A hA w
  have hAR : A * R = S := gram_mul_gramRankOne A w
  have hRtAR : Matrix.transpose R * A * R = q • S :=
    gramRankOne_quadruple A hA w
  change Matrix.transpose (1 - a • R) * A * (1 - a • R) = A
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul]
  simp only [sub_mul, mul_sub, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [hRtAR, hRtA, hAR]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  dsimp [a, q]
  field_simp [hw]
  ring

/-- The action of a Gram reflection on a vector. -/
lemma gramReflectionMatrix_mulVec
    {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K)
    (w x : Fin n → K) :
    Matrix.mulVec (gramReflectionMatrix A w) x =
      x - ((2 / gramQuadraticValue A w) *
        (Matrix.mulVec A w ⬝ᵥ x)) • w := by
  rw [gramReflectionMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  ring

/-- The bilinear pairing represented by a symmetric Gram matrix is
symmetric. -/
lemma gramBilinearValue_symm
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (hA : A.IsSymm)
    (x y : Fin n → K) :
    x ⬝ᵥ Matrix.mulVec A y = y ⬝ᵥ Matrix.mulVec A x := by
  rw [Matrix.dotProduct_mulVec]
  have hvec : Matrix.vecMul x A = Matrix.mulVec A x := by
    funext i
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    have hij : A j i = A i j := congrFun (congrFun hA i) j
    rw [hij]
    ring
  rw [hvec, dotProduct_comm]

lemma gramQuadraticValue_sub
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (hA : A.IsSymm)
    (x y : Fin n → K) :
    gramQuadraticValue A (x - y) =
      gramQuadraticValue A x + gramQuadraticValue A y -
        2 * (x ⬝ᵥ Matrix.mulVec A y) := by
  simp only [gramQuadraticValue, Matrix.mulVec_sub, dotProduct_sub,
    sub_dotProduct]
  rw [gramBilinearValue_symm A hA y x]
  ring

lemma gramQuadraticValue_add
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (hA : A.IsSymm)
    (x y : Fin n → K) :
    gramQuadraticValue A (x + y) =
      gramQuadraticValue A x + gramQuadraticValue A y +
        2 * (x ⬝ᵥ Matrix.mulVec A y) := by
  simp only [gramQuadraticValue, Matrix.mulVec_add, dotProduct_add,
    add_dotProduct]
  rw [gramBilinearValue_symm A hA y x]
  ring

/-- A Gram reflection is invertible when the ambient symmetric Gram matrix
is nonsingular. -/
lemma gramReflectionMatrix_det_ne_zero
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (hA : A.IsSymm)
    (hAdet : A.det ≠ 0) (w : Fin n → K)
    (hw : gramQuadraticValue A w ≠ 0) :
    (gramReflectionMatrix A w).det ≠ 0 := by
  have hpres := gramReflectionMatrix_preserves A hA w hw
  have hdet := congrArg Matrix.det hpres
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  intro hzero
  rw [hzero] at hdet
  simp at hdet
  exact hAdet hdet.symm

/-- A reflection in a vector of nonzero Gram norm has determinant `-1`. -/
lemma gramReflectionMatrix_det
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (w : Fin n → K)
    (hw : gramQuadraticValue A w ≠ 0) :
    (gramReflectionMatrix A w).det = -1 := by
  rw [gramReflectionMatrix, sub_eq_add_neg,
    show -((2 / gramQuadraticValue A w) •
        Matrix.vecMulVec w (A *ᵥ w)) =
        Matrix.vecMulVec
          (-(2 / gramQuadraticValue A w) • w)
          (A *ᵥ w) by
      ext a b
      simp [Matrix.vecMulVec_apply]
      ring]
  rw [Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [Pi.smul_apply, smul_eq_mul, dotProduct]
  have hsum :
      (∑ x, (A *ᵥ w) x *
        (-(2 / gramQuadraticValue A w) * w x)) =
      -(2 / gramQuadraticValue A w) *
        ∑ x, w x * (A *ᵥ w) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hsum]
  change 1 + -(2 / gramQuadraticValue A w) *
      gramQuadraticValue A w = -1
  field_simp [hw]
  ring

/-- Two vectors of the same nonzero value for a nonsingular symmetric Gram
matrix are related by a Gram isometry. This is the reflection step used in
the common-value induction for Hasse--Minkowski. -/
theorem exists_gramIsometry_mulVec_eq_of_same_nonzero_value
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (A : Matrix (Fin n) (Fin n) K) (hA : A.IsSymm)
    (hAdet : A.det ≠ 0) (x y : Fin n → K)
    (hxy : gramQuadraticValue A x = gramQuadraticValue A y)
    (hx : gramQuadraticValue A x ≠ 0) :
    ∃ T : GL (Fin n) K,
      T.1ᵀ * A * T.1 = A ∧ Matrix.mulVec T.1 x = y := by
  classical
  by_cases hsub : gramQuadraticValue A (x - y) = 0
  · have hadd : gramQuadraticValue A (x + y) ≠ 0 := by
      have hsub' := gramQuadraticValue_sub A hA x y
      rw [hxy, hsub] at hsub'
      have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
      have hb : x ⬝ᵥ Matrix.mulVec A y = gramQuadraticValue A y := by
        have hmul : 2 * (gramQuadraticValue A y -
            x ⬝ᵥ Matrix.mulVec A y) = 0 := by
          calc
            _ = gramQuadraticValue A y + gramQuadraticValue A y -
                2 * (x ⬝ᵥ Matrix.mulVec A y) := by ring
            _ = 0 := hsub'.symm
        exact (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left htwo)).symm
      rw [gramQuadraticValue_add A hA, ← hxy, hb]
      intro hzero
      have hfour : (4 : K) ≠ 0 := by
        have hfour_eq : (4 : K) = 2 * 2 := by norm_num
        rw [hfour_eq]
        exact mul_ne_zero htwo htwo
      apply hx
      have h4q : (4 : K) * gramQuadraticValue A x = 0 := by
        rw [← hxy] at hzero
        linear_combination (norm := ring_nf) hzero
      exact (mul_eq_zero.mp h4q).resolve_left hfour
    let Rmat := -gramReflectionMatrix A (x + y)
    have hRdet : Rmat.det ≠ 0 := by
      dsimp [Rmat]
      rw [Matrix.det_neg]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (gramReflectionMatrix_det_ne_zero A hA hAdet (x + y) hadd)
    let R : GL (Fin n) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero Rmat hRdet
    refine ⟨R, ?_, ?_⟩
    · change (-gramReflectionMatrix A (x + y))ᵀ * A *
          (-gramReflectionMatrix A (x + y)) = A
      simpa using gramReflectionMatrix_preserves A hA (x + y) hadd
    · change Matrix.mulVec (-gramReflectionMatrix A (x + y)) x = y
      rw [Matrix.neg_mulVec, gramReflectionMatrix_mulVec]
      have hdot : (Matrix.mulVec A (x + y)) ⬝ᵥ x =
          gramQuadraticValue A x + x ⬝ᵥ Matrix.mulVec A y := by
        rw [dotProduct_comm]
        simp [gramQuadraticValue, Matrix.mulVec_add, dotProduct_add]
      have hcoef : (2 / gramQuadraticValue A (x + y)) *
          ((Matrix.mulVec A (x + y)) ⬝ᵥ x) = 1 := by
        have hrel : gramQuadraticValue A (x + y) =
            2 * ((Matrix.mulVec A (x + y)) ⬝ᵥ x) := by
          rw [hdot, gramQuadraticValue_add A hA, hxy]
          ring
        field_simp [hadd]
        exact hrel.symm
      rw [hcoef]
      simp
  · let Rmat := gramReflectionMatrix A (x - y)
    let R : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Rmat
      (gramReflectionMatrix_det_ne_zero A hA hAdet (x - y) hsub)
    refine ⟨R, gramReflectionMatrix_preserves A hA (x - y) hsub, ?_⟩
    change Matrix.mulVec (gramReflectionMatrix A (x - y)) x = y
    rw [gramReflectionMatrix_mulVec]
    have hdot : (Matrix.mulVec A (x - y)) ⬝ᵥ x =
        gramQuadraticValue A x - x ⬝ᵥ Matrix.mulVec A y := by
      rw [dotProduct_comm]
      simp [gramQuadraticValue, Matrix.mulVec_sub, dotProduct_sub]
    have hcoef : (2 / gramQuadraticValue A (x - y)) *
        ((Matrix.mulVec A (x - y)) ⬝ᵥ x) = 1 := by
      have hrel : gramQuadraticValue A (x - y) =
          2 * ((Matrix.mulVec A (x - y)) ⬝ᵥ x) := by
        rw [hdot, gramQuadraticValue_sub A hA, hxy]
        ring
      field_simp [hsub]
      exact hrel.symm
    rw [hcoef]
    simp

end PositiveDefiniteIntegralLattice
