import SMSFormula.QuadraticReflection
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Orthogonal complements in Gram coordinates

This module packages the coordinate decomposition of a nonsingular symmetric
Gram space along a vector of nonzero value.  It is shared by the finite-field
counting layer and the common-value induction for Hasse--Minkowski.
-/

noncomputable section

open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A Gram congruence transports represented quadratic values by the
corresponding change of coordinates. -/
lemma gramQuadraticValue_mulVec_of_congr
    {K : Type*} [Field K]
    (A B : Matrix (Fin n) (Fin n) K)
    (P : Matrix.GeneralLinearGroup (Fin n) K)
    (hP : (↑P : Matrix (Fin n) (Fin n) K)ᵀ * A *
      (↑P : Matrix (Fin n) (Fin n) K) = B)
    (v : Fin n → K) :
    gramQuadraticValue A ((↑P : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      gramQuadraticValue B v := by
  let U : Matrix (Fin n) (Fin n) K := P
  change (U *ᵥ v) ⬝ᵥ A *ᵥ (U *ᵥ v) = v ⬝ᵥ B *ᵥ v
  calc
    (U *ᵥ v) ⬝ᵥ A *ᵥ (U *ᵥ v) = ((U *ᵥ v) ᵥ* A) ⬝ᵥ (U *ᵥ v) :=
      Matrix.dotProduct_mulVec _ _ _
    _ = (v ᵥ* (Uᵀ * A)) ⬝ᵥ (U *ᵥ v) := by rw [Matrix.vecMul_mulVec]
    _ = ((v ᵥ* (Uᵀ * A)) ᵥ* U) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
    _ = (v ᵥ* (Uᵀ * A * U)) ⬝ᵥ v := by rw [Matrix.vecMul_vecMul]
    _ = (v ᵥ* B) ⬝ᵥ v := by rw [hP]
    _ = v ⬝ᵥ B *ᵥ v := (Matrix.dotProduct_mulVec _ _ _).symm

/-- Adjoin a leading one-dimensional Gram block of weight `c` to `B`. -/
def finSuccGramBlock
    {K : Type*} [Field K]
    (c : K) (B : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => Fin.cases (Fin.cases c (fun _ => 0) j)
    (fun i => Fin.cases 0 (fun j => B i j) j) i

/-- The block diagonal Gram matrix `diag(A, -B)`, reindexed from
`Fin m ⊕ Fin n` to `Fin (m + n)`. -/
def differenceGramBlock
    {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (B : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (m + n)) (Fin (m + n)) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (-B))

/-- Join vectors on the two sides of a generic difference Gram block. -/
def differenceGramVector
    {K : Type*} {m n : ℕ} (u : Fin m → K) (v : Fin n → K) :
    Fin (m + n) → K :=
  fun i ↦ Sum.elim u v (finSumFinEquiv.symm i)

@[simp] theorem differenceGramVector_castAdd
    {K : Type*} {m n : ℕ} (u : Fin m → K) (v : Fin n → K) (i : Fin m) :
    differenceGramVector u v (Fin.castAdd n i) = u i := by
  simp [differenceGramVector]

@[simp] theorem differenceGramVector_natAdd
    {K : Type*} {m n : ℕ} (u : Fin m → K) (v : Fin n → K) (i : Fin n) :
    differenceGramVector u v (Fin.natAdd m i) = v i := by
  simp [differenceGramVector]

/-- Splitting a vector at `m` and joining the two pieces recovers it. -/
theorem differenceGramVector_split
    {K : Type*} {m n : ℕ} (x : Fin (m + n) → K) :
    differenceGramVector (fun i ↦ x (Fin.castAdd n i))
      (fun i ↦ x (Fin.natAdd m i)) = x := by
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp

/-- The quadratic value of a generic difference block is the difference of
the values on its two coordinate blocks. -/
theorem gramQuadraticValue_differenceGramBlock
    {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (B : Matrix (Fin n) (Fin n) K)
    (x : Fin (m + n) → K) :
    gramQuadraticValue (differenceGramBlock A B) x =
      gramQuadraticValue A (fun i ↦ x (Fin.castAdd n i)) -
        gramQuadraticValue B (fun i ↦ x (Fin.natAdd m i)) := by
  simp [differenceGramBlock, gramQuadraticValue, Matrix.mulVec, dotProduct,
    ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  ring

/-- Scalar extension commutes with forming a generic difference block. -/
@[simp] theorem differenceGramBlock_map
    {K L : Type*} [Field K] [Field L] {m n : ℕ} (f : K →+* L)
    (A : Matrix (Fin m) (Fin m) K) (B : Matrix (Fin n) (Fin n) K) :
    (differenceGramBlock A B).map f =
      differenceGramBlock (A.map f) (B.map f) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [differenceGramBlock]

/-- A generic difference block of diagonal matrices is diagonal, with the
second coefficient vector negated. -/
theorem differenceGramBlock_diagonal
    {K : Type*} [Field K] {m n : ℕ} (a : Fin m → K) (b : Fin n → K) :
    differenceGramBlock (Matrix.diagonal a) (Matrix.diagonal b) =
      Matrix.diagonal (differenceGramVector a (-b)) := by
  have hcross (i : Fin m) (j : Fin n) :
      Fin.castAdd n i ≠ Fin.natAdd m j := by
    intro h
    have : (Sum.inl i : Fin m ⊕ Fin n) = Sum.inr j :=
      finSumFinEquiv.injective h
    contradiction
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [differenceGramBlock, differenceGramVector, Matrix.diagonal]
      | inr j =>
          simp [differenceGramBlock, differenceGramVector, Matrix.diagonal,
            hcross i j]
  | inr i =>
      cases j with
      | inl j =>
          simp [differenceGramBlock, differenceGramVector, Matrix.diagonal,
            (hcross j i).symm]
      | inr j =>
          by_cases hij : i = j <;>
            simp [differenceGramBlock, differenceGramVector, Matrix.diagonal,
              hij]

/-- Splitting one coefficient vector into a leading block and a negated
trailing block reconstructs its diagonal matrix. -/
theorem differenceGramBlock_diagonal_split
    {K : Type*} [Field K] {m n : ℕ} (d : Fin (m + n) → K) :
    differenceGramBlock
        (Matrix.diagonal (fun i ↦ d (Fin.castAdd n i)))
        (Matrix.diagonal (fun i ↦ -d (Fin.natAdd m i))) =
      Matrix.diagonal d := by
  rw [differenceGramBlock_diagonal]
  apply congrArg Matrix.diagonal
  have htail : (-(fun i : Fin n ↦ -d (Fin.natAdd m i))) =
      fun i ↦ d (Fin.natAdd m i) := by
    funext i
    simp
  rw [htail, differenceGramVector_split]

/-- The block diagonal Gram matrix whose quadratic value is the difference
of the values of two binary forms. -/
def binaryPairDifferenceGramBlock
    {K : Type*} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  differenceGramBlock A B

/-- The block diagonal Gram matrix whose quadratic value is the difference of
a binary and a ternary quadratic value. -/
def binaryTernaryDifferenceGramBlock
    {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 5) (Fin 5) K :=
  differenceGramBlock A B

/-- The block diagonal Gram matrix whose quadratic value is the difference of
two ternary quadratic values. -/
def ternaryPairDifferenceGramBlock
    {K : Type*} [Field K]
    (A B : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 6) (Fin 6) K :=
  differenceGramBlock A B

/-- The block diagonal Gram matrix whose quadratic value is the difference of
a ternary and a quaternary quadratic value. -/
def ternaryQuaternaryDifferenceGramBlock
    {K : Type*} [Field K]
    (A : Matrix (Fin 3) (Fin 3) K) (B : Matrix (Fin 4) (Fin 4) K) :
    Matrix (Fin 7) (Fin 7) K :=
  differenceGramBlock A B

/-- The block diagonal Gram matrix whose quadratic value is the difference of
two quaternary quadratic values. -/
def quaternaryPairDifferenceGramBlock
    {K : Type*} [Field K]
    (A B : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 8) (Fin 8) K :=
  differenceGramBlock A B

/-- The block diagonal Gram matrix whose quadratic value is the difference of
a quaternary and a quinary quadratic value. -/
def quaternaryQuinaryDifferenceGramBlock
    {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (B : Matrix (Fin 5) (Fin 5) K) :
    Matrix (Fin 9) (Fin 9) K :=
  differenceGramBlock A B

/-- The block diagonal Gram matrix whose quadratic value is the difference of
two quinary quadratic values. -/
def quinaryPairDifferenceGramBlock
    {K : Type*} [Field K]
    (A B : Matrix (Fin 5) (Fin 5) K) : Matrix (Fin 10) (Fin 10) K :=
  differenceGramBlock A B

/-- The quadratic value of the binary-pair difference block is the difference
of the two binary quadratic values. -/
theorem gramQuadraticValue_binaryPairDifferenceGramBlock
    {K : Type*} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (x : Fin 4 → K) :
    gramQuadraticValue (binaryPairDifferenceGramBlock A B) x =
      gramQuadraticValue A ![x 0, x 1] -
        gramQuadraticValue B ![x 2, x 3] := by
  change gramQuadraticValue (differenceGramBlock A B) x = _
  rw [gramQuadraticValue_differenceGramBlock]
  congr 1

/-- The binary-versus-ternary difference block represents the difference of
the values represented by its two coordinate blocks. -/
theorem gramQuadraticValue_binaryTernaryDifferenceGramBlock
    {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 3) (Fin 3) K)
    (x : Fin 5 → K) :
    gramQuadraticValue (binaryTernaryDifferenceGramBlock A B) x =
      gramQuadraticValue A ![x 0, x 1] -
        gramQuadraticValue B ![x 2, x 3, x 4] := by
  change gramQuadraticValue (differenceGramBlock A B) x = _
  rw [gramQuadraticValue_differenceGramBlock]
  congr 1

/-- The ternary-pair difference block represents the difference of the two
ternary quadratic values. -/
theorem gramQuadraticValue_ternaryPairDifferenceGramBlock
    {K : Type*} [Field K]
    (A B : Matrix (Fin 3) (Fin 3) K) (x : Fin 6 → K) :
    gramQuadraticValue (ternaryPairDifferenceGramBlock A B) x =
      gramQuadraticValue A ![x 0, x 1, x 2] -
        gramQuadraticValue B ![x 3, x 4, x 5] := by
  change gramQuadraticValue (differenceGramBlock A B) x = _
  rw [gramQuadraticValue_differenceGramBlock]
  congr 1

/-- The ternary-versus-quaternary difference block represents the difference
of the values represented by its two coordinate blocks. -/
theorem gramQuadraticValue_ternaryQuaternaryDifferenceGramBlock
    {K : Type*} [Field K]
    (A : Matrix (Fin 3) (Fin 3) K) (B : Matrix (Fin 4) (Fin 4) K)
    (x : Fin 7 → K) :
    gramQuadraticValue (ternaryQuaternaryDifferenceGramBlock A B) x =
      gramQuadraticValue A ![x 0, x 1, x 2] -
        gramQuadraticValue B ![x 3, x 4, x 5, x 6] := by
  change gramQuadraticValue (differenceGramBlock A B) x = _
  rw [gramQuadraticValue_differenceGramBlock]
  congr 1

/-- The quaternary-pair difference block represents the difference of the two
quaternary quadratic values. -/
theorem gramQuadraticValue_quaternaryPairDifferenceGramBlock
    {K : Type*} [Field K]
    (A B : Matrix (Fin 4) (Fin 4) K) (x : Fin 8 → K) :
    gramQuadraticValue (quaternaryPairDifferenceGramBlock A B) x =
      gramQuadraticValue A ![x 0, x 1, x 2, x 3] -
        gramQuadraticValue B ![x 4, x 5, x 6, x 7] := by
  change gramQuadraticValue (differenceGramBlock A B) x = _
  rw [gramQuadraticValue_differenceGramBlock]
  congr 1

/-- The quaternary-versus-quinary difference block represents the difference
of the values represented by its two coordinate blocks. -/
theorem gramQuadraticValue_quaternaryQuinaryDifferenceGramBlock
    {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (B : Matrix (Fin 5) (Fin 5) K)
    (x : Fin 9 → K) :
    gramQuadraticValue (quaternaryQuinaryDifferenceGramBlock A B) x =
      gramQuadraticValue A ![x 0, x 1, x 2, x 3] -
        gramQuadraticValue B ![x 4, x 5, x 6, x 7, x 8] := by
  change gramQuadraticValue (differenceGramBlock A B) x = _
  rw [gramQuadraticValue_differenceGramBlock]
  congr 1

/-- The quinary-pair difference block represents the difference of the two
quinary quadratic values. -/
theorem gramQuadraticValue_quinaryPairDifferenceGramBlock
    {K : Type*} [Field K]
    (A B : Matrix (Fin 5) (Fin 5) K) (x : Fin 10 → K) :
    gramQuadraticValue (quinaryPairDifferenceGramBlock A B) x =
      gramQuadraticValue A ![x 0, x 1, x 2, x 3, x 4] -
        gramQuadraticValue B ![x 5, x 6, x 7, x 8, x 9] := by
  change gramQuadraticValue (differenceGramBlock A B) x = _
  rw [gramQuadraticValue_differenceGramBlock]
  congr 1

/-- Scalar extension commutes with forming a binary-pair difference block. -/
@[simp] theorem binaryPairDifferenceGramBlock_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (A B : Matrix (Fin 2) (Fin 2) K) :
    (binaryPairDifferenceGramBlock A B).map f =
      binaryPairDifferenceGramBlock (A.map f) (B.map f) := by
  simpa [binaryPairDifferenceGramBlock] using differenceGramBlock_map f A B

/-- Scalar extension commutes with forming a binary-versus-ternary difference
block. -/
@[simp] theorem binaryTernaryDifferenceGramBlock_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (A : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 3) (Fin 3) K) :
    (binaryTernaryDifferenceGramBlock A B).map f =
      binaryTernaryDifferenceGramBlock (A.map f) (B.map f) := by
  simpa [binaryTernaryDifferenceGramBlock] using differenceGramBlock_map f A B

/-- Scalar extension commutes with forming a ternary-pair difference block. -/
@[simp] theorem ternaryPairDifferenceGramBlock_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (A B : Matrix (Fin 3) (Fin 3) K) :
    (ternaryPairDifferenceGramBlock A B).map f =
      ternaryPairDifferenceGramBlock (A.map f) (B.map f) := by
  simpa [ternaryPairDifferenceGramBlock] using differenceGramBlock_map f A B

/-- Scalar extension commutes with forming a ternary-versus-quaternary
difference block. -/
@[simp] theorem ternaryQuaternaryDifferenceGramBlock_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (A : Matrix (Fin 3) (Fin 3) K) (B : Matrix (Fin 4) (Fin 4) K) :
    (ternaryQuaternaryDifferenceGramBlock A B).map f =
      ternaryQuaternaryDifferenceGramBlock (A.map f) (B.map f) := by
  simpa [ternaryQuaternaryDifferenceGramBlock] using
    differenceGramBlock_map f A B

/-- Scalar extension commutes with forming a quaternary-pair difference
block. -/
@[simp] theorem quaternaryPairDifferenceGramBlock_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (A B : Matrix (Fin 4) (Fin 4) K) :
    (quaternaryPairDifferenceGramBlock A B).map f =
      quaternaryPairDifferenceGramBlock (A.map f) (B.map f) := by
  simpa [quaternaryPairDifferenceGramBlock] using differenceGramBlock_map f A B

set_option maxHeartbeats 800000 in
/-- Scalar extension commutes with forming a quaternary-versus-quinary
difference block. -/
@[simp] theorem quaternaryQuinaryDifferenceGramBlock_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (A : Matrix (Fin 4) (Fin 4) K) (B : Matrix (Fin 5) (Fin 5) K) :
    (quaternaryQuinaryDifferenceGramBlock A B).map f =
      quaternaryQuinaryDifferenceGramBlock (A.map f) (B.map f) := by
  simpa [quaternaryQuinaryDifferenceGramBlock] using
    differenceGramBlock_map f A B

set_option maxHeartbeats 800000 in
/-- Scalar extension commutes with forming a quinary-pair difference block. -/
@[simp] theorem quinaryPairDifferenceGramBlock_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (A B : Matrix (Fin 5) (Fin 5) K) :
    (quinaryPairDifferenceGramBlock A B).map f =
      quinaryPairDifferenceGramBlock (A.map f) (B.map f) := by
  simpa [quinaryPairDifferenceGramBlock] using differenceGramBlock_map f A B

/-- Adjoining a leading scalar block preserves symmetry of the tail Gram
matrix. -/
lemma finSuccGramBlock_isSymm
    {K : Type*} [Field K] (c : K)
    (B : Matrix (Fin n) (Fin n) K) (hB : B.IsSymm) :
    (finSuccGramBlock c B).IsSymm := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp [finSuccGramBlock, hB.apply]

/-- The determinant of a leading scalar Gram block is the scalar times the
tail determinant. -/
@[simp] lemma finSuccGramBlock_det
    {K : Type*} [Field K] (c : K)
    (B : Matrix (Fin n) (Fin n) K) :
    (finSuccGramBlock c B).det = c * B.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hsub : (finSuccGramBlock c B).submatrix Fin.succ Fin.succ = B := by
    ext i j
    rfl
  simp [finSuccGramBlock, hsub]

/-- Adjoin a leading fixed coordinate to a square matrix. -/
def finSuccMatrixBlock
    {K : Type*} [Field K]
    (Y : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  finSuccGramBlock 1 Y

/-- The leading standard basis vector in `Fin (n+1)` coordinates. -/
def finSuccHeadVector {K : Type*} [Field K] : Fin (n + 1) → K :=
  Fin.cases 1 (fun _ => 0)

/-- Extract the lower `n`-dimensional block of a matrix indexed by
`Fin (n+1)`. -/
def finSuccTailMatrix
    {K : Type*} [Field K]
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => X i.succ j.succ

/-- Scalar extension commutes with adjoining a leading Gram block. -/
@[simp] lemma finSuccGramBlock_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (c : K) (B : Matrix (Fin n) (Fin n) K) :
    (finSuccGramBlock c B).map f =
      finSuccGramBlock (f c) (B.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp [finSuccGramBlock]

/-- Scalar extension commutes with extracting the tail block. -/
@[simp] lemma finSuccTailMatrix_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    finSuccTailMatrix (X.map f) = (finSuccTailMatrix X).map f := by
  ext i j
  rfl

/-- Block extension transports a lower-dimensional Gram congruence while
leaving the head weight fixed. -/
lemma finSuccMatrixBlock_congr
    {K : Type*} [Field K] (c : K)
    (B Y : Matrix (Fin n) (Fin n) K) :
    (finSuccMatrixBlock Y)ᵀ * finSuccGramBlock c B *
        finSuccMatrixBlock Y =
      finSuccGramBlock c (Yᵀ * B * Y) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp [finSuccMatrixBlock, finSuccGramBlock,
    Matrix.mul_apply, Fin.sum_univ_succ]

lemma finSuccMatrixBlock_mulVec_head
    {K : Type*} [Field K] (Y : Matrix (Fin n) (Fin n) K) :
    finSuccMatrixBlock Y *ᵥ finSuccHeadVector = finSuccHeadVector := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  all_goals simp [finSuccMatrixBlock, finSuccGramBlock,
    finSuccHeadVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma finSuccTailMatrix_finSuccMatrixBlock
    {K : Type*} [Field K] (Y : Matrix (Fin n) (Fin n) K) :
    finSuccTailMatrix (finSuccMatrixBlock Y) = Y := by
  ext i j
  simp [finSuccTailMatrix, finSuccMatrixBlock, finSuccGramBlock]

lemma finSuccMatrixBlock_mul
    {K : Type*} [Field K] (Y Z : Matrix (Fin n) (Fin n) K) :
    finSuccMatrixBlock Y * finSuccMatrixBlock Z =
      finSuccMatrixBlock (Y * Z) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp [finSuccMatrixBlock, finSuccGramBlock,
    Matrix.mul_apply, Fin.sum_univ_succ]

lemma finSuccMatrixBlock_one
    {K : Type*} [Field K] :
    finSuccMatrixBlock (1 : Matrix (Fin n) (Fin n) K) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp [finSuccMatrixBlock, finSuccGramBlock,
    Matrix.one_apply, eq_comm]

/-- Adjoining a leading unit Gram block to an identity matrix gives the
next identity matrix. -/
@[simp] lemma finSuccGramBlock_one
    {K : Type*} [Field K] :
    finSuccGramBlock (1 : K) (1 : Matrix (Fin n) (Fin n) K) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) := by
  simpa [finSuccMatrixBlock] using
    (finSuccMatrixBlock_one (K := K) (n := n))

/-- Block extension of a lower-dimensional general-linear matrix. -/
noncomputable def finSuccGeneralLinearBlock
    {K : Type*} [Field K]
    (Y : Matrix.GeneralLinearGroup (Fin n) K) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) K := by
  let M := finSuccMatrixBlock (Y : Matrix (Fin n) (Fin n) K)
  let N := finSuccMatrixBlock (↑(Y⁻¹) : Matrix (Fin n) (Fin n) K)
  refine ⟨M, N, ?_, ?_⟩
  · rw [show M * N = finSuccMatrixBlock
        ((Y : Matrix (Fin n) (Fin n) K) * ↑(Y⁻¹)) by
      exact finSuccMatrixBlock_mul _ _]
    rw [← Matrix.GeneralLinearGroup.coe_mul]
    simp [finSuccMatrixBlock_one]
  · rw [show N * M = finSuccMatrixBlock
        ((↑(Y⁻¹) : Matrix (Fin n) (Fin n) K) *
          (Y : Matrix (Fin n) (Fin n) K)) by
      exact finSuccMatrixBlock_mul _ _]
    rw [← Matrix.GeneralLinearGroup.coe_mul]
    simp [finSuccMatrixBlock_one]

@[simp] lemma finSuccGeneralLinearBlock_coe
    {K : Type*} [Field K]
    (Y : Matrix.GeneralLinearGroup (Fin n) K) :
    (finSuccGeneralLinearBlock Y : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      finSuccMatrixBlock (Y : Matrix (Fin n) (Fin n) K) := rfl

/-- Fixing the leading standard vector determines the first column. -/
lemma finSucc_fixed_head_entries
    {K : Type*} [Field K]
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hX : X *ᵥ finSuccHeadVector = finSuccHeadVector) :
    X 0 0 = 1 ∧ (∀ i : Fin n, X i.succ 0 = 0) := by
  constructor
  · have h := congrFun hX 0
    simpa [finSuccHeadVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using h
  · intro i
    have h := congrFun hX i.succ
    simpa [finSuccHeadVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using h

/-- A congruence between two `diag(c,-)` blocks which fixes the head vector
has zero off-diagonal entries in its first row when `c` is nonzero. -/
lemma finSucc_fixed_head_row_zero_of_congr
    {K : Type*} [Field K] (c : K) (hc : c ≠ 0)
    (B C : Matrix (Fin n) (Fin n) K)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hcongr : Xᵀ * finSuccGramBlock c B * X = finSuccGramBlock c C)
    (hfix : X *ᵥ finSuccHeadVector = finSuccHeadVector) :
    ∀ j : Fin n, X 0 j.succ = 0 := by
  obtain ⟨h00, hcol⟩ := finSucc_fixed_head_entries X hfix
  intro j
  have h := congrFun (congrFun hcongr 0) j.succ
  simp [finSuccGramBlock, Matrix.mul_apply, Fin.sum_univ_succ,
    h00, hcol] at h
  exact h.resolve_left hc

/-- The tail of a head-fixing block congruence is a congruence of the
codimension-one Gram matrices. -/
lemma finSuccTailMatrix_congr
    {K : Type*} [Field K] (c : K) (hc : c ≠ 0)
    (B C : Matrix (Fin n) (Fin n) K)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hcongr : Xᵀ * finSuccGramBlock c B * X = finSuccGramBlock c C)
    (hfix : X *ᵥ finSuccHeadVector = finSuccHeadVector) :
    (finSuccTailMatrix X)ᵀ * B * finSuccTailMatrix X = C := by
  have hrow := finSucc_fixed_head_row_zero_of_congr
    c hc B C X hcongr hfix
  ext i j
  have h := congrFun (congrFun hcongr i.succ) j.succ
  simp [finSuccTailMatrix, finSuccGramBlock,
    Matrix.mul_apply, Fin.sum_univ_succ, hrow] at h ⊢
  exact h

/-- Scalar extension preserves the congruence induced on the orthogonal
complement coordinates. -/
lemma finSuccTailMatrix_congr_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (c : K) (hc : c ≠ 0)
    (B C : Matrix (Fin n) (Fin n) K)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hcongr : Xᵀ * finSuccGramBlock c B * X = finSuccGramBlock c C)
    (hfix : X *ᵥ finSuccHeadVector = finSuccHeadVector) :
    ((finSuccTailMatrix X).map f)ᵀ * B.map f *
        (finSuccTailMatrix X).map f = C.map f := by
  have htail := finSuccTailMatrix_congr c hc B C X hcongr hfix
  simpa using congrArg (fun M => M.map f) htail

/-- An isometry of `diag(c,B)` fixing the head vector also has zero
off-diagonal entries in its first row when `c` is nonzero. -/
lemma finSucc_fixed_head_row_zero
    {K : Type*} [Field K] (c : K) (hc : c ≠ 0)
    (B : Matrix (Fin n) (Fin n) K)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hpres : Xᵀ * finSuccGramBlock c B * X = finSuccGramBlock c B)
    (hfix : X *ᵥ finSuccHeadVector = finSuccHeadVector) :
    ∀ j : Fin n, X 0 j.succ = 0 :=
  finSucc_fixed_head_row_zero_of_congr c hc B B X hpres hfix

/-- The lower block of an isometry fixing the head vector preserves the
lower Gram matrix. -/
lemma finSuccTailMatrix_preserves
    {K : Type*} [Field K] (c : K) (hc : c ≠ 0)
    (B : Matrix (Fin n) (Fin n) K)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hpres : Xᵀ * finSuccGramBlock c B * X = finSuccGramBlock c B)
    (hfix : X *ᵥ finSuccHeadVector = finSuccHeadVector) :
    (finSuccTailMatrix X)ᵀ * B * finSuccTailMatrix X = B :=
  finSuccTailMatrix_congr c hc B B X hpres hfix

/-- A non-null vector can be prescribed as the first vector of an orthogonal
basis over a field of odd characteristic. -/
theorem exists_orthogonal_basis_with_head
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (B : LinearMap.BilinForm K (Fin (n + 1) → K))
    (hB : LinearMap.IsSymm B) (x : Fin (n + 1) → K)
    (hx : ¬ B.IsOrtho x x) :
    ∃ v : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K),
      v 0 = x ∧ B.IsOrthoᵢ v := by
  classical
  letI : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hchar)
  let W := (K ∙ x).orthogonalBilin B
  have hx0 : x ≠ 0 := LinearMap.BilinForm.ne_zero_of_not_isOrtho_self x hx
  have hdim : Module.finrank K W = n := by
    have hsum := Submodule.finrank_add_eq_of_isCompl
      (LinearMap.BilinForm.isCompl_span_singleton_orthogonal hx).symm
    have hamb : Module.finrank K (Fin (n + 1) → K) = n + 1 := by simp
    rw [finrank_span_singleton hx0] at hsum
    have hsum' : Module.finrank K W + 1 = n + 1 := hsum.trans hamb
    exact Nat.add_right_cancel hsum'
  let B' := B.domRestrict₁₂ W W
  obtain ⟨u0, hu0⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (hB.domRestrict W : B'.IsSymm)
  let e : Fin (Module.finrank K W) ≃ Fin n := Fin.castOrderIso hdim
  let u : Module.Basis (Fin n) K W := u0.reindex e
  have hu : B'.IsOrthoᵢ u := by
    intro i j hij
    simp only [u, Module.Basis.coe_reindex]
    exact hu0 (e.symm.injective.ne hij)
  let v := Module.Basis.mkFinCons x u
    (by
      rintro c y hy hc
      rw [add_eq_zero_iff_neg_eq] at hc
      rw [← hc, Submodule.neg_mem_iff] at hy
      have hdisjoint :=
        (LinearMap.BilinForm.isCompl_span_singleton_orthogonal hx).disjoint
      rw [Submodule.disjoint_def] at hdisjoint
      have hzero := hdisjoint (c • x)
        (Submodule.smul_mem _ _ <| Submodule.mem_span_singleton_self x) hy
      exact (smul_eq_zero.1 hzero).resolve_right fun h =>
        hx <| h.symm ▸ map_zero _)
    (by
      intro y
      refine ⟨-B x y / B x x, fun z hz => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [LinearMap.IsOrtho, map_smul, LinearMap.smul_apply, map_add, map_smul,
        smul_eq_mul, smul_eq_mul, div_mul_cancel₀ _ hx, add_neg_cancel,
        mul_zero])
  refine ⟨v, ?_, ?_⟩
  · simp [v, Module.Basis.coe_mkFinCons]
  · rw [Module.Basis.coe_mkFinCons]
    intro j i
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
      simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ,
        Function.comp_apply]
    · exact (hij rfl).elim
    · rw [LinearMap.IsOrtho, ← hB.eq]
      exact (u j).prop _ (Submodule.mem_span_singleton_self x)
    · exact (u i).prop _ (Submodule.mem_span_singleton_self x)
    · exact hu (ne_of_apply_ne _ hij)

/-- The standard-coordinate matrix of a basis with prescribed first vector
sends the leading coordinate vector to that first vector. -/
lemma basisFun_toMatrix_mulVec_head
    {K : Type*} [Field K]
    (v : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K)) :
    Matrix.mulVec ((Pi.basisFun K (Fin (n + 1))).toMatrix v)
      finSuccHeadVector = v 0 := by
  have h := Module.Basis.toMatrix_mulVec_repr (b := v)
    (b' := Pi.basisFun K (Fin (n + 1))) (v 0)
  have hrepr : ⇑(v.repr (v 0)) = finSuccHeadVector := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [finSuccHeadVector]
  rw [hrepr] at h
  ext i
  simpa [Pi.basisFun_repr] using congrFun h i

/-- Every nonsingular symmetric Gram matrix over a field of odd
characteristic is congruent to a diagonal matrix with nonzero diagonal
entries. -/
theorem exists_gramMatrix_congr_diagonal
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (d : Fin n → K) (P : Matrix.GeneralLinearGroup (Fin n) K),
      (∀ i, d i ≠ 0) ∧
        (↑P : Matrix (Fin n) (Fin n) K)ᵀ * A *
          (↑P : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d := by
  classical
  letI : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hchar)
  let b := Pi.basisFun K (Fin n)
  let B : LinearMap.BilinForm K (Fin n → K) := Matrix.toBilin' A
  have hB_symm : LinearMap.IsSymm B := by
    constructor
    intro x y
    simp only [B, Matrix.toBilin'_apply]
    calc
      (∑ i, ∑ j, x i * A i j * y j) =
          ∑ j, ∑ i, x i * A i j * y j := Finset.sum_comm
      _ = ∑ i, ∑ j, y i * A i j * x j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hA_symm.apply j i]
        ring
  obtain ⟨v0, hv0⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB_symm
  have hrank : Module.finrank K (Fin n → K) = n := by simp
  let e : Fin (Module.finrank K (Fin n → K)) ≃ Fin n := Fin.castOrderIso hrank
  let v : Module.Basis (Fin n) K (Fin n → K) := v0.reindex e
  have hv : LinearMap.IsOrthoᵢ B v := by
    intro i j hij
    simp only [v, Module.Basis.coe_reindex]
    exact hv0 (e.symm.injective.ne hij)
  let d : Fin n → K := fun i ↦ B (v i) (v i)
  let P0 : Matrix (Fin n) (Fin n) K := b.toMatrix v
  letI : Invertible P0 := Module.Basis.invertibleToMatrix b v
  let P : Matrix.GeneralLinearGroup (Fin n) K :=
    Matrix.GeneralLinearGroup.mk'' P0
      ((Matrix.isUnit_iff_isUnit_det P0).mp (isUnit_of_invertible P0))
  refine ⟨d, P, ?_, ?_⟩
  · intro i
    have hB_non : B.Nondegenerate := by
      exact (Matrix.nondegenerate_iff_det_ne_zero.mpr hA_det).toBilin'
    have hnot := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
      hv hB_non i
    simpa [LinearMap.IsOrtho] using hnot
  · have hP0 : P0ᵀ * A * P0 = Matrix.diagonal d := by
      dsimp only [P0]
      calc
        (b.toMatrix v)ᵀ * A * b.toMatrix v =
            (LinearMap.BilinForm.toMatrix v) B := by
          rw [← show (LinearMap.BilinForm.toMatrix b) B = A by
            dsimp only [b, B]
            rw [LinearMap.BilinForm.toMatrix_basisFun]
            exact LinearMap.BilinForm.toMatrix'_toBilin' A]
          exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b v B
        _ = Matrix.diagonal d := by
          ext i j
          by_cases hij : i = j
          · subst j
            simp [d, LinearMap.BilinForm.toMatrix_apply]
          · rw [LinearMap.BilinForm.toMatrix_apply, hv hij]
            simp [Matrix.diagonal, hij]
    simpa [P] using hP0

/-- Diagonalization with a prescribed non-null head vector. The first
diagonal entry is the Gram value of that vector, and the congruence matrix
sends the leading coordinate vector to the prescribed vector. -/
theorem exists_gramMatrix_congr_diagonal_with_head
    {K : Type*} [Field K]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (x : Fin (n + 1) → K)
    (hx : gramQuadraticValue A x ≠ 0) :
    ∃ (d : Fin (n + 1) → K)
        (P : Matrix.GeneralLinearGroup (Fin (n + 1)) K),
      d 0 = gramQuadraticValue A x ∧ (∀ i, d i ≠ 0) ∧
        Matrix.mulVec (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
          finSuccHeadVector = x ∧
        (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K)ᵀ * A *
          (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
            Matrix.diagonal d := by
  classical
  let b := Pi.basisFun K (Fin (n + 1))
  let B : LinearMap.BilinForm K (Fin (n + 1) → K) := Matrix.toBilin' A
  have hB_symm : LinearMap.IsSymm B := by
    constructor
    intro y z
    simp only [B, Matrix.toBilin'_apply]
    calc
      (∑ i, ∑ j, y i * A i j * z j) =
          ∑ j, ∑ i, y i * A i j * z j := Finset.sum_comm
      _ = ∑ i, ∑ j, z i * A i j * y j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hA_symm.apply j i]
        ring
  have hBx : B x x = gramQuadraticValue A x := by
    simp [B, Matrix.toBilin'_apply, gramQuadraticValue, Matrix.mulVec,
      dotProduct, Finset.mul_sum, mul_assoc]
  have hxB : ¬ B.IsOrtho x x := by
    intro h
    apply hx
    simpa [hBx] using LinearMap.BilinForm.isOrtho_def.mp h
  obtain ⟨v, hv0, hv⟩ :=
    exists_orthogonal_basis_with_head hchar B hB_symm x hxB
  let d : Fin (n + 1) → K := fun i => B (v i) (v i)
  let P0 : Matrix (Fin (n + 1)) (Fin (n + 1)) K := b.toMatrix v
  letI : Invertible P0 := Module.Basis.invertibleToMatrix b v
  let P : Matrix.GeneralLinearGroup (Fin (n + 1)) K :=
    Matrix.GeneralLinearGroup.mk'' P0
      ((Matrix.isUnit_iff_isUnit_det P0).mp (isUnit_of_invertible P0))
  refine ⟨d, P, ?_, ?_, ?_, ?_⟩
  · simp [d, hv0, hBx]
  · intro i
    have hB_non : B.Nondegenerate := by
      exact (Matrix.nondegenerate_iff_det_ne_zero.mpr hA_det).toBilin'
    have hnot := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
      hv hB_non i
    simpa [d, LinearMap.IsOrtho] using hnot
  · change Matrix.mulVec P0 finSuccHeadVector = x
    rw [basisFun_toMatrix_mulVec_head v, hv0]
  · have hP0 : P0ᵀ * A * P0 = Matrix.diagonal d := by
      dsimp only [P0]
      calc
        (b.toMatrix v)ᵀ * A * b.toMatrix v =
            (LinearMap.BilinForm.toMatrix v) B := by
          rw [← show (LinearMap.BilinForm.toMatrix b) B = A by
            dsimp only [b, B]
            rw [LinearMap.BilinForm.toMatrix_basisFun]
            exact LinearMap.BilinForm.toMatrix'_toBilin' A]
          exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b v B
        _ = Matrix.diagonal d := by
          ext i j
          by_cases hij : i = j
          · subst j
            simp [d, LinearMap.BilinForm.toMatrix_apply]
          · rw [LinearMap.BilinForm.toMatrix_apply, hv hij]
            simp [Matrix.diagonal, hij]
    simpa [P] using hP0

/-- A nonsingular symmetric Gram space split along a non-null vector. The
tail matrix is the Gram matrix of its codimension-one orthogonal complement
in the chosen coordinates. -/
theorem exists_gramMatrix_congr_finSuccBlock_with_head
    {K : Type*} [Field K]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (x : Fin (n + 1) → K)
    (hx : gramQuadraticValue A x ≠ 0) :
    ∃ (C : Matrix (Fin n) (Fin n) K)
        (P : Matrix.GeneralLinearGroup (Fin (n + 1)) K),
      C.IsSymm ∧ C.det ≠ 0 ∧
        Matrix.mulVec (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
          finSuccHeadVector = x ∧
        (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K)ᵀ * A *
          (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
            finSuccGramBlock (gramQuadraticValue A x) C := by
  classical
  obtain ⟨d, P, hd0, hd, hPhead, hP⟩ :=
    exists_gramMatrix_congr_diagonal_with_head A hA_symm hA_det hchar x hx
  let C : Matrix (Fin n) (Fin n) K :=
    Matrix.diagonal (fun i : Fin n => d i.succ)
  refine ⟨C, P, ?_, ?_, hPhead, ?_⟩
  · simp [C]
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i.succ
  · rw [hP, ← hd0]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    all_goals simp [C, finSuccGramBlock, Matrix.diagonal, eq_comm]

end PositiveDefiniteIntegralLattice
