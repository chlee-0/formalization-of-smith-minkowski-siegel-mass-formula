import SMSFormula.Applications.Unimodular.Seeds
import SMSFormula.StandardAxiomsGuard

/-!
# Finite certificates for even forms modulo eight

The exact finite certificates are checked by computation in Lean.  No all-rank
classification theorem is claimed in this file.
-/

namespace TypeIIModEightCertificates
open Matrix

abbrev R := ZMod 8

def H : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]
def A : Matrix (Fin 2) (Fin 2) R := !![2, 1; 1, 2]

/-- Parity predicate for elements of `ZMod 8`, expressed internally as divisibility by two. -/
def zmod8Even (x : R) : Prop := ∃ y : R, x = 2 * y

/-- Oddness predicate for elements of `ZMod 8`. -/
def zmod8Odd (x : R) : Prop := ∃ y : R, x = 2 * y + 1

/-- Every element of `ZMod 8` is even or odd. -/
theorem zmod8_even_or_odd (x : R) : zmod8Even x ∨ zmod8Odd x := by
  fin_cases x
  · left; exact ⟨0, rfl⟩
  · right; exact ⟨0, rfl⟩
  · left; exact ⟨1, rfl⟩
  · right; exact ⟨1, rfl⟩
  · left; exact ⟨2, rfl⟩
  · right; exact ⟨2, rfl⟩
  · left; exact ⟨3, rfl⟩
  · right; exact ⟨3, rfl⟩

/-- One is not even in `ZMod 8`. -/
theorem zmod8_one_not_even : ¬ zmod8Even (1 : R) := by
  rintro ⟨y, hy⟩
  have hne : (1 : R) ≠ 2 * y := by
    fin_cases y <;> decide
  exact hne hy

/-- Even elements of `ZMod 8` are closed under addition. -/
theorem zmod8Even_add {x y : R} (hx : zmod8Even x) (hy : zmod8Even y) :
    zmod8Even (x + y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a + b, by ring⟩

/-- Multiplying an even element of `ZMod 8` on the right keeps it even. -/
theorem zmod8Even_mul_left {x y : R} (hx : zmod8Even x) : zmod8Even (x * y) := by
  rcases hx with ⟨a, rfl⟩
  exact ⟨a * y, by ring⟩

/-- Finite sums of even `ZMod 8` elements are even. -/
theorem zmod8Even_sum {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i, i ∈ s → zmod8Even (f i)) : zmod8Even (Finset.sum s f) := by
  classical
  revert hf
  refine Finset.induction_on s ?base ?step
  · intro _
    exact ⟨0, rfl⟩
  · intro a s has ih hf
    rw [Finset.sum_insert has]
    exact zmod8Even_add (hf a (by simp))
      (ih (by intro i hi; exact hf i (by simp [hi])))

/-- In a right-invertible mod-eight matrix with even diagonal, every row has an
odd off-diagonal entry.  This is the finite pivot-existence lemma used by the
rank-uniform Type II normal-form route before applying the binary certificates. -/
theorem exists_odd_offdiag_of_even_diag_right_inverse {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) R) (hGV : G * V = 1)
    (hdiag : ∀ i, zmod8Even (G i i)) (i : Fin n) :
    ∃ j, j ≠ i ∧ zmod8Odd (G i j) := by
  by_contra hnone
  have hrow : ∀ j, zmod8Even (G i j) := by
    intro j
    by_cases hji : j = i
    · simpa [hji] using hdiag i
    · have hnot : ¬ zmod8Odd (G i j) := by
        intro hodd
        exact hnone ⟨j, hji, hodd⟩
      cases zmod8_even_or_odd (G i j) with
      | inl he => exact he
      | inr ho => exact False.elim (hnot ho)
  have hsum : zmod8Even (∑ j : Fin n, G i j * V j i) := by
    exact zmod8Even_sum Finset.univ (fun j => G i j * V j i)
      (by intro j _; exact zmod8Even_mul_left (hrow j))
  have hentry := congrFun (congrFun hGV i) i
  rw [Matrix.mul_apply] at hentry
  have hentry' : (∑ j, G i j * V j i) = (1 : R) := by
    simpa [Matrix.one_apply] using hentry
  have hone : zmod8Even (1 : R) := by
    rw [← hentry']
    exact hsum
  exact zmod8_one_not_even hone

def binary (a b c : Fin 4) : Matrix (Fin 2) (Fin 2) R :=
  !![2 * (a.val : R), 2 * (b.val : R) + 1;
     2 * (b.val : R) + 1, 2 * (c.val : R)]

def binaryTarget (a c : Fin 4) : Matrix (Fin 2) (Fin 2) R :=
  if a.val % 2 = 1 ∧ c.val % 2 = 1 then A else H

def binaryIndex (a b c : Fin 4) : Fin 64 :=
  ⟨16 * a.val + 4 * b.val + c.val, by omega⟩

def changeTable : Fin 64 → Matrix (Fin 2) (Fin 2) R :=
  ![!![0, 1; 1, 0],
    !![1, 3; 0, 1],
    !![1, 2; 0, 1],
    !![1, 1; 0, 1],
    !![0, 1; 3, 0],
    !![1, 3; 0, 3],
    !![1, 2; 0, 3],
    !![1, 1; 0, 3],
    !![0, 1; 5, 0],
    !![1, 3; 0, 5],
    !![1, 2; 0, 5],
    !![1, 1; 0, 5],
    !![0, 1; 7, 0],
    !![1, 3; 0, 7],
    !![1, 2; 0, 7],
    !![1, 1; 0, 7],
    !![0, 1; 1, 3],
    !![0, 1; 1, 0],
    !![1, 2; 1, 7],
    !![1, 2; 0, 5],
    !![0, 1; 3, 1],
    !![0, 1; 3, 0],
    !![1, 2; 3, 5],
    !![1, 2; 0, 7],
    !![0, 1; 5, 3],
    !![0, 1; 3, 3],
    !![1, 2; 1, 3],
    !![1, 2; 0, 1],
    !![0, 1; 7, 1],
    !![0, 1; 1, 1],
    !![1, 2; 3, 1],
    !![1, 2; 0, 3],
    !![0, 1; 1, 2],
    !![1, 3; 1, 6],
    !![1, 2; 2, 5],
    !![1, 1; 2, 7],
    !![0, 1; 3, 2],
    !![1, 3; 2, 5],
    !![1, 2; 2, 7],
    !![1, 1; 1, 2],
    !![0, 1; 5, 2],
    !![1, 3; 1, 2],
    !![1, 2; 2, 1],
    !![1, 1; 2, 3],
    !![0, 1; 7, 2],
    !![1, 3; 2, 1],
    !![1, 2; 2, 3],
    !![1, 1; 1, 6],
    !![0, 1; 1, 1],
    !![0, 1; 3, 1],
    !![1, 2; 3, 3],
    !![1, 2; 2, 5],
    !![0, 1; 3, 3],
    !![0, 1; 1, 3],
    !![1, 2; 1, 1],
    !![1, 2; 1, 7],
    !![0, 1; 5, 1],
    !![0, 1; 1, 2],
    !![1, 2; 3, 7],
    !![1, 2; 2, 1],
    !![0, 1; 7, 3],
    !![0, 1; 3, 2],
    !![1, 2; 1, 5],
    !![1, 2; 1, 3]]

def inverseTable : Fin 64 → Matrix (Fin 2) (Fin 2) R :=
  ![!![0, 1; 1, 0],
    !![1, 5; 0, 1],
    !![1, 6; 0, 1],
    !![1, 7; 0, 1],
    !![0, 3; 1, 0],
    !![1, 7; 0, 3],
    !![1, 2; 0, 3],
    !![1, 5; 0, 3],
    !![0, 5; 1, 0],
    !![1, 1; 0, 5],
    !![1, 6; 0, 5],
    !![1, 3; 0, 5],
    !![0, 7; 1, 0],
    !![1, 3; 0, 7],
    !![1, 2; 0, 7],
    !![1, 1; 0, 7],
    !![5, 1; 1, 0],
    !![0, 1; 1, 0],
    !![3, 6; 3, 5],
    !![1, 6; 0, 5],
    !![5, 3; 1, 0],
    !![0, 3; 1, 0],
    !![3, 2; 3, 7],
    !![1, 2; 0, 7],
    !![1, 5; 1, 0],
    !![7, 3; 1, 0],
    !![3, 6; 7, 1],
    !![1, 6; 0, 1],
    !![1, 7; 1, 0],
    !![7, 1; 1, 0],
    !![3, 2; 7, 3],
    !![1, 2; 0, 3],
    !![6, 1; 1, 0],
    !![2, 7; 5, 3],
    !![5, 6; 6, 1],
    !![3, 3; 6, 5],
    !![2, 3; 1, 0],
    !![3, 3; 2, 7],
    !![5, 2; 2, 3],
    !![2, 7; 7, 1],
    !![6, 5; 1, 0],
    !![6, 3; 1, 7],
    !![5, 6; 6, 5],
    !![3, 7; 6, 1],
    !![2, 7; 1, 0],
    !![3, 7; 2, 3],
    !![5, 2; 2, 7],
    !![6, 3; 3, 5],
    !![7, 1; 1, 0],
    !![5, 3; 1, 0],
    !![7, 6; 1, 5],
    !![5, 6; 6, 1],
    !![7, 3; 1, 0],
    !![5, 1; 1, 0],
    !![7, 2; 1, 7],
    !![3, 6; 3, 5],
    !![3, 5; 1, 0],
    !![6, 1; 1, 0],
    !![7, 6; 5, 1],
    !![5, 6; 6, 5],
    !![3, 7; 1, 0],
    !![2, 3; 1, 0],
    !![7, 2; 5, 3],
    !![3, 6; 7, 1]]

def binaryChange (a b c : Fin 4) := changeTable (binaryIndex a b c)
def binaryInverse (a b c : Fin 4) := inverseTable (binaryIndex a b c)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- All 64 binary forms, with explicit two-sided inverse certificates. -/
theorem all_binary_certificates :
    ∀ a b c : Fin 4,
      (binaryChange a b c).transpose * binary a b c * binaryChange a b c =
        binaryTarget a c ∧
      binaryChange a b c * binaryInverse a b c = 1 ∧
      binaryInverse a b c * binaryChange a b c = 1 := by
  decide

/-- Congruence component of `all_binary_certificates`. -/
theorem binaryChange_congruence (a b c : Fin 4) :
    (binaryChange a b c).transpose * binary a b c * binaryChange a b c =
      binaryTarget a c :=
  (all_binary_certificates a b c).1

/-- Right-inverse component of `all_binary_certificates`. -/
theorem binaryChange_mul_inverse (a b c : Fin 4) :
    binaryChange a b c * binaryInverse a b c = 1 :=
  (all_binary_certificates a b c).2.1

/-- Left-inverse component of `all_binary_certificates`. -/
theorem binaryInverse_mul_change (a b c : Fin 4) :
    binaryInverse a b c * binaryChange a b c = 1 :=
  (all_binary_certificates a b c).2.2

/-- The split binary target has determinant `-1` modulo eight. -/
theorem H_det : H.det = (-1 : R) := by
  decide

/-- The anisotropic binary target has determinant `3` modulo eight. -/
theorem A_det : A.det = (3 : R) := by
  decide

/-- The finite binary target determinant is the H/A determinant dictated by its parity branch. -/
theorem binaryTarget_det (a c : Fin 4) :
    (binaryTarget a c).det =
      if a.val % 2 = 1 ∧ c.val % 2 = 1 then (3 : R) else (-1 : R) := by
  by_cases h : a.val % 2 = 1 ∧ c.val % 2 = 1
  · simp [binaryTarget, h, A_det]
  · simp [binaryTarget, h, H_det]

/-- The finite binary target determinant is always a unit modulo eight. -/
theorem binaryTarget_det_unit_certificate (a c : Fin 4) :
    ∃ u : R, (binaryTarget a c).det * u = 1 := by
  by_cases h : a.val % 2 = 1 ∧ c.val % 2 = 1
  · refine ⟨3, ?_⟩
    rw [binaryTarget_det]
    simp [h]
    decide
  · refine ⟨(-1 : R), ?_⟩
    rw [binaryTarget_det]
    simp [h]

def aaChange : Matrix (Fin 4) (Fin 4) R := !![0, 0, 1, 3; 1, 7, 0, 5; 1, 7, 2, 2; 1, 2, 3, 7]
def aaInverse : Matrix (Fin 4) (Fin 4) R := !![7, 6, 0, 3; 1, 2, 3, 3; 3, 5, 3, 0; 2, 1, 7, 0]
def AA : Matrix (Fin 4) (Fin 4) R := !![2, 1, 0, 0; 1, 2, 0, 0; 0, 0, 2, 1; 0, 0, 1, 2]
def HH : Matrix (Fin 4) (Fin 4) R := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

/-- Cancellation is a congruence modulo eight, not an integral isometry. -/
theorem aa_certificate :
    aaChange.transpose * AA * aaChange = HH ∧
    aaChange * aaInverse = 1 ∧ aaInverse * aaChange = 1 := by
  decide

/-- Congruence component of the A+A cancellation certificate. -/
theorem aa_congruence : aaChange.transpose * AA * aaChange = HH :=
  aa_certificate.1

/-- Right-inverse component of the A+A cancellation certificate. -/
theorem aa_mul_inverse : aaChange * aaInverse = 1 :=
  aa_certificate.2.1

/-- Left-inverse component of the A+A cancellation certificate. -/
theorem aa_inverse_mul : aaInverse * aaChange = 1 :=
  aa_certificate.2.2

/-- Every unit square is one modulo eight. The inverse is explicit. -/
theorem unit_square_certificate :
    ∀ u v : R, u * v = 1 → u ^ 2 = 1 := by
  decide

def e8Change : Matrix (Fin 8) (Fin 8) R := !![3, 1, 7, 3, 6, 1, 7, 0; 6, 2, 6, 6, 3, 3, 7, 6; 1, 3, 5, 1, 7, 6, 5, 1; 2, 1, 4, 1, 4, 0, 4, 4; 0, 0, 3, 1, 1, 2, 3, 7; 0, 0, 2, 1, 5, 1, 4, 4; 0, 0, 1, 1, 0, 0, 0, 0; 0, 0, 0, 3, 0, 0, 0, 0]
def e8Inverse : Matrix (Fin 8) (Fin 8) R := !![0, 0, 3, 7, 7, 0, 0, 5; 0, 0, 2, 3, 6, 0, 0, 7; 0, 0, 0, 0, 0, 0, 1, 5; 0, 0, 0, 0, 0, 0, 0, 3; 7, 7, 1, 0, 3, 0, 7, 2; 1, 1, 7, 0, 1, 1, 3, 1; 2, 3, 0, 0, 6, 1, 4, 7; 7, 2, 7, 0, 6, 5, 4, 3]
def H4 : Matrix (Fin 8) (Fin 8) R := !![0, 1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 0]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The actual stored E8 Cartan matrix, not an unrelated split model. -/
theorem e8_certificate :
    e8Change.transpose *
        (PositiveDefiniteIntegralLattice.e8CartanMatrix.map (Int.cast : ℤ → R)) * e8Change = H4 ∧
      e8Change * e8Inverse = 1 ∧ e8Inverse * e8Change = 1 := by
  decide

/-- Congruence component of the actual E8-to-H^4 certificate. -/
theorem e8_congruence :
    e8Change.transpose *
        (PositiveDefiniteIntegralLattice.e8CartanMatrix.map (Int.cast : ℤ → R)) * e8Change = H4 :=
  e8_certificate.1

/-- Right-inverse component of the actual E8-to-H^4 certificate. -/
theorem e8_mul_inverse : e8Change * e8Inverse = 1 :=
  e8_certificate.2.1

/-- Left-inverse component of the actual E8-to-H^4 certificate. -/
theorem e8_inverse_mul : e8Inverse * e8Change = 1 :=
  e8_certificate.2.2

/-! ## Composable congruence certificates -/

/-- Block-sum a pair of finite matrices on a sum index type.  This is the
finite certificate analogue of a direct sum of quadratic blocks. -/
def sumBlockMatrix {α β : Type*} (A : Matrix α α R) (B : Matrix β β R) :
    Matrix (α ⊕ β) (α ⊕ β) R
  | Sum.inl i, Sum.inl j => A i j
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr i, Sum.inr j => B i j

@[simp] theorem sumBlockMatrix_inl_inl {α β : Type*}
    (A : Matrix α α R) (B : Matrix β β R) (i j : α) :
    sumBlockMatrix A B (Sum.inl i) (Sum.inl j) = A i j := rfl

@[simp] theorem sumBlockMatrix_inl_inr {α β : Type*}
    (A : Matrix α α R) (B : Matrix β β R) (i : α) (j : β) :
    sumBlockMatrix A B (Sum.inl i) (Sum.inr j) = 0 := rfl

@[simp] theorem sumBlockMatrix_inr_inl {α β : Type*}
    (A : Matrix α α R) (B : Matrix β β R) (i : β) (j : α) :
    sumBlockMatrix A B (Sum.inr i) (Sum.inl j) = 0 := rfl

@[simp] theorem sumBlockMatrix_inr_inr {α β : Type*}
    (A : Matrix α α R) (B : Matrix β β R) (i j : β) :
    sumBlockMatrix A B (Sum.inr i) (Sum.inr j) = B i j := rfl

/-- Transposition respects direct sums of finite certificates. -/
theorem sumBlockMatrix_transpose {α β : Type*}
    (A : Matrix α α R) (B : Matrix β β R) :
    (sumBlockMatrix A B).transpose = sumBlockMatrix A.transpose B.transpose := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Matrix multiplication respects direct sums of finite certificates. -/
theorem sumBlockMatrix_mul {α β : Type*} [Fintype α] [Fintype β]
    (A C : Matrix α α R) (B D : Matrix β β R) :
    sumBlockMatrix A B * sumBlockMatrix C D = sumBlockMatrix (A * C) (B * D) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.mul_apply, sumBlockMatrix, Fintype.sum_sum_type]

/-- The direct sum of identity matrices is the identity matrix. -/
theorem sumBlockMatrix_one {α β : Type*} [DecidableEq α] [DecidableEq β] :
    sumBlockMatrix (1 : Matrix α α R) (1 : Matrix β β R) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [sumBlockMatrix, Matrix.one_apply]

/-- Simultaneous reindexing commutes with transposition. -/
theorem reindexMatrix_transpose {α β : Type*} (e : α ≃ β) (A : Matrix α α R) :
    (Matrix.reindex e e A).transpose = Matrix.reindex e e A.transpose := by
  ext i j
  simp [Matrix.reindex_apply]

/-- Simultaneous reindexing commutes with matrix multiplication. -/
theorem reindexMatrix_mul {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A B : Matrix α α R) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B := by
  ext i j
  simp [Matrix.mul_apply, Matrix.reindex_apply, ← e.sum_comp]

/-- Simultaneous reindexing preserves the identity matrix. -/
theorem reindexMatrix_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) :
    Matrix.reindex e e (1 : Matrix α α R) = 1 := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.one_apply]

/-- A finite mod-eight Gram-congruence certificate, including an explicit
two-sided inverse for the change matrix. -/
structure GramCongruenceCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (source target : Matrix ι ι R) where
  changeMatrix : Matrix ι ι R
  inverseMatrix : Matrix ι ι R
  congruence : changeMatrix.transpose * source * changeMatrix = target
  mul_inverse : changeMatrix * inverseMatrix = 1
  inverse_mul : inverseMatrix * changeMatrix = 1

/-- A finite Gram-congruence certificate preserves determinants modulo eight.  This is the
certificate-level invariant used by the normal-form route to track the H/A parity. -/
theorem GramCongruenceCertificate.det_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {source target : Matrix ι ι R}
    (C : GramCongruenceCertificate source target) :
    target.det = source.det := by
  have hunit : C.changeMatrix.det * C.inverseMatrix.det = 1 := by
    have h := congrArg Matrix.det C.mul_inverse
    simpa [Matrix.det_mul] using h
  have hsquare : C.changeMatrix.det ^ 2 = 1 :=
    unit_square_certificate C.changeMatrix.det C.inverseMatrix.det hunit
  have hdet := congrArg Matrix.det C.congruence
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  calc
    target.det = C.changeMatrix.det * source.det * C.changeMatrix.det := hdet.symm
    _ = C.changeMatrix.det ^ 2 * source.det := by ring
    _ = source.det := by rw [hsquare]; simp

/-- Reverse a packaged finite Gram-congruence certificate using its explicit inverse. -/
def GramCongruenceCertificate.symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {source target : Matrix ι ι R}
    (C : GramCongruenceCertificate source target) :
    GramCongruenceCertificate target source where
  changeMatrix := C.inverseMatrix
  inverseMatrix := C.changeMatrix
  congruence := by
    calc
      C.inverseMatrix.transpose * target * C.inverseMatrix =
          C.inverseMatrix.transpose * (C.changeMatrix.transpose * source * C.changeMatrix) *
            C.inverseMatrix := by rw [C.congruence]
      _ = (C.changeMatrix * C.inverseMatrix).transpose * source *
            (C.changeMatrix * C.inverseMatrix) := by
          rw [Matrix.transpose_mul]
          noncomm_ring
      _ = source := by rw [C.mul_inverse]; simp
  mul_inverse := C.inverse_mul
  inverse_mul := C.mul_inverse

/-- Compose packaged finite Gram-congruence certificates. -/
def GramCongruenceCertificate.trans {ι : Type*} [Fintype ι] [DecidableEq ι]
    {source middle target : Matrix ι ι R}
    (C : GramCongruenceCertificate source middle)
    (D : GramCongruenceCertificate middle target) :
    GramCongruenceCertificate source target where
  changeMatrix := C.changeMatrix * D.changeMatrix
  inverseMatrix := D.inverseMatrix * C.inverseMatrix
  congruence := by
    calc
      (C.changeMatrix * D.changeMatrix).transpose * source *
          (C.changeMatrix * D.changeMatrix) =
          D.changeMatrix.transpose * (C.changeMatrix.transpose * source * C.changeMatrix) *
            D.changeMatrix := by
            rw [Matrix.transpose_mul]
            noncomm_ring
      _ = D.changeMatrix.transpose * middle * D.changeMatrix := by rw [C.congruence]
      _ = target := D.congruence
  mul_inverse := by
    calc
      (C.changeMatrix * D.changeMatrix) * (D.inverseMatrix * C.inverseMatrix) =
          C.changeMatrix * (D.changeMatrix * D.inverseMatrix) * C.inverseMatrix := by
          noncomm_ring
      _ = C.changeMatrix * C.inverseMatrix := by rw [D.mul_inverse]; simp
      _ = 1 := C.mul_inverse
  inverse_mul := by
    calc
      (D.inverseMatrix * C.inverseMatrix) * (C.changeMatrix * D.changeMatrix) =
          D.inverseMatrix * (C.inverseMatrix * C.changeMatrix) * D.changeMatrix := by
          noncomm_ring
      _ = D.inverseMatrix * D.changeMatrix := by rw [C.inverse_mul]; simp
      _ = 1 := D.inverse_mul

/-- The checked binary reduction packaged as a reusable congruence certificate. -/
def binaryGramCertificate (a b c : Fin 4) :
    GramCongruenceCertificate (binary a b c) (binaryTarget a c) where
  changeMatrix := binaryChange a b c
  inverseMatrix := binaryInverse a b c
  congruence := binaryChange_congruence a b c
  mul_inverse := binaryChange_mul_inverse a b c
  inverse_mul := binaryInverse_mul_change a b c

/-- The checked `A + A` cancellation packaged as a reusable congruence certificate. -/
def aaCancellationCertificate : GramCongruenceCertificate AA HH where
  changeMatrix := aaChange
  inverseMatrix := aaInverse
  congruence := aa_congruence
  mul_inverse := aa_mul_inverse
  inverse_mul := aa_inverse_mul

/-- The checked stored-`E8` to `H^4` reduction packaged as a reusable congruence certificate. -/
def e8ToH4Certificate :
    GramCongruenceCertificate (PositiveDefiniteIntegralLattice.e8CartanMatrix.map (Int.cast : ℤ → R)) H4 where
  changeMatrix := e8Change
  inverseMatrix := e8Inverse
  congruence := e8_congruence
  mul_inverse := e8_mul_inverse
  inverse_mul := e8_inverse_mul

/-- Direct sums compose finite mod-eight Gram-congruence certificates. -/
def sumBlockCertificate {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {A T : Matrix α α R} {B S : Matrix β β R}
    (C : GramCongruenceCertificate A T) (D : GramCongruenceCertificate B S) :
    GramCongruenceCertificate (sumBlockMatrix A B) (sumBlockMatrix T S) where
  changeMatrix := sumBlockMatrix C.changeMatrix D.changeMatrix
  inverseMatrix := sumBlockMatrix C.inverseMatrix D.inverseMatrix
  congruence := by
    rw [sumBlockMatrix_transpose, sumBlockMatrix_mul, sumBlockMatrix_mul,
      C.congruence, D.congruence]
  mul_inverse := by
    rw [sumBlockMatrix_mul, C.mul_inverse, D.mul_inverse, sumBlockMatrix_one]
  inverse_mul := by
    rw [sumBlockMatrix_mul, C.inverse_mul, D.inverse_mul, sumBlockMatrix_one]

/-- Reindex a finite mod-eight Gram-congruence certificate. -/
def reindexCertificate {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    {A T : Matrix α α R} (C : GramCongruenceCertificate A T) :
    GramCongruenceCertificate (Matrix.reindex e e A) (Matrix.reindex e e T) where
  changeMatrix := Matrix.reindex e e C.changeMatrix
  inverseMatrix := Matrix.reindex e e C.inverseMatrix
  congruence := by
    rw [reindexMatrix_transpose, ← reindexMatrix_mul, ← reindexMatrix_mul, C.congruence]
  mul_inverse := by
    rw [← reindexMatrix_mul, C.mul_inverse, reindexMatrix_one]
  inverse_mul := by
    rw [← reindexMatrix_mul, C.inverse_mul, reindexMatrix_one]

/-- The permutation matrix whose `j`th column is the standard basis vector at
`e.symm j`.  This packages coordinate reindexing as an ordinary square change
matrix over `ZMod 8`, where `Matrix.GeneralLinearGroup` is not available through
a field structure. -/
def equivPermutationMatrix {ι : Type*} [DecidableEq ι] (e : ι ≃ ι) : Matrix ι ι R :=
  fun i j => if i = e.symm j then 1 else 0

@[simp] theorem equivPermutationMatrix_transpose {ι : Type*} [DecidableEq ι]
    (e : ι ≃ ι) :
    (equivPermutationMatrix e).transpose = equivPermutationMatrix e.symm := by
  ext i j
  change (if j = e.symm i then 1 else 0) = if i = e j then 1 else 0
  by_cases h : i = e j
  · have h' : j = e.symm i := by rw [h]; simp
    rw [if_pos h, if_pos h']
  · have h' : j ≠ e.symm i := by
      intro hij
      apply h
      rw [hij]
      simp
    rw [if_neg h, if_neg h']

@[simp] theorem equivPermutationMatrix_mul_symm {ι : Type*} [Fintype ι]
    [DecidableEq ι] (e : ι ≃ ι) :
    equivPermutationMatrix e * equivPermutationMatrix e.symm = 1 := by
  ext i j
  simp [equivPermutationMatrix, Matrix.mul_apply, Matrix.one_apply]

@[simp] theorem equivPermutationMatrix_symm_mul {ι : Type*} [Fintype ι]
    [DecidableEq ι] (e : ι ≃ ι) :
    equivPermutationMatrix e.symm * equivPermutationMatrix e = 1 := by
  simpa using equivPermutationMatrix_mul_symm e.symm

@[simp] theorem equivPermutationMatrix_mul_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (e : ι ≃ ι) (A : Matrix ι ι R) (i j : ι) :
    (equivPermutationMatrix e * A) i j = A (e i) j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (e i)]
  · simp [equivPermutationMatrix]
  · intro b hb
    have hne : i ≠ e.symm b := by
      intro h
      apply hb
      simpa using (congrArg e h).symm
    simp [equivPermutationMatrix, hne]

@[simp] theorem mul_equivPermutationMatrix_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι R) (e : ι ≃ ι) (i j : ι) :
    (A * equivPermutationMatrix e) i j = A i (e.symm j) := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (e.symm j)]
  · simp [equivPermutationMatrix]
  · intro b hb
    simp [equivPermutationMatrix, hb]

/-- Congruence by the permutation matrix is exactly simultaneous reindexing. -/
theorem equivPermutationMatrix_congruence_reindex {ι : Type*} [Fintype ι]
    [DecidableEq ι] (e : ι ≃ ι) (A : Matrix ι ι R) :
    (equivPermutationMatrix e).transpose * A * equivPermutationMatrix e =
      Matrix.reindex e e A := by
  ext i j
  rw [mul_equivPermutationMatrix_apply, equivPermutationMatrix_transpose,
    equivPermutationMatrix_mul_apply]
  rfl

/-- Simultaneous reindexing by a permutation of a fixed coordinate type is itself a
finite mod-eight Gram-congruence certificate. -/
def reindexSelfCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (A : Matrix ι ι R) :
    GramCongruenceCertificate A (Matrix.reindex e e A) where
  changeMatrix := equivPermutationMatrix e
  inverseMatrix := equivPermutationMatrix e.symm
  congruence := equivPermutationMatrix_congruence_reindex e A
  mul_inverse := equivPermutationMatrix_mul_symm e
  inverse_mul := equivPermutationMatrix_symm_mul e

/-- The generic block-sum matrix is the same matrix as `Matrix.fromBlocks`. -/
theorem sumBlockMatrix_eq_fromBlocks {α β : Type*}
    (A : Matrix α α R) (B : Matrix β β R) :
    sumBlockMatrix A B = Matrix.fromBlocks A 0 0 B := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Direct-sum certificates reindexed to the usual `Fin (m+n)` block coordinates. -/
def finBlockCertificate {m n : ℕ}
    {A T : Matrix (Fin m) (Fin m) R} {B S : Matrix (Fin n) (Fin n) R}
    (C : GramCongruenceCertificate A T) (D : GramCongruenceCertificate B S) :
    GramCongruenceCertificate
      (Matrix.reindex finSumFinEquiv finSumFinEquiv (sumBlockMatrix A B))
      (Matrix.reindex finSumFinEquiv finSumFinEquiv (sumBlockMatrix T S)) :=
  reindexCertificate finSumFinEquiv (sumBlockCertificate C D)

/-- The application block-sum matrix, reduced modulo eight, is the generic finite-certificate
block sum reindexed to the stored `Fin (m+n)` coordinates. -/
theorem blockSumMatrix_map_zmodEight {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℤ) (B : Matrix (Fin n) (Fin n) ℤ) :
    (PositiveDefiniteIntegralLattice.blockSumMatrix A B).map (Int.cast : ℤ → R) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (sumBlockMatrix (A.map (Int.cast : ℤ → R)) (B.map (Int.cast : ℤ → R))) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [PositiveDefiniteIntegralLattice.blockSumMatrix, sumBlockMatrix]

/-- The canonical equivalence between two binary block indices and four coordinates. -/
def finTwoSumFinTwoEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv

/-- The generic direct sum `A ⊕ A` reindexes to the generated four-coordinate matrix `AA`. -/
theorem reindex_sumBlock_A_A_eq_AA :
    Matrix.reindex finTwoSumFinTwoEquiv finTwoSumFinTwoEquiv (sumBlockMatrix A A) = AA := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The generated four-coordinate matrix `AA` is the generic direct sum `A ⊕ A` on the
sum index. -/
theorem submatrix_AA_eq_sumBlock_A_A :
    AA.submatrix ⇑finTwoSumFinTwoEquiv ⇑finTwoSumFinTwoEquiv = sumBlockMatrix A A := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;> decide
      | inr j => fin_cases i <;> fin_cases j <;> decide
  | inr i =>
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;> decide
      | inr j => fin_cases i <;> fin_cases j <;> decide

/-- The generated four-coordinate matrix `HH` is the generic direct sum `H ⊕ H` on the
sum index. -/
theorem submatrix_HH_eq_sumBlock_H_H :
    HH.submatrix ⇑finTwoSumFinTwoEquiv ⇑finTwoSumFinTwoEquiv = sumBlockMatrix H H := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;> decide
      | inr j => fin_cases i <;> fin_cases j <;> decide
  | inr i =>
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;> decide
      | inr j => fin_cases i <;> fin_cases j <;> decide

/-- The checked `A + A` cancellation, converted to the generic sum-index certificate
interface used by recursive normal-form assembly. -/
def aaCancellationSumCertificate :
    GramCongruenceCertificate (sumBlockMatrix A A) (sumBlockMatrix H H) := by
  let C := reindexCertificate finTwoSumFinTwoEquiv.symm aaCancellationCertificate
  exact {
    changeMatrix := C.changeMatrix
    inverseMatrix := C.inverseMatrix
    congruence := by
      simpa [submatrix_AA_eq_sumBlock_A_A, submatrix_HH_eq_sumBlock_H_H] using C.congruence
    mul_inverse := C.mul_inverse
    inverse_mul := C.inverse_mul
  }

/-- The canonical equivalence between two four-coordinate H+H blocks and eight coordinates. -/
def finFourSumFinFourEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8 := finSumFinEquiv

/-- The generic direct sum `HH ⊕ HH` reindexes to the generated eight-coordinate `H4`. -/
theorem reindex_sumBlock_HH_HH_eq_H4 :
    Matrix.reindex finFourSumFinFourEquiv finFourSumFinFourEquiv (sumBlockMatrix HH HH) = H4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The generated eight-coordinate `H4` is the generic direct sum `HH ⊕ HH` on the
sum index. -/
theorem submatrix_H4_eq_sumBlock_HH_HH :
    H4.submatrix ⇑finFourSumFinFourEquiv ⇑finFourSumFinFourEquiv = sumBlockMatrix HH HH := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;> decide
      | inr j => fin_cases i <;> fin_cases j <;> decide
  | inr i =>
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;> decide
      | inr j => fin_cases i <;> fin_cases j <;> decide

end TypeIIModEightCertificates

#assert_standard_axioms TypeIIModEightCertificates.zmod8Even
#assert_standard_axioms TypeIIModEightCertificates.zmod8Odd
#assert_standard_axioms TypeIIModEightCertificates.zmod8_even_or_odd
#assert_standard_axioms TypeIIModEightCertificates.zmod8_one_not_even
#assert_standard_axioms TypeIIModEightCertificates.zmod8Even_add
#assert_standard_axioms TypeIIModEightCertificates.zmod8Even_mul_left
#assert_standard_axioms TypeIIModEightCertificates.zmod8Even_sum
#assert_standard_axioms TypeIIModEightCertificates.exists_odd_offdiag_of_even_diag_right_inverse
#assert_standard_axioms TypeIIModEightCertificates.all_binary_certificates
#assert_standard_axioms TypeIIModEightCertificates.binaryChange_congruence
#assert_standard_axioms TypeIIModEightCertificates.binaryChange_mul_inverse
#assert_standard_axioms TypeIIModEightCertificates.binaryInverse_mul_change
#assert_standard_axioms TypeIIModEightCertificates.H_det
#assert_standard_axioms TypeIIModEightCertificates.A_det
#assert_standard_axioms TypeIIModEightCertificates.binaryTarget_det
#assert_standard_axioms TypeIIModEightCertificates.binaryTarget_det_unit_certificate
#assert_standard_axioms TypeIIModEightCertificates.aa_certificate
#assert_standard_axioms TypeIIModEightCertificates.aa_congruence
#assert_standard_axioms TypeIIModEightCertificates.aa_mul_inverse
#assert_standard_axioms TypeIIModEightCertificates.aa_inverse_mul
#assert_standard_axioms TypeIIModEightCertificates.unit_square_certificate
#assert_standard_axioms TypeIIModEightCertificates.e8_certificate
#assert_standard_axioms TypeIIModEightCertificates.e8_congruence
#assert_standard_axioms TypeIIModEightCertificates.e8_mul_inverse
#assert_standard_axioms TypeIIModEightCertificates.e8_inverse_mul
#assert_standard_axioms TypeIIModEightCertificates.sumBlockMatrix_transpose
#assert_standard_axioms TypeIIModEightCertificates.sumBlockMatrix_mul
#assert_standard_axioms TypeIIModEightCertificates.sumBlockMatrix_one
#assert_standard_axioms TypeIIModEightCertificates.reindexMatrix_transpose
#assert_standard_axioms TypeIIModEightCertificates.reindexMatrix_mul
#assert_standard_axioms TypeIIModEightCertificates.reindexMatrix_one
#assert_standard_axioms TypeIIModEightCertificates.GramCongruenceCertificate.det_eq
#assert_standard_axioms TypeIIModEightCertificates.GramCongruenceCertificate.symm
#assert_standard_axioms TypeIIModEightCertificates.GramCongruenceCertificate.trans
#assert_standard_axioms TypeIIModEightCertificates.binaryGramCertificate
#assert_standard_axioms TypeIIModEightCertificates.aaCancellationCertificate
#assert_standard_axioms TypeIIModEightCertificates.e8ToH4Certificate
#assert_standard_axioms TypeIIModEightCertificates.sumBlockCertificate
#assert_standard_axioms TypeIIModEightCertificates.reindexCertificate
#assert_standard_axioms TypeIIModEightCertificates.equivPermutationMatrix
#assert_standard_axioms TypeIIModEightCertificates.equivPermutationMatrix_transpose
#assert_standard_axioms TypeIIModEightCertificates.equivPermutationMatrix_mul_symm
#assert_standard_axioms TypeIIModEightCertificates.equivPermutationMatrix_symm_mul
#assert_standard_axioms TypeIIModEightCertificates.equivPermutationMatrix_mul_apply
#assert_standard_axioms TypeIIModEightCertificates.mul_equivPermutationMatrix_apply
#assert_standard_axioms TypeIIModEightCertificates.equivPermutationMatrix_congruence_reindex
#assert_standard_axioms TypeIIModEightCertificates.reindexSelfCertificate
#assert_standard_axioms TypeIIModEightCertificates.sumBlockMatrix_eq_fromBlocks
#assert_standard_axioms TypeIIModEightCertificates.finBlockCertificate
#assert_standard_axioms TypeIIModEightCertificates.blockSumMatrix_map_zmodEight
#assert_standard_axioms TypeIIModEightCertificates.finTwoSumFinTwoEquiv
#assert_standard_axioms TypeIIModEightCertificates.reindex_sumBlock_A_A_eq_AA
#assert_standard_axioms TypeIIModEightCertificates.submatrix_AA_eq_sumBlock_A_A
#assert_standard_axioms TypeIIModEightCertificates.submatrix_HH_eq_sumBlock_H_H
#assert_standard_axioms TypeIIModEightCertificates.aaCancellationSumCertificate
#assert_standard_axioms TypeIIModEightCertificates.finFourSumFinFourEquiv
#assert_standard_axioms TypeIIModEightCertificates.reindex_sumBlock_HH_HH_eq_H4
#assert_standard_axioms TypeIIModEightCertificates.submatrix_H4_eq_sumBlock_HH_HH
