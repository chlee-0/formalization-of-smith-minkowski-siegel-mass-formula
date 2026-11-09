import SMSFormula.Applications.Unimodular.Gram
import Mathlib.Data.Real.StarOrdered

/-!
# Concrete seed lattices for unimodular mass applications

This module starts the seed-lattice layer with the odd unimodular identity
lattice and the rank-eight even E8 Cartan lattice.
-/

noncomputable section

open Matrix BigOperators

namespace PositiveDefiniteIntegralLattice

/-- The identity integral lattice with stored quadratic matrix `I_n`. -/
def identityLattice (n : ℕ) : PositiveDefiniteIntegralLattice n where
  pairingMatrix := 1
  form_symm := by simp
  form_posDef := by
    simpa using (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef)

@[simp] theorem identityLattice_pairingMatrix (n : ℕ) :
    (identityLattice n).pairingMatrix = 1 := rfl

theorem identityLattice_isUnimodular (n : ℕ) :
    (identityLattice n).IsUnimodular := by
  simp [IsUnimodular, pairingDeterminant]

theorem identityLattice_quadForm_single_one {n : ℕ} (i : Fin n) :
    (identityLattice n).quadForm (Pi.single i (1 : ℤ)) = 1 := by
  rw [(identityLattice n).quadForm_eq_dotProduct]
  simp [identityLattice]

theorem identityLattice_hasOddNorm {n : ℕ} (hn : 0 < n) :
    (identityLattice n).HasOddNorm := by
  let i : Fin n := ⟨0, hn⟩
  exact ⟨Pi.single i (1 : ℤ), by simp [identityLattice_quadForm_single_one]⟩

theorem identityLattice_not_hasEvenNorms {n : ℕ} (hn : 0 < n) :
    ¬ (identityLattice n).HasEvenNorms :=
  (identityLattice n).not_hasEvenNorms_of_hasOddNorm
    (identityLattice_hasOddNorm hn)

/-- Every rank-zero integral lattice is globally isometric to the identity
seed.  The matrix equality is vacuous in rank zero. -/
theorem isGlobalIsometry_identityLattice_zero (L : PositiveDefiniteIntegralLattice 0) :
    L.IsGlobalIsometry (identityLattice 0) := by
  refine ⟨1, isUnit_one, ?_⟩
  ext i j
  fin_cases i

/-- Every classically unimodular rank-one integral lattice is globally
isometric to the identity seed. -/
theorem isGlobalIsometry_identityLattice_one_of_isUnimodular
    (L : PositiveDefiniteIntegralLattice 1) (hL : L.IsUnimodular) :
    L.IsGlobalIsometry (identityLattice 1) := by
  refine ⟨1, isUnit_one, ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  have hdiag : L.pairingMatrix 0 0 = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using hL
  simp [identityLattice, hdiag]

/-- The usual E8 Cartan matrix, used here as the stored quadratic matrix
`q(x)=xᵀGx`. -/
def e8CartanMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0, 0, 0;
    0, -1, 2, -1, 0, 0, 0, -1;
    0, 0, -1, 2, -1, 0, 0, 0;
    0, 0, 0, -1, 2, -1, 0, 0;
    0, 0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, 0, -1, 2, 0;
    0, 0, -1, 0, 0, 0, 0, 2]

/-- An explicit integral inverse of the E8 Cartan matrix. -/
def e8CartanInverseMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 7, 10, 8, 6, 4, 2, 5;
    7, 14, 20, 16, 12, 8, 4, 10;
    10, 20, 30, 24, 18, 12, 6, 15;
    8, 16, 24, 20, 15, 10, 5, 12;
    6, 12, 18, 15, 12, 8, 4, 9;
    4, 8, 12, 10, 8, 6, 3, 6;
    2, 4, 6, 5, 4, 3, 2, 3;
    5, 10, 15, 12, 9, 6, 3, 8]

theorem e8CartanMatrix_isSymm : e8CartanMatrix.IsSymm := by
  decide

private def e8LDLVector (x : Fin 8 → ℝ) : Fin 8 → ℝ
  | 0 => x 0 - (1 / 2) * x 1
  | 1 => x 1 - (2 / 3) * x 2
  | 2 => x 2 - (3 / 4) * x 3 - (3 / 4) * x 7
  | 3 => x 3 - (4 / 5) * x 4 - (3 / 5) * x 7
  | 4 => x 4 - (5 / 6) * x 5 - (1 / 2) * x 7
  | 5 => x 5 - (6 / 7) * x 6 - (3 / 7) * x 7
  | 6 => x 6 - (3 / 8) * x 7
  | 7 => x 7

private def e8LDLWeight : Fin 8 → ℝ
  | 0 => 2
  | 1 => 3 / 2
  | 2 => 4 / 3
  | 3 => 5 / 4
  | 4 => 6 / 5
  | 5 => 7 / 6
  | 6 => 8 / 7
  | 7 => 1 / 8

private lemma e8LDLWeight_pos (i : Fin 8) : 0 < e8LDLWeight i := by
  fin_cases i <;> norm_num [e8LDLWeight]

private lemma e8LDLVector_ne_zero_of_ne_zero {x : Fin 8 → ℝ} (hx : x ≠ 0) :
    e8LDLVector x ≠ 0 := by
  intro hy
  apply hx
  funext i
  have h0 := congr_fun hy 0
  have h1 := congr_fun hy 1
  have h2 := congr_fun hy 2
  have h3 := congr_fun hy 3
  have h4 := congr_fun hy 4
  have h5 := congr_fun hy 5
  have h6 := congr_fun hy 6
  have h7 := congr_fun hy 7
  fin_cases i <;> simp [e8LDLVector] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢ <;> linarith

private lemma e8CartanMatrix_quadratic_eq_ldl (x : Fin 8 → ℝ) :
    x ⬝ᵥ (e8CartanMatrix.map (Int.cast : ℤ → ℝ)).mulVec x =
      ∑ i : Fin 8, e8LDLWeight i * (e8LDLVector x i) ^ 2 := by
  simp [Fin.sum_univ_eight, e8CartanMatrix, e8LDLVector, e8LDLWeight,
    dotProduct, mulVec]
  ring_nf

theorem e8CartanMatrix_posDef :
    (e8CartanMatrix.map (Int.cast : ℤ → ℝ)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?hherm ?hpos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [e8CartanMatrix]
  · intro x hx
    rw [show star x = x by ext i; simp]
    rw [e8CartanMatrix_quadratic_eq_ldl]
    have hy : e8LDLVector x ≠ 0 := e8LDLVector_ne_zero_of_ne_zero hx
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    refine Finset.sum_pos' (s := Finset.univ) ?hnonneg ?hex
    · intro j hj
      exact mul_nonneg (le_of_lt (e8LDLWeight_pos j)) (sq_nonneg _)
    · exact ⟨i, Finset.mem_univ i,
        mul_pos (e8LDLWeight_pos i) (sq_pos_of_ne_zero hi)⟩

/-- The rank-eight E8 integral lattice. -/
def e8Lattice : PositiveDefiniteIntegralLattice 8 where
  pairingMatrix := e8CartanMatrix
  form_symm := e8CartanMatrix_isSymm
  form_posDef := e8CartanMatrix_posDef

@[simp] theorem e8Lattice_pairingMatrix :
    e8Lattice.pairingMatrix = e8CartanMatrix := rfl

theorem e8CartanMatrix_mul_inverse :
    e8CartanMatrix * e8CartanInverseMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_eight, e8CartanMatrix, e8CartanInverseMatrix, Matrix.mul_apply]

theorem e8CartanMatrix_det_eq_one : e8CartanMatrix.det = 1 := by
  have hdet := congrArg Matrix.det e8CartanMatrix_mul_inverse
  have hmul : e8CartanMatrix.det * e8CartanInverseMatrix.det = 1 := by
    simpa [Matrix.det_mul] using hdet
  exact Int.eq_one_of_mul_eq_one_right
    (le_of_lt (by simpa [e8Lattice, pairingDeterminant] using e8Lattice.pairingDeterminant_pos)) hmul

theorem e8Lattice_isUnimodular : e8Lattice.IsUnimodular := by
  simpa [IsUnimodular, pairingDeterminant, e8Lattice] using e8CartanMatrix_det_eq_one

theorem e8Lattice_quadForm_even (x : Fin 8 → ℤ) : Even (e8Lattice.quadForm x) := by
  rw [e8Lattice.quadForm_eq_dotProduct]
  refine ⟨x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 - x 1 * x 2 + x 2 ^ 2 - x 2 * x 3 -
      x 2 * x 7 + x 3 ^ 2 - x 3 * x 4 + x 4 ^ 2 - x 4 * x 5 +
      x 5 ^ 2 - x 5 * x 6 + x 6 ^ 2 + x 7 ^ 2, ?_⟩
  simp [Fin.sum_univ_eight, e8Lattice, e8CartanMatrix, dotProduct, mulVec]
  ring

theorem e8Lattice_hasEvenNorms : e8Lattice.HasEvenNorms := by
  intro x
  exact e8Lattice_quadForm_even x

variable {m n : ℕ}

/-- Orthogonal block sum of two stored quadratic matrices, reindexed from
`Fin m ⊕ Fin n` to `Fin (m+n)`. -/
def blockSumMatrix {R : Type*} [Zero R]
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A 0 0 B)

/-- Scalar extension to `ℝ` commutes with the orthogonal block sum. -/
theorem blockSumMatrix_map_real
    (A : Matrix (Fin m) (Fin m) ℤ) (B : Matrix (Fin n) (Fin n) ℤ) :
    (blockSumMatrix A B).map (Int.cast : ℤ → ℝ) =
      blockSumMatrix (A.map (Int.cast : ℤ → ℝ)) (B.map (Int.cast : ℤ → ℝ)) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [blockSumMatrix]

/-- The block sum of symmetric lattice matrices is symmetric. -/
theorem blockSumMatrix_isSymm (L : PositiveDefiniteIntegralLattice m) (M : PositiveDefiniteIntegralLattice n) :
    (blockSumMatrix L.pairingMatrix M.pairingMatrix).IsSymm := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [blockSumMatrix, L.form_symm.apply, M.form_symm.apply]

/-- The real quadratic value of a block sum splits as the sum of the two block
quadratic values. -/
theorem dotProduct_blockSumMatrix_real
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin (m + n) → ℝ) :
    x ⬝ᵥ (blockSumMatrix A B).mulVec x =
      (fun i : Fin m => x (Fin.castAdd n i)) ⬝ᵥ
        (A.mulVec (fun i : Fin m => x (Fin.castAdd n i))) +
      (fun i : Fin n => x (Fin.natAdd m i)) ⬝ᵥ
        (B.mulVec (fun i : Fin n => x (Fin.natAdd m i))) := by
  simp [blockSumMatrix, Matrix.mulVec, dotProduct, ← finSumFinEquiv.sum_comp,
    Fintype.sum_sum_type]

private lemma blockSum_left_or_right_ne_zero {x : Fin (m + n) → ℝ} (hx : x ≠ 0) :
    (fun i : Fin m => x (Fin.castAdd n i)) ≠ 0 ∨
      (fun i : Fin n => x (Fin.natAdd m i)) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hx
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i => exact congrFun h.1 i
  | inr i => exact congrFun h.2 i

/-- The orthogonal block sum of two positive-definite integral lattices is
positive definite. -/
theorem blockSumMatrix_posDef (L : PositiveDefiniteIntegralLattice m) (M : PositiveDefiniteIntegralLattice n) :
    ((blockSumMatrix L.pairingMatrix M.pairingMatrix).map (Int.cast : ℤ → ℝ)).PosDef := by
  rw [blockSumMatrix_map_real]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?hherm ?hpos
  · ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;>
      simp [blockSumMatrix, Matrix.conjTranspose_apply, L.form_symm.apply, M.form_symm.apply]
  · intro x hx
    rw [show star x = x by ext i; simp]
    rw [dotProduct_blockSumMatrix_real]
    rcases blockSum_left_or_right_ne_zero (m := m) (n := n) hx with hleft | hright
    · exact add_pos_of_pos_of_nonneg (L.form_posDef.dotProduct_mulVec_pos hleft)
        (M.form_posDef.posSemidef.dotProduct_mulVec_nonneg _)
    · exact add_pos_of_nonneg_of_pos
        (L.form_posDef.posSemidef.dotProduct_mulVec_nonneg _)
        (M.form_posDef.dotProduct_mulVec_pos hright)

/-- Orthogonal block sum of two integral lattices. -/
def blockSumLattice (L : PositiveDefiniteIntegralLattice m) (M : PositiveDefiniteIntegralLattice n) :
    PositiveDefiniteIntegralLattice (m + n) where
  pairingMatrix := blockSumMatrix L.pairingMatrix M.pairingMatrix
  form_symm := blockSumMatrix_isSymm L M
  form_posDef := blockSumMatrix_posDef L M

@[simp] theorem blockSumLattice_pairingMatrix (L : PositiveDefiniteIntegralLattice m)
    (M : PositiveDefiniteIntegralLattice n) :
    (blockSumLattice L M).pairingMatrix = blockSumMatrix L.pairingMatrix M.pairingMatrix := rfl

/-- Determinant of an orthogonal block sum. -/
theorem blockSumMatrix_det (A : Matrix (Fin m) (Fin m) ℤ)
    (B : Matrix (Fin n) (Fin n) ℤ) :
    (blockSumMatrix A B).det = A.det * B.det := by
  rw [blockSumMatrix, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/-- Schulze--Pillot determinant of a lattice block sum. -/
theorem blockSumLattice_pairingDeterminant (L : PositiveDefiniteIntegralLattice m) (M : PositiveDefiniteIntegralLattice n) :
    (blockSumLattice L M).pairingDeterminant = L.pairingDeterminant * M.pairingDeterminant := by
  simp [pairingDeterminant, blockSumLattice, blockSumMatrix_det]

/-- Classical unimodularity is preserved by orthogonal block sums. -/
theorem blockSumLattice_isUnimodular {L : PositiveDefiniteIntegralLattice m} {M : PositiveDefiniteIntegralLattice n}
    (hL : L.IsUnimodular) (hM : M.IsUnimodular) :
    (blockSumLattice L M).IsUnimodular := by
  rw [IsUnimodular, blockSumLattice_pairingDeterminant, hL, hM, mul_one]

/-- The quadratic form of a lattice block sum splits on the coordinate blocks. -/
theorem blockSumLattice_quadForm
    (L : PositiveDefiniteIntegralLattice m) (M : PositiveDefiniteIntegralLattice n) (x : Fin (m + n) → ℤ) :
    (blockSumLattice L M).quadForm x =
      L.quadForm (fun i : Fin m => x (Fin.castAdd n i)) +
      M.quadForm (fun i : Fin n => x (Fin.natAdd m i)) := by
  rw [(blockSumLattice L M).quadForm_eq_dotProduct, L.quadForm_eq_dotProduct,
    M.quadForm_eq_dotProduct]
  simp [blockSumLattice, blockSumMatrix, Matrix.mulVec, dotProduct,
    ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]

/-- Type II parity is preserved by orthogonal block sums. -/
theorem blockSumLattice_hasEvenNorms {L : PositiveDefiniteIntegralLattice m} {M : PositiveDefiniteIntegralLattice n}
    (hL : L.HasEvenNorms) (hM : M.HasEvenNorms) :
    (blockSumLattice L M).HasEvenNorms := by
  intro x
  rw [blockSumLattice_quadForm]
  exact Even.add (hL _) (hM _)

/-- A Type I left summand makes the block sum Type I. -/
theorem blockSumLattice_hasOddNorm_left {L : PositiveDefiniteIntegralLattice m} {M : PositiveDefiniteIntegralLattice n}
    (hL : L.HasOddNorm) :
    (blockSumLattice L M).HasOddNorm := by
  rcases hL with ⟨x, hx⟩
  refine ⟨fun i => Sum.elim x 0 (finSumFinEquiv.symm i), ?_⟩
  rw [blockSumLattice_quadForm]
  have hzero : Even (M.quadForm 0) := by
    rw [M.quadForm_eq_dotProduct]
    exact ⟨0, by simp⟩
  simpa using hx.add_even hzero

/-- A Type I right summand makes the block sum Type I. -/
theorem blockSumLattice_hasOddNorm_right {L : PositiveDefiniteIntegralLattice m} {M : PositiveDefiniteIntegralLattice n}
    (hM : M.HasOddNorm) :
    (blockSumLattice L M).HasOddNorm := by
  rcases hM with ⟨y, hy⟩
  refine ⟨fun i => Sum.elim 0 y (finSumFinEquiv.symm i), ?_⟩
  rw [blockSumLattice_quadForm]
  have hzero : Even (L.quadForm 0) := by
    rw [L.quadForm_eq_dotProduct]
    exact ⟨0, by simp⟩
  simpa using hzero.add_odd hy

/-- Reindex an integral lattice along an equivalence of coordinate types. -/
def reindexLattice (e : Fin m ≃ Fin n) (L : PositiveDefiniteIntegralLattice m) : PositiveDefiniteIntegralLattice n where
  pairingMatrix := Matrix.reindex e e L.pairingMatrix
  form_symm := by
    ext i j
    simp [Matrix.reindex_apply, L.form_symm.apply]
  form_posDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?hherm ?hpos
    · ext i j
      simp [Matrix.reindex_apply, Matrix.conjTranspose_apply, L.form_symm.apply]
    · intro x hx
      rw [show star x = x by ext i; simp]
      let y : Fin m → ℝ := fun i => x (e i)
      have hy : y ≠ 0 := by
        intro hy
        apply hx
        funext j
        obtain ⟨i, rfl⟩ := e.surjective j
        exact congrFun hy i
      have hquad : x ⬝ᵥ (((Matrix.reindex e e L.pairingMatrix).map (Int.cast : ℤ → ℝ)).mulVec x) =
          y ⬝ᵥ ((L.pairingMatrix.map (Int.cast : ℤ → ℝ)).mulVec y) := by
        simp [y, Matrix.reindex_apply, Matrix.mulVec, dotProduct, ← e.sum_comp]
      rw [hquad]
      exact L.form_posDef.dotProduct_mulVec_pos hy

@[simp] theorem reindexLattice_pairingMatrix (e : Fin m ≃ Fin n) (L : PositiveDefiniteIntegralLattice m) :
    (reindexLattice e L).pairingMatrix = Matrix.reindex e e L.pairingMatrix := rfl

theorem reindexLattice_pairingDeterminant (e : Fin m ≃ Fin n) (L : PositiveDefiniteIntegralLattice m) :
    (reindexLattice e L).pairingDeterminant = L.pairingDeterminant := by
  simp [pairingDeterminant, reindexLattice]

theorem reindexLattice_isUnimodular (e : Fin m ≃ Fin n) {L : PositiveDefiniteIntegralLattice m}
    (hL : L.IsUnimodular) :
    (reindexLattice e L).IsUnimodular := by
  simpa [IsUnimodular, reindexLattice_pairingDeterminant] using hL

theorem reindexLattice_quadForm (e : Fin m ≃ Fin n) (L : PositiveDefiniteIntegralLattice m)
    (x : Fin n → ℤ) :
    (reindexLattice e L).quadForm x = L.quadForm (fun i : Fin m => x (e i)) := by
  rw [(reindexLattice e L).quadForm_eq_dotProduct, L.quadForm_eq_dotProduct]
  simp [reindexLattice, Matrix.reindex_apply, Matrix.mulVec, dotProduct, ← e.sum_comp]

theorem reindexLattice_hasEvenNorms (e : Fin m ≃ Fin n) {L : PositiveDefiniteIntegralLattice m}
    (hL : L.HasEvenNorms) :
    (reindexLattice e L).HasEvenNorms := by
  intro x
  rw [reindexLattice_quadForm]
  exact hL _

theorem reindexLattice_hasOddNorm (e : Fin m ≃ Fin n) {L : PositiveDefiniteIntegralLattice m}
    (hL : L.HasOddNorm) :
    (reindexLattice e L).HasOddNorm := by
  rcases hL with ⟨x, hx⟩
  refine ⟨fun j => x (e.symm j), ?_⟩
  rw [reindexLattice_quadForm]
  simpa using hx

/-- The zero-rank identity lattice is even. -/
theorem identityLattice_zero_hasEvenNorms : (identityLattice 0).HasEvenNorms := by
  intro x
  have hx : x = 0 := by
    funext i
    exact Fin.elim0 i
  rw [hx]
  rw [(identityLattice 0).quadForm_eq_dotProduct]
  exact ⟨0, by simp⟩

/-- A recursive Type II unimodular seed in every rank `8*k`. -/
def typeIISeed : (k : ℕ) → PositiveDefiniteIntegralLattice (8 * k)
  | 0 => identityLattice 0
  | k + 1 =>
      reindexLattice (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
        (blockSumLattice (typeIISeed k) e8Lattice)

theorem typeIISeed_isUnimodular : ∀ k : ℕ, (typeIISeed k).IsUnimodular
  | 0 => by
      simpa [typeIISeed] using identityLattice_isUnimodular 0
  | k + 1 => by
      simp [typeIISeed, reindexLattice_isUnimodular,
        blockSumLattice_isUnimodular, typeIISeed_isUnimodular k,
        e8Lattice_isUnimodular]

theorem typeIISeed_hasEvenNorms : ∀ k : ℕ, (typeIISeed k).HasEvenNorms
  | 0 => by
      simpa [typeIISeed] using identityLattice_zero_hasEvenNorms
  | k + 1 => by
      simp [typeIISeed, reindexLattice_hasEvenNorms,
        blockSumLattice_hasEvenNorms, typeIISeed_hasEvenNorms k,
        e8Lattice_hasEvenNorms]

/-- The constructive direction of the Type II rank condition: every rank
`8*k` has a classically unimodular Type II seed.  The converse obstruction is a
separate theorem. -/
theorem exists_isUnimodular_hasEvenNorms_of_dvd_eight {n : ℕ} (h8 : 8 ∣ n) :
    ∃ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular ∧ L.HasEvenNorms := by
  rcases h8 with ⟨k, rfl⟩
  exact ⟨typeIISeed k, typeIISeed_isUnimodular k, typeIISeed_hasEvenNorms k⟩

end PositiveDefiniteIntegralLattice
