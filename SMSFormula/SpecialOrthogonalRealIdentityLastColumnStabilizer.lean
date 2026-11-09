import SMSFormula.SpecialOrthogonalRealIdentityLastColumnSurjective

/-!
# The lower-rank identity last-column stabilizer

This module identifies the identity-vector fiber of the last-column map on
`SO(n + 1)` with the identity-form special orthogonal group in rank `n`.

Fiber membership first forces both the final column and final row to be the
last standard coordinate. The remaining upper-left block is therefore a
determinant-one orthogonal matrix. Conversely, adjoining a final identity
coordinate embeds every rank-`n` special orthogonal matrix in the fiber.
These constructions are inverse, and the block embedding gives a
multiplicative equivalence with a subgroup whose carrier is exactly the
fiber.

No topology, Haar measure, quotient disintegration, or volume recurrence is
used.
-/

open scoped BigOperators Matrix

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

variable (n : ℕ)

abbrev identitySpecialOrthogonalRankGroup (n : ℕ) :=
  specialFormPreservingMatrixSubgroup
    (1 : Matrix (Fin n) (Fin n) ℝ)

def identitySpecialOrthogonalUpperLeftBlock
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  A.submatrix Fin.castSucc Fin.castSucc

def identitySpecialOrthogonalLastBlockMatrix
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))

@[simp]
theorem identitySpecialOrthogonalLastBlockMatrix_castSucc_castSucc
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    identitySpecialOrthogonalLastBlockMatrix n A i.castSucc j.castSucc =
      A i j := by
  simp [identitySpecialOrthogonalLastBlockMatrix, Matrix.reindex_apply,
    Matrix.fromBlocks]

@[simp]
theorem identitySpecialOrthogonalLastBlockMatrix_castSucc_last
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    identitySpecialOrthogonalLastBlockMatrix n A i.castSucc (Fin.last n) =
      0 := by
  simp [identitySpecialOrthogonalLastBlockMatrix, Matrix.reindex_apply,
    Matrix.fromBlocks]

@[simp]
theorem identitySpecialOrthogonalLastBlockMatrix_last_castSucc
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    identitySpecialOrthogonalLastBlockMatrix n A (Fin.last n) j.castSucc =
      0 := by
  simp [identitySpecialOrthogonalLastBlockMatrix, Matrix.reindex_apply,
    Matrix.fromBlocks]

@[simp]
theorem identitySpecialOrthogonalLastBlockMatrix_last_last
    (A : Matrix (Fin n) (Fin n) ℝ) :
    identitySpecialOrthogonalLastBlockMatrix n A (Fin.last n) (Fin.last n) =
      1 := by
  simp [identitySpecialOrthogonalLastBlockMatrix, Matrix.reindex_apply,
    Matrix.fromBlocks]

@[simp]
theorem identitySpecialOrthogonalUpperLeftBlock_lastBlockMatrix
    (A : Matrix (Fin n) (Fin n) ℝ) :
    identitySpecialOrthogonalUpperLeftBlock n
      (identitySpecialOrthogonalLastBlockMatrix n A) = A := by
  ext i j
  simp [identitySpecialOrthogonalUpperLeftBlock]

theorem identitySpecialOrthogonalLastBlockMatrix_det
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (identitySpecialOrthogonalLastBlockMatrix n A).det = A.det := by
  rw [identitySpecialOrthogonalLastBlockMatrix, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁]
  simp

theorem identitySpecialOrthogonalLastColumnFiber_finalRow
    (g : identitySpecialOrthogonalGroup n)
    (hg : g ∈ identitySpecialOrthogonalLastColumnFiber n)
    (j : Fin (n + 1)) :
    g.1.1.1 (Fin.last n) j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (Fin.last n) j := by
  have hpres : g.1.1.1ᵀ * g.1.1.1 = 1 := by
    have h := g.1.2
    change g.1.1.1ᵀ * 1 * g.1.1.1 = 1 at h
    simpa only [Matrix.mul_one] using h
  have hcol :=
    (mem_identitySpecialOrthogonalLastColumnFiber_iff n g).mp hg
  have hentry := congrArg
    (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      A (Fin.last n) j) hpres
  change
    (∑ x : Fin (n + 1),
      g.1.1.1 x (Fin.last n) * g.1.1.1 x j) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (Fin.last n) j at hentry
  simp_rw [hcol] at hentry
  simpa [Matrix.one_apply] using hentry

theorem identitySpecialOrthogonalLastColumnFiber_eq_lastBlockMatrix
    (g : identitySpecialOrthogonalGroup n)
    (hg : g ∈ identitySpecialOrthogonalLastColumnFiber n) :
    g.1.1.1 =
      identitySpecialOrthogonalLastBlockMatrix n
        (identitySpecialOrthogonalUpperLeftBlock n g.1.1.1) := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          rw [identitySpecialOrthogonalLastColumnFiber_finalRow n g hg]
          simp
      | cast j =>
          rw [identitySpecialOrthogonalLastColumnFiber_finalRow n g hg]
          simp only [Matrix.one_apply,
            if_neg (Fin.castSucc_ne_last j).symm]
          symm
          exact identitySpecialOrthogonalLastBlockMatrix_last_castSucc n _ j
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          rw [(mem_identitySpecialOrthogonalLastColumnFiber_iff n g).mp hg]
          simp
      | cast j =>
          simp [identitySpecialOrthogonalUpperLeftBlock]

theorem identitySpecialOrthogonalUpperLeftBlock_transpose_mul_self
    (g : identitySpecialOrthogonalGroup n)
    (hg : g ∈ identitySpecialOrthogonalLastColumnFiber n) :
    (identitySpecialOrthogonalUpperLeftBlock n g.1.1.1)ᵀ *
        identitySpecialOrthogonalUpperLeftBlock n g.1.1.1 = 1 := by
  ext i j
  have hpres : g.1.1.1ᵀ * g.1.1.1 = 1 := by
    have h := g.1.2
    change g.1.1.1ᵀ * 1 * g.1.1.1 = 1 at h
    simpa only [Matrix.mul_one] using h
  have hentry := congrArg
    (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      A i.castSucc j.castSucc) hpres
  change
    (∑ x : Fin n,
      g.1.1.1 x.castSucc i.castSucc *
        g.1.1.1 x.castSucc j.castSucc) = (1 : Matrix (Fin n) (Fin n) ℝ) i j
  change
    (∑ x : Fin (n + 1),
      g.1.1.1 x i.castSucc * g.1.1.1 x j.castSucc) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          i.castSucc j.castSucc at hentry
  rw [Fin.sum_univ_castSucc] at hentry
  have hrow := identitySpecialOrthogonalLastColumnFiber_finalRow n g hg
  have hlast_i : g.1.1.1 (Fin.last n) i.castSucc = 0 := by
    rw [hrow]
    exact Matrix.one_apply_ne (Fin.castSucc_ne_last i).symm
  have hlast_j : g.1.1.1 (Fin.last n) j.castSucc = 0 := by
    rw [hrow]
    exact Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm
  simpa [Matrix.one_apply, hlast_i, hlast_j] using hentry

theorem identitySpecialOrthogonalUpperLeftBlock_det
    (g : identitySpecialOrthogonalGroup n)
    (hg : g ∈ identitySpecialOrthogonalLastColumnFiber n) :
    (identitySpecialOrthogonalUpperLeftBlock n g.1.1.1).det = 1 := by
  calc
    (identitySpecialOrthogonalUpperLeftBlock n g.1.1.1).det =
        (identitySpecialOrthogonalLastBlockMatrix n
          (identitySpecialOrthogonalUpperLeftBlock n g.1.1.1)).det :=
      (identitySpecialOrthogonalLastBlockMatrix_det n _).symm
    _ = g.1.1.1.det := congrArg Matrix.det
      (identitySpecialOrthogonalLastColumnFiber_eq_lastBlockMatrix n g hg).symm
    _ = 1 :=
      (mem_specialFormPreservingMatrixSubgroup_iff _ g.1).mp g.2

theorem identitySpecialOrthogonalLastBlockMatrix_transpose_mul_self
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ * A = 1) :
    (identitySpecialOrthogonalLastBlockMatrix n A)ᵀ *
        identitySpecialOrthogonalLastBlockMatrix n A = 1 := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp
      | cast j =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp only [Matrix.transpose_apply,
            identitySpecialOrthogonalLastBlockMatrix_last_castSucc,
            identitySpecialOrthogonalLastBlockMatrix_castSucc_last,
            identitySpecialOrthogonalLastBlockMatrix_last_last,
            zero_mul, one_mul, Finset.sum_const_zero, zero_add]
          rw [Matrix.one_apply,
            if_neg (Fin.castSucc_ne_last j).symm]
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp
      | cast j =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          have hentry := congrArg
            (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hA
          simp only [Matrix.transpose_apply,
            identitySpecialOrthogonalLastBlockMatrix_castSucc_castSucc,
            identitySpecialOrthogonalLastBlockMatrix_last_castSucc,
            zero_mul, add_zero]
          rw [Matrix.one_apply]
          simp only [Fin.castSucc_inj]
          simpa [Matrix.mul_apply, Matrix.one_apply] using hentry

@[simp]
theorem identitySpecialOrthogonalLastBlockMatrix_one :
    identitySpecialOrthogonalLastBlockMatrix n
      (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last => simp
      | cast j =>
          simp only [identitySpecialOrthogonalLastBlockMatrix_last_castSucc,
            Matrix.one_apply,
            if_neg (Fin.castSucc_ne_last j).symm]
  | cast i =>
      cases j using Fin.lastCases with
      | last => simp
      | cast j => simp [Matrix.one_apply]

@[simp]
theorem identitySpecialOrthogonalLastBlockMatrix_mul
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    identitySpecialOrthogonalLastBlockMatrix n (A * B) =
      identitySpecialOrthogonalLastBlockMatrix n A *
        identitySpecialOrthogonalLastBlockMatrix n B := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases <;>
        rw [Matrix.mul_apply, Fin.sum_univ_castSucc] <;> simp
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp
      | cast j =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp [Matrix.mul_apply]

/-- Extract the lower-rank special orthogonal element from a member of the
last-column fiber. -/
def identitySpecialOrthogonalLastColumnFiberExtract
    (g : {g : identitySpecialOrthogonalGroup n //
      g ∈ identitySpecialOrthogonalLastColumnFiber n}) :
    identitySpecialOrthogonalRankGroup n := by
  let B := identitySpecialOrthogonalUpperLeftBlock n g.1.1.1.1
  let Bset : Matrix.specialOrthogonalMatrixSet
      (1 : Matrix (Fin n) (Fin n) ℝ) :=
    ⟨B,
      (Matrix.formPreservingConstraint_eq_zero_iff _ _).mpr
        (by simpa [B] using
          identitySpecialOrthogonalUpperLeftBlock_transpose_mul_self n g.1 g.2),
      identitySpecialOrthogonalUpperLeftBlock_det n g.1 g.2⟩
  exact specialOrthogonalMatrixSetToSpecialSubgroup _ Bset

@[simp]
theorem coe_identitySpecialOrthogonalLastColumnFiberExtract
    (g : {g : identitySpecialOrthogonalGroup n //
      g ∈ identitySpecialOrthogonalLastColumnFiber n}) :
    (identitySpecialOrthogonalLastColumnFiberExtract n g).1.1.1 =
      identitySpecialOrthogonalUpperLeftBlock n g.1.1.1.1 :=
  rfl

/-- Embed a lower-rank identity-form special orthogonal element by adjoining a
fixed final coordinate. -/
def identitySpecialOrthogonalLastColumnFiberEmbedGroup
    (h : identitySpecialOrthogonalRankGroup n) :
    identitySpecialOrthogonalGroup n := by
  let A := identitySpecialOrthogonalLastBlockMatrix n h.1.1.1
  have hsmall : h.1.1.1ᵀ * h.1.1.1 = 1 := by
    have hh := h.1.2
    change h.1.1.1ᵀ * 1 * h.1.1.1 = 1 at hh
    simpa only [Matrix.mul_one] using hh
  let Aset : Matrix.specialOrthogonalMatrixSet
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
    ⟨A,
      (Matrix.formPreservingConstraint_eq_zero_iff _ _).mpr
        (by simpa [A] using
          identitySpecialOrthogonalLastBlockMatrix_transpose_mul_self n _ hsmall),
      by
        change
          (identitySpecialOrthogonalLastBlockMatrix n h.1.1.1).det = 1
        rw [identitySpecialOrthogonalLastBlockMatrix_det]
        exact (mem_specialFormPreservingMatrixSubgroup_iff _ h.1).mp h.2⟩
  exact specialOrthogonalMatrixSetToSpecialSubgroup _ Aset

@[simp]
theorem coe_identitySpecialOrthogonalLastColumnFiberEmbedGroup
    (h : identitySpecialOrthogonalRankGroup n) :
    (identitySpecialOrthogonalLastColumnFiberEmbedGroup n h).1.1.1 =
      identitySpecialOrthogonalLastBlockMatrix n h.1.1.1 :=
  rfl

theorem identitySpecialOrthogonalLastColumnFiberEmbedGroup_mem
    (h : identitySpecialOrthogonalRankGroup n) :
    identitySpecialOrthogonalLastColumnFiberEmbedGroup n h ∈
      identitySpecialOrthogonalLastColumnFiber n := by
  rw [mem_identitySpecialOrthogonalLastColumnFiber_iff]
  intro i
  cases i using Fin.lastCases <;> simp

def identitySpecialOrthogonalLastColumnFiberEmbed
    (h : identitySpecialOrthogonalRankGroup n) :
    {g : identitySpecialOrthogonalGroup n //
      g ∈ identitySpecialOrthogonalLastColumnFiber n} :=
  ⟨identitySpecialOrthogonalLastColumnFiberEmbedGroup n h,
    identitySpecialOrthogonalLastColumnFiberEmbedGroup_mem n h⟩

theorem identitySpecialOrthogonalLastColumnFiberExtract_embed
    (h : identitySpecialOrthogonalRankGroup n) :
    identitySpecialOrthogonalLastColumnFiberExtract n
      (identitySpecialOrthogonalLastColumnFiberEmbed n h) = h := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact identitySpecialOrthogonalUpperLeftBlock_lastBlockMatrix n h.1.1.1

theorem identitySpecialOrthogonalLastColumnFiberEmbed_extract
    (g : {g : identitySpecialOrthogonalGroup n //
      g ∈ identitySpecialOrthogonalLastColumnFiber n}) :
    identitySpecialOrthogonalLastColumnFiberEmbed n
      (identitySpecialOrthogonalLastColumnFiberExtract n g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact
    (identitySpecialOrthogonalLastColumnFiber_eq_lastBlockMatrix n g.1 g.2).symm

/-- The identity-vector fiber is algebraically equivalent, as a type, to the
identity-form special orthogonal group in one lower rank. -/
def identitySpecialOrthogonalLastColumnFiberEquiv :
    identitySpecialOrthogonalRankGroup n ≃
      {g : identitySpecialOrthogonalGroup n //
        g ∈ identitySpecialOrthogonalLastColumnFiber n} where
  toFun := identitySpecialOrthogonalLastColumnFiberEmbed n
  invFun := identitySpecialOrthogonalLastColumnFiberExtract n
  left_inv := identitySpecialOrthogonalLastColumnFiberExtract_embed n
  right_inv := identitySpecialOrthogonalLastColumnFiberEmbed_extract n

/-- Block embedding is multiplicative. -/
def identitySpecialOrthogonalLastColumnFiberEmbedHom :
    identitySpecialOrthogonalRankGroup n →*
      identitySpecialOrthogonalGroup n where
  toFun := identitySpecialOrthogonalLastColumnFiberEmbedGroup n
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simp
  map_mul' h k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simp

theorem identitySpecialOrthogonalLastColumnFiberEmbedHom_injective :
    Function.Injective
      (identitySpecialOrthogonalLastColumnFiberEmbedHom n) := by
  intro h k hhk
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have hmatrix := congrArg
    (fun g : identitySpecialOrthogonalGroup n =>
      identitySpecialOrthogonalUpperLeftBlock n g.1.1.1) hhk
  change
    identitySpecialOrthogonalUpperLeftBlock n
        (identitySpecialOrthogonalLastBlockMatrix n h.1.1.1) =
      identitySpecialOrthogonalUpperLeftBlock n
        (identitySpecialOrthogonalLastBlockMatrix n k.1.1.1) at hmatrix
  simpa using hmatrix

/-- The block-embedded lower-rank group, as a subgroup of the ambient
identity-form special orthogonal group. -/
def identitySpecialOrthogonalLastColumnStabilizerSubgroup :
    Subgroup (identitySpecialOrthogonalGroup n) :=
  (identitySpecialOrthogonalLastColumnFiberEmbedHom n).range

theorem mem_identitySpecialOrthogonalLastColumnStabilizerSubgroup_iff
    (g : identitySpecialOrthogonalGroup n) :
    g ∈ identitySpecialOrthogonalLastColumnStabilizerSubgroup n ↔
      g ∈ identitySpecialOrthogonalLastColumnFiber n := by
  constructor
  · rintro ⟨h, rfl⟩
    exact identitySpecialOrthogonalLastColumnFiberEmbedGroup_mem n h
  · intro hg
    refine ⟨identitySpecialOrthogonalLastColumnFiberExtract n ⟨g, hg⟩, ?_⟩
    exact congrArg Subtype.val
      (identitySpecialOrthogonalLastColumnFiberEmbed_extract n ⟨g, hg⟩)

/-- The lower-rank identity-form special orthogonal group is multiplicatively
equivalent to the last-column stabilizer subgroup. -/
def identitySpecialOrthogonalLastColumnStabilizerMulEquiv :
    identitySpecialOrthogonalRankGroup n ≃*
      identitySpecialOrthogonalLastColumnStabilizerSubgroup n :=
  MonoidHom.ofInjective
    (f := identitySpecialOrthogonalLastColumnFiberEmbedHom n)
    (identitySpecialOrthogonalLastColumnFiberEmbedHom_injective n)

end PositiveDefiniteIntegralLattice
