import SMSFormula.Applications.Unimodular.StableIdentityComparison.StableCertificate
import SMSFormula.StandardAxiomsGuard

/-!
# Recursive stable-coordinate matrices

This file turns the explicit rank `9`, `17`, and `25` Voskresenskii stable
matrices into a single closed-form recursive pattern.  In the definitions below,
each E8 block updates the shared
norm-one line together with that block by the rank-nine stable matrix, and the
inverse updates the blocks in reverse order.
-/

noncomputable section
open Matrix PositiveDefiniteIntegralLattice UnimodularMass

namespace StableIdentityComparisonStableRecursive

set_option maxHeartbeats 5000000

/-- Rank-nine stable matrix reduced modulo four. -/
def stableNineModFour : Matrix (Fin 9) (Fin 9) (ZMod 4) :=
  StableIdentityComparisonCertificate.stableNine.map (Int.cast : ℤ → ZMod 4)

/-- Rank-nine inverse stable matrix reduced modulo four. -/
def stableNineInverseModFour : Matrix (Fin 9) (Fin 9) (ZMod 4) :=
  StableIdentityComparisonCertificate.stableNineInverse.map (Int.cast : ℤ → ZMod 4)

/-- Safe natural-number indexing into the rank-nine stable matrix. -/
def stableNineEntry (i j : ℕ) : ZMod 4 :=
  if hi : i < 9 then
    if hj : j < 9 then stableNineModFour ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

/-- Safe natural-number indexing into the rank-nine inverse stable matrix. -/
def stableNineInverseEntry (i j : ℕ) : ZMod 4 :=
  if hi : i < 9 then
    if hj : j < 9 then stableNineInverseModFour ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

/-- The first column of the rank-nine stable matrix is the norm-one line. -/
theorem stableNineEntry_col_zero (r : Fin 9) :
    stableNineEntry r.val 0 = 1 := by
  fin_cases r <;> decide

/-- The first row of the rank-nine inverse stable matrix is the all-ones characteristic row. -/
theorem stableNineInverseEntry_row_zero (s : Fin 9) :
    stableNineInverseEntry 0 s.val = 1 := by
  fin_cases s <;> decide

/-- The tail form of the checked rank-nine right-inverse identity.  This is the
coefficient identity used by each E8-block contribution in the recursive product. -/
theorem stableNine_tail_right_inverse (r s : Fin 9) :
    stableNineEntry r.val 0 * stableNineInverseEntry 0 s.val +
      (∑ a : Fin 8, stableNineEntry r.val (a.val + 1) *
        stableNineInverseEntry (a.val + 1) s.val) =
        (1 : Matrix (Fin 9) (Fin 9) (ZMod 4)) r s := by
  have h := congr_fun
    (congr_fun StableIdentityComparisonCertificate.stableNine_right_inverse_four r) s
  rw [Matrix.mul_apply] at h
  rw [Fin.sum_univ_succ] at h
  simpa [stableNineModFour, stableNineInverseModFour, stableNineEntry,
    stableNineInverseEntry] using h

/-- A normalized tail form of the checked rank-nine right-inverse identity. -/
theorem stableNine_tail_right_inverse_one_add (r s : Fin 9) :
    1 + (∑ a : Fin 8, stableNineEntry r.val (a.val + 1) *
      stableNineInverseEntry (a.val + 1) s.val) =
        (1 : Matrix (Fin 9) (Fin 9) (ZMod 4)) r s := by
  simpa [stableNineEntry_col_zero r, stableNineInverseEntry_row_zero s] using
    stableNine_tail_right_inverse r s

/-- The tail form of the checked rank-nine left-inverse identity. -/
theorem stableNine_tail_left_inverse (r s : Fin 9) :
    stableNineInverseEntry r.val 0 * stableNineEntry 0 s.val +
      (∑ a : Fin 8, stableNineInverseEntry r.val (a.val + 1) *
        stableNineEntry (a.val + 1) s.val) =
        (1 : Matrix (Fin 9) (Fin 9) (ZMod 4)) r s := by
  have h := congr_fun
    (congr_fun StableIdentityComparisonCertificate.stableNine_left_inverse_four r) s
  rw [Matrix.mul_apply] at h
  rw [Fin.sum_univ_succ] at h
  simpa [stableNineModFour, stableNineInverseModFour, stableNineEntry,
    stableNineInverseEntry] using h

/-- The zeroth row of the rank-nine left-inverse identity as a column-sum identity for the forward matrix. -/
theorem stableNine_tail_left_inverse_row_zero (s : Fin 9) :
    stableNineEntry 0 s.val +
      (∑ a : Fin 8, stableNineEntry (a.val + 1) s.val) =
        (1 : Matrix (Fin 9) (Fin 9) (ZMod 4)) (0 : Fin 9) s := by
  have h := stableNine_tail_left_inverse (0 : Fin 9) s
  have h0 : stableNineInverseEntry (0 : Fin 9).val 0 = 1 :=
    stableNineInverseEntry_row_zero (0 : Fin 9)
  have ha : ∀ a : Fin 8, stableNineInverseEntry (0 : Fin 9).val (a.val + 1) = 1 := by
    intro a
    exact stableNineInverseEntry_row_zero ⟨a.val + 1, by omega⟩
  have htail : (∑ a : Fin 8,
      stableNineInverseEntry (0 : Fin 9).val (a.val + 1) * stableNineEntry (a.val + 1) s.val) =
        ∑ a : Fin 8, stableNineEntry (a.val + 1) s.val := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ha a]
    simp
  rw [h0, htail] at h
  simpa using h

/-- The zeroth column of the rank-nine left-inverse identity as a row-sum identity for the inverse matrix. -/
theorem stableNine_tail_left_inverse_col_zero (r : Fin 9) :
    stableNineInverseEntry r.val 0 +
      (∑ a : Fin 8, stableNineInverseEntry r.val (a.val + 1)) =
        (1 : Matrix (Fin 9) (Fin 9) (ZMod 4)) r (0 : Fin 9) := by
  have h := stableNine_tail_left_inverse r (0 : Fin 9)
  have h0 : stableNineEntry 0 (0 : Fin 9).val = 1 := stableNineEntry_col_zero (0 : Fin 9)
  have ha : ∀ a : Fin 8, stableNineEntry (a.val + 1) (0 : Fin 9).val = 1 := by
    intro a
    exact stableNineEntry_col_zero ⟨a.val + 1, by omega⟩
  have htail : (∑ a : Fin 8,
      stableNineInverseEntry r.val (a.val + 1) * stableNineEntry (a.val + 1) (0 : Fin 9).val) =
        ∑ a : Fin 8, stableNineInverseEntry r.val (a.val + 1) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ha a]
    simp
  rw [h0, htail] at h
  simpa using h

/-- Block number for a non-line coordinate in `(line, E8 blocks)` coordinates. -/
def blockOf (t : ℕ) : ℕ := (t - 1) / 8

/-- Local rank-nine coordinate for a non-line coordinate. -/
def localOf (t : ℕ) : ℕ := (t - 1) % 8 + 1

/-- Embed the old coordinates into the next recursive rank. -/
def oldCoord (k : ℕ) (i : Fin (8 * k + 1)) : Fin (8 * (k + 1) + 1) :=
  ⟨i.val, by omega⟩

/-- The coordinate in the new E8 block of the next recursive rank. -/
def newBlockCoord (k : ℕ) (a : Fin 8) : Fin (8 * (k + 1) + 1) :=
  ⟨8 * k + 1 + a.val, by omega⟩

/-- Closed-form entry of the recursive forward stable matrix. -/
def stableRecursiveEntry (k : ℕ) (i j : Fin (8 * k + 1)) : ZMod 4 :=
  if i.val = 0 then
    if j.val = 0 then 1 else stableNineEntry 0 (localOf j.val)
  else if j.val = 0 then
    1
  else
    let bi := blockOf i.val
    let bj := blockOf j.val
    let ai := localOf i.val
    let aj := localOf j.val
    if bj < bi then stableNineEntry 0 aj
    else if bj = bi then stableNineEntry ai aj
    else 0

/-- Recursive forward stable matrix on a norm-one line plus `k` E8 blocks. -/
def stableRecursive (k : ℕ) :
    Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4) :=
  fun i j => stableRecursiveEntry k i j

/-- Closed-form entry of the recursive inverse stable matrix. -/
def stableRecursiveInverseEntry (k : ℕ) (i j : Fin (8 * k + 1)) : ZMod 4 :=
  if i.val = 0 then
    1
  else
    let bi := blockOf i.val
    let ai := localOf i.val
    if j.val = 0 then stableNineInverseEntry ai 0
    else
      let bj := blockOf j.val
      let aj := localOf j.val
      if bj < bi then 0
      else if bj = bi then stableNineInverseEntry ai aj
      else stableNineInverseEntry ai 0

/-- Recursive inverse stable matrix on a norm-one line plus `k` E8 blocks. -/
def stableRecursiveInverse (k : ℕ) :
    Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4) :=
  fun i j => stableRecursiveInverseEntry k i j

/-- The old/new coordinate split for the next recursive rank. -/
noncomputable def oldNewEquiv (k : ℕ) :
    (Fin (8 * k + 1) ⊕ Fin 8) ≃ Fin (8 * (k + 1) + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The old/new split sends old coordinates to `oldCoord`. -/
theorem oldNewEquiv_inl (k : ℕ) (i : Fin (8 * k + 1)) :
    oldNewEquiv k (Sum.inl i) = oldCoord k i := by
  ext
  rw [oldNewEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply]
  simp [oldCoord]

/-- The old/new split sends the right summand to the new E8 block. -/
theorem oldNewEquiv_inr (k : ℕ) (a : Fin 8) :
    oldNewEquiv k (Sum.inr a) = newBlockCoord k a := by
  ext
  rw [oldNewEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply]
  simp [newBlockCoord, Fin.natAdd]

/-- Split a sum over the next recursive rank into old coordinates and the new E8 block. -/
theorem sum_old_newBlock (k : ℕ) (f : Fin (8 * (k + 1) + 1) → ZMod 4) :
    (∑ x : Fin (8 * (k + 1) + 1), f x) =
      (∑ x : Fin (8 * k + 1), f (oldCoord k x)) +
      (∑ a : Fin 8, f (newBlockCoord k a)) := by
  rw [← Fintype.sum_equiv (oldNewEquiv k) (fun y => f (oldNewEquiv k y)) f (by intro y; rfl)]
  rw [Fintype.sum_sum_type]
  simp [oldNewEquiv_inl, oldNewEquiv_inr]

/-- Split a modulo-eight sum over the next recursive rank into old coordinates and the new E8 block. -/
theorem sum_old_newBlock_zmodEight (k : ℕ) (f : Fin (8 * (k + 1) + 1) → ZMod 8) :
    (∑ x : Fin (8 * (k + 1) + 1), f x) =
      (∑ x : Fin (8 * k + 1), f (oldCoord k x)) +
      (∑ a : Fin 8, f (newBlockCoord k a)) := by
  rw [← Fintype.sum_equiv (oldNewEquiv k) (fun y => f (oldNewEquiv k y)) f (by intro y; rfl)]
  rw [Fintype.sum_sum_type]
  simp [oldNewEquiv_inl, oldNewEquiv_inr]

/-- Matrix products over the next recursive rank split into old-coordinate and new-block contributions. -/
theorem mul_apply_old_newBlock (k : ℕ)
    (A B : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4))
    (i j : Fin (8 * (k + 1) + 1)) :
    (A * B) i j =
      (∑ x : Fin (8 * k + 1), A i (oldCoord k x) * B (oldCoord k x) j) +
      (∑ a : Fin 8, A i (newBlockCoord k a) * B (newBlockCoord k a) j) := by
  rw [Matrix.mul_apply, sum_old_newBlock]

/-- The identity matrix is compatible with the old-coordinate embedding. -/
theorem one_oldCoord_oldCoord (k : ℕ) (i j : Fin (8 * k + 1)) :
    (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4))
        (oldCoord k i) (oldCoord k j) =
      (1 : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4)) i j := by
  simp [Matrix.one_apply, oldCoord, Fin.ext_iff]

/-- Old and new recursive coordinates are distinct in the identity matrix. -/
theorem one_oldCoord_newBlock (k : ℕ) (i : Fin (8 * k + 1)) (a : Fin 8) :
    (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4))
        (oldCoord k i) (newBlockCoord k a) = 0 := by
  simp [Matrix.one_apply, oldCoord, newBlockCoord, Fin.ext_iff]
  omega

/-- New and old recursive coordinates are distinct in the identity matrix. -/
theorem one_newBlock_oldCoord (k : ℕ) (a : Fin 8) (j : Fin (8 * k + 1)) :
    (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4))
        (newBlockCoord k a) (oldCoord k j) = 0 := by
  simp [Matrix.one_apply, oldCoord, newBlockCoord, Fin.ext_iff]
  omega

/-- The identity matrix on a new E8 block is the tail of the rank-nine identity matrix. -/
theorem one_newBlock_newBlock (k : ℕ) (a b : Fin 8) :
    (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4))
        (newBlockCoord k a) (newBlockCoord k b) =
      (1 : Matrix (Fin 9) (Fin 9) (ZMod 4)) ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ := by
  simp [Matrix.one_apply, newBlockCoord, Fin.ext_iff]

/-- The forward recursive matrix restricts to the previous rank on old rows and columns. -/
theorem stableRecursive_old_old (k : ℕ) (i j : Fin (8 * k + 1)) :
    stableRecursive (k + 1) (oldCoord k i) (oldCoord k j) = stableRecursive k i j := by
  simp [stableRecursive, stableRecursiveEntry, oldCoord]

/-- The old line row sees the new block through the rank-nine line row. -/
theorem stableRecursive_line_newBlock (k : ℕ) (a : Fin 8) :
    stableRecursive (k + 1) (oldCoord k 0) (newBlockCoord k a) =
      stableNineEntry 0 (a.val + 1) := by
  have hloc : localOf (8 * k + 1 + a.val) = a.val + 1 := by simp [localOf]
  simp [stableRecursive, stableRecursiveEntry, oldCoord, newBlockCoord, hloc]

/-- Old non-line rows have zero entries in the new forward block. -/
theorem stableRecursive_old_ne_zero_newBlock (k : ℕ) (i : Fin (8 * k + 1))
    (a : Fin 8) (hi : i.val ≠ 0) :
    stableRecursive (k + 1) (oldCoord k i) (newBlockCoord k a) = 0 := by
  have hlt : ¬ blockOf (8 * k + 1 + a.val) < blockOf i.val := by
    have hi_lt : i.val < 8 * k + 1 := i.isLt
    simp [blockOf]
    omega
  have hne : ¬ blockOf (8 * k + 1 + a.val) = blockOf i.val := by
    have hi_lt : i.val < 8 * k + 1 := i.isLt
    simp [blockOf]
    omega
  simp [stableRecursive, stableRecursiveEntry, oldCoord, newBlockCoord, hi, hlt, hne]

/-- A new forward-block row restricts to the old line row on old columns. -/
theorem stableRecursive_newBlock_old (k : ℕ) (a : Fin 8) (j : Fin (8 * k + 1)) :
    stableRecursive (k + 1) (newBlockCoord k a) (oldCoord k j) = stableRecursive k 0 j := by
  by_cases hj : j.val = 0
  · simp [stableRecursive, stableRecursiveEntry, oldCoord, newBlockCoord, hj]
  · have hlt : blockOf j.val < blockOf (8 * k + 1 + a.val) := by
      have hj_lt : j.val < 8 * k + 1 := j.isLt
      simp [blockOf]
      omega
    simp [stableRecursive, stableRecursiveEntry, oldCoord, newBlockCoord, hj, hlt]

/-- The new forward block itself is the E8 tail of the rank-nine stable matrix. -/
theorem stableRecursive_newBlock_newBlock (k : ℕ) (a b : Fin 8) :
    stableRecursive (k + 1) (newBlockCoord k a) (newBlockCoord k b) =
      stableNineEntry (a.val + 1) (b.val + 1) := by
  have hblk : blockOf (8 * k + 1 + a.val) = blockOf (8 * k + 1 + b.val) := by
    simp [blockOf]
    omega
  have hloca : localOf (8 * k + 1 + a.val) = a.val + 1 := by simp [localOf]
  have hlocb : localOf (8 * k + 1 + b.val) = b.val + 1 := by simp [localOf]
  simp [stableRecursive, stableRecursiveEntry, newBlockCoord, hblk, hloca, hlocb]

/-- The old-coordinate part of a vector in the next recursive rank. -/
def oldPart (k : ℕ) (x : Fin (8 * (k + 1) + 1) → ZMod 4) : Fin (8 * k + 1) → ZMod 4 :=
  fun i => x (oldCoord k i)

/-- The new E8 block part of a vector in the next recursive rank. -/
def newBlockPart (k : ℕ) (x : Fin (8 * (k + 1) + 1) → ZMod 4) : Fin 8 → ZMod 4 :=
  fun a => x (newBlockCoord k a)

/-- The rank-nine input obtained after the previous recursive blocks have updated the shared line. -/
def recursiveNineInput (k : ℕ) (x : Fin (8 * (k + 1) + 1) → ZMod 4) : Fin 9 → ZMod 4 :=
  Fin.cons ((stableRecursive k).mulVec (oldPart k x) 0) (newBlockPart k x)

/-- The old non-line output coordinates are unchanged by adjoining the next E8 block. -/
theorem stableRecursive_mulVec_old_ne_zero (k : ℕ)
    (x : Fin (8 * (k + 1) + 1) → ZMod 4) (i : Fin (8 * k + 1)) (hi : i.val ≠ 0) :
    (stableRecursive (k + 1)).mulVec x (oldCoord k i) =
      (stableRecursive k).mulVec (oldPart k x) i := by
  rw [Matrix.mulVec, dotProduct, sum_old_newBlock]
  simp_rw [stableRecursive_old_old]
  have hnew : (∑ a : Fin 8,
      stableRecursive (k + 1) (oldCoord k i) (newBlockCoord k a) * x (newBlockCoord k a)) = 0 := by
    simp [stableRecursive_old_ne_zero_newBlock, hi]
  rw [hnew]
  simp [oldPart, Matrix.mulVec, dotProduct]

/-- The old line output is the line coordinate of the rank-nine update applied to the previous line and the new block. -/
theorem stableRecursive_mulVec_old_zero (k : ℕ)
    (x : Fin (8 * (k + 1) + 1) → ZMod 4) :
    (stableRecursive (k + 1)).mulVec x (oldCoord k 0) =
      stableNineModFour.mulVec (recursiveNineInput k x) 0 := by
  rw [Matrix.mulVec, dotProduct, sum_old_newBlock]
  simp_rw [stableRecursive_old_old, stableRecursive_line_newBlock]
  rw [show stableNineModFour.mulVec (recursiveNineInput k x) 0 =
      stableNineEntry 0 0 * (stableRecursive k).mulVec (oldPart k x) 0 +
        (∑ a : Fin 8, stableNineEntry 0 (a.val + 1) * x (newBlockCoord k a)) by
    simp [stableNineModFour, stableNineEntry, recursiveNineInput, newBlockPart,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]]
  rw [show stableNineEntry 0 0 = 1 by decide]
  simp [oldPart, Matrix.mulVec, dotProduct]

/-- New-block output coordinates are the E8-tail coordinates of the rank-nine update. -/
theorem stableRecursive_mulVec_newBlock (k : ℕ)
    (x : Fin (8 * (k + 1) + 1) → ZMod 4) (a : Fin 8) :
    (stableRecursive (k + 1)).mulVec x (newBlockCoord k a) =
      stableNineModFour.mulVec (recursiveNineInput k x) ⟨a.val + 1, by omega⟩ := by
  rw [Matrix.mulVec, dotProduct, sum_old_newBlock]
  simp_rw [stableRecursive_newBlock_old, stableRecursive_newBlock_newBlock]
  have ha : a.val + 1 < 9 := by omega
  rw [show stableNineModFour.mulVec (recursiveNineInput k x) ⟨a.val + 1, by omega⟩ =
      stableNineEntry (a.val + 1) 0 * (stableRecursive k).mulVec (oldPart k x) 0 +
        (∑ b : Fin 8, stableNineEntry (a.val + 1) (b.val + 1) * x (newBlockCoord k b)) by
    simp [stableNineModFour, stableNineEntry, recursiveNineInput, newBlockPart,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, ha]]
  rw [stableNineEntry_col_zero ⟨a.val + 1, by omega⟩]
  simp [oldPart, Matrix.mulVec, dotProduct]

/-- The old tail coordinates inside the successor seed tail. -/
def oldTailPart (k : ℕ) (v : Fin (8 * (k + 1)) → ZMod 4) : Fin (8 * k) → ZMod 4 :=
  fun i => v ⟨i.val, by omega⟩

/-- The new E8-block tail coordinates inside the successor seed tail. -/
def newTailPart (k : ℕ) (v : Fin (8 * (k + 1)) → ZMod 4) : Fin 8 → ZMod 4 :=
  fun a => v ⟨8 * k + a.val, by omega⟩

/-- The quadratic contraction of a block-sum matrix splits over the two blocks. -/
theorem blockSumMatrix_quadratic_split_zmodEight {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin (m + n) → ZMod 8) :
    (∑ i : Fin (m + n), v i *
      (((blockSumMatrix A B).map (Int.cast : ℤ → ZMod 8)).mulVec v i)) =
      (∑ i : Fin m, v (Fin.castAdd n i) *
        ((A.map (Int.cast : ℤ → ZMod 8)).mulVec
          (fun j : Fin m => v (Fin.castAdd n j)) i)) +
      (∑ i : Fin n, v (Fin.natAdd m i) *
        ((B.map (Int.cast : ℤ → ZMod 8)).mulVec
          (fun j : Fin n => v (Fin.natAdd m j)) i)) := by
  simp [blockSumMatrix, Matrix.mulVec, dotProduct, ← finSumFinEquiv.sum_comp,
    Fintype.sum_sum_type]

/-- The stored seed norm splits over the recursive old tail and the newly appended E8 block. -/
theorem seedNormModEight_succ_split (k : ℕ)
    (v : Fin (8 * (k + 1)) → ZMod 4) :
    StableIdentityComparisonSeedNormAdapter.seedNormModEight (k + 1) v =
      StableIdentityComparisonSeedNormAdapter.seedNormModEight k (oldTailPart k v) +
        StableIdentityComparisonCertificate.e8Norm
          (fun a : Fin 8 => zmodFourLiftToZModEight (newTailPart k v a)) := by
  unfold StableIdentityComparisonSeedNormAdapter.seedNormModEight
    oldTailPart newTailPart StableIdentityComparisonCertificate.e8Norm
  simp only [typeIISeed, e8Lattice, blockSumLattice_pairingMatrix, reindexLattice_pairingMatrix,
    Matrix.reindex_apply, finCongr_symm]
  simpa [Matrix.mulVec, dotProduct] using
    (blockSumMatrix_quadratic_split_zmodEight
      (m := 8 * k) (n := 8) (typeIISeed k).pairingMatrix e8CartanMatrix
      (fun i : Fin (8 * k + 8) => zmodFourLiftToZModEight (v (finCongr (by omega) i))))

/-- The diagonal modulo-eight quadratic form splits over old coordinates and the new E8 block. -/
theorem identityQuadraticModEight_old_newBlock (k : ℕ)
    (y : Fin (8 * (k + 1) + 1) → ZMod 4) :
    identityQuadraticModEight y =
      (∑ i : Fin (8 * k + 1), zmodFourLiftToZModEight (y (oldCoord k i)) ^ 2) +
      (∑ a : Fin 8, zmodFourLiftToZModEight (y (newBlockCoord k a)) ^ 2) := by
  simpa [identityQuadraticModEight] using
    (sum_old_newBlock_zmodEight k (fun i => zmodFourLiftToZModEight (y i) ^ 2))

/-- The successor output quadratic splits into the old non-line coordinates and the rank-nine update. -/
theorem stableRecursive_identityQuadratic_succ_split (k : ℕ)
    (x : Fin (8 * (k + 1) + 1) → ZMod 4) :
    identityQuadraticModEight ((stableRecursive (k + 1)).mulVec x) =
      (∑ i : Fin (8 * k),
        zmodFourLiftToZModEight ((stableRecursive k).mulVec (oldPart k x) i.succ) ^ 2) +
      identityQuadraticModEight (stableNineModFour.mulVec (recursiveNineInput k x)) := by
  rw [identityQuadraticModEight_old_newBlock]
  rw [identityQuadraticModEight]
  rw [Fin.sum_univ_succ]
  simp_rw [stableRecursive_mulVec_old_zero]
  have holdTail : (∑ i : Fin (8 * k),
      zmodFourLiftToZModEight ((stableRecursive (k + 1)).mulVec x (oldCoord k i.succ)) ^ 2) =
      ∑ i : Fin (8 * k),
        zmodFourLiftToZModEight ((stableRecursive k).mulVec (oldPart k x) i.succ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [stableRecursive_mulVec_old_ne_zero]
    simp
  have hnewTail : (∑ a : Fin 8,
      zmodFourLiftToZModEight ((stableRecursive (k + 1)).mulVec x (newBlockCoord k a)) ^ 2) =
      ∑ a : Fin 8,
        zmodFourLiftToZModEight (stableNineModFour.mulVec (recursiveNineInput k x) ⟨a.val + 1, by omega⟩) ^ 2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [stableRecursive_mulVec_newBlock]
  have hnine : (∑ j : Fin 9,
      zmodFourLiftToZModEight (stableNineModFour.mulVec (recursiveNineInput k x) j) ^ 2) =
      zmodFourLiftToZModEight (stableNineModFour.mulVec (recursiveNineInput k x) 0) ^ 2 +
        ∑ a : Fin 8,
          zmodFourLiftToZModEight (stableNineModFour.mulVec (recursiveNineInput k x) ⟨a.val + 1, by omega⟩) ^ 2 := by
    rw [Fin.sum_univ_succ]
    congr 1
  rw [holdTail, hnewTail, hnine]
  ring_nf

/-- The fixed-line quadratic identity is preserved by adjoining one recursive E8 block. -/
theorem stableRecursive_quadratic_identity_succ_step (k : ℕ)
    (hQ : ∀ y : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight ((stableRecursive k).mulVec y) =
        StableIdentityFixedLine.lineNorm
          (StableIdentityComparisonSeedNormAdapter.seedNormModEight k) y)
    (x : Fin (8 * (k + 1) + 1) → ZMod 4) :
    identityQuadraticModEight ((stableRecursive (k + 1)).mulVec x) =
      StableIdentityFixedLine.lineNorm
        (StableIdentityComparisonSeedNormAdapter.seedNormModEight (k + 1)) x := by
  rw [stableRecursive_identityQuadratic_succ_split]
  rw [show identityQuadraticModEight (stableNineModFour.mulVec (recursiveNineInput k x)) =
      StableIdentityComparisonCertificate.onePlusE8NormModEight (recursiveNineInput k x) by
    simpa [stableNineModFour] using
      (StableIdentityComparisonCertificate.stableNine_identityQuadraticModEight_eq_onePlusE8Norm
        (recursiveNineInput k x))]
  have hOldRaw := hQ (oldPart k x)
  unfold identityQuadraticModEight StableIdentityFixedLine.lineNorm at hOldRaw
  rw [Fin.sum_univ_succ] at hOldRaw
  have hOld :
      (∑ i : Fin (8 * k),
          zmodFourLiftToZModEight ((stableRecursive k).mulVec (oldPart k x) i.succ) ^ 2) +
        zmodFourLiftToZModEight ((stableRecursive k).mulVec (oldPart k x) 0) ^ 2 =
        zmodFourLiftToZModEight (x 0) ^ 2 +
          StableIdentityComparisonSeedNormAdapter.seedNormModEight k
            (oldTailPart k (fun i : Fin (8 * (k + 1)) => x i.succ)) := by
    simpa [oldPart, oldTailPart, oldCoord, add_comm, add_left_comm, add_assoc] using hOldRaw
  unfold StableIdentityComparisonCertificate.onePlusE8NormModEight
  unfold StableIdentityFixedLine.lineNorm
  rw [seedNormModEight_succ_split]
  simp [newTailPart, newBlockPart, recursiveNineInput, newBlockCoord]
  rw [← add_assoc]
  rw [hOld]
  ring_nf

/-- The inverse recursive matrix restricts to the previous rank on old rows and columns. -/
theorem stableRecursiveInverse_old_old (k : ℕ) (i j : Fin (8 * k + 1)) :
    stableRecursiveInverse (k + 1) (oldCoord k i) (oldCoord k j) =
      stableRecursiveInverse k i j := by
  simp [stableRecursiveInverse, stableRecursiveInverseEntry, oldCoord]

/-- Old inverse rows see the new block as their old line column. -/
theorem stableRecursiveInverse_old_newBlock (k : ℕ) (i : Fin (8 * k + 1)) (a : Fin 8) :
    stableRecursiveInverse (k + 1) (oldCoord k i) (newBlockCoord k a) =
      stableRecursiveInverse k i 0 := by
  by_cases hi : i.val = 0
  · simp [stableRecursiveInverse, stableRecursiveInverseEntry, oldCoord, hi]
  · have hgt : ¬ blockOf (8 * k + 1 + a.val) < blockOf i.val := by
      have hi_lt : i.val < 8 * k + 1 := i.isLt
      simp [blockOf]
      omega
    have hne : ¬ blockOf (8 * k + 1 + a.val) = blockOf i.val := by
      have hi_lt : i.val < 8 * k + 1 := i.isLt
      simp [blockOf]
      omega
    simp [stableRecursiveInverse, stableRecursiveInverseEntry, oldCoord, newBlockCoord, hi, hgt, hne]

/-- The new inverse block line column is the rank-nine inverse tail line column. -/
theorem stableRecursiveInverse_newBlock_old_zero (k : ℕ) (a : Fin 8) :
    stableRecursiveInverse (k + 1) (newBlockCoord k a) (oldCoord k 0) =
      stableNineInverseEntry (a.val + 1) 0 := by
  have hloca : localOf (8 * k + 1 + a.val) = a.val + 1 := by simp [localOf]
  simp [stableRecursiveInverse, stableRecursiveInverseEntry, oldCoord, newBlockCoord, hloca]

/-- New inverse block rows vanish on old non-line columns. -/
theorem stableRecursiveInverse_newBlock_old_ne_zero (k : ℕ) (a : Fin 8)
    (j : Fin (8 * k + 1)) (hj : j.val ≠ 0) :
    stableRecursiveInverse (k + 1) (newBlockCoord k a) (oldCoord k j) = 0 := by
  have hlt : blockOf j.val < blockOf (8 * k + 1 + a.val) := by
    have hj_lt : j.val < 8 * k + 1 := j.isLt
    simp [blockOf]
    omega
  simp [stableRecursiveInverse, stableRecursiveInverseEntry, oldCoord, newBlockCoord, hj, hlt]

/-- The new inverse block itself is the E8 tail of the rank-nine inverse stable matrix. -/
theorem stableRecursiveInverse_newBlock_newBlock (k : ℕ) (a b : Fin 8) :
    stableRecursiveInverse (k + 1) (newBlockCoord k a) (newBlockCoord k b) =
      stableNineInverseEntry (a.val + 1) (b.val + 1) := by
  have hblk : blockOf (8 * k + 1 + a.val) = blockOf (8 * k + 1 + b.val) := by
    simp [blockOf]
    omega
  have hloca : localOf (8 * k + 1 + a.val) = a.val + 1 := by simp [localOf]
  have hlocb : localOf (8 * k + 1 + b.val) = b.val + 1 := by simp [localOf]
  simp [stableRecursiveInverse, stableRecursiveInverseEntry, newBlockCoord, hblk, hloca, hlocb]

/-- Forward-times-inverse on old rows and old columns reduces to the previous rank. -/
theorem stableRecursive_right_inverse_old_old (k : ℕ) (h : stableRecursive k * stableRecursiveInverse k = 1) (i j : Fin (8 * k + 1)) :
    (stableRecursive (k + 1) * stableRecursiveInverse (k + 1)) (oldCoord k i) (oldCoord k j) =
      (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4)) (oldCoord k i) (oldCoord k j) := by
  rw [mul_apply_old_newBlock]
  simp_rw [stableRecursive_old_old, stableRecursiveInverse_old_old]
  have hij := congr_fun (congr_fun h i) j
  rw [Matrix.mul_apply] at hij
  rw [hij]
  rw [one_oldCoord_oldCoord]
  by_cases hi : i.val = 0
  · by_cases hj : j.val = 0
    · have hi0 : i = 0 := by ext; exact hi
      have hj0 : j = 0 := by ext; exact hj
      subst i
      subst j
      have htail := stableNine_tail_right_inverse_one_add (0 : Fin 9) (0 : Fin 9)
      simp at htail
      have hnew : (∑ a : Fin 8,
          stableRecursive (k + 1) (oldCoord k (0 : Fin (8 * k + 1))) (newBlockCoord k a) *
            stableRecursiveInverse (k + 1) (newBlockCoord k a) (oldCoord k (0 : Fin (8 * k + 1)))) = 0 := by
        simpa [stableRecursive_line_newBlock, stableRecursiveInverse_newBlock_old_zero] using htail
      rw [hnew]
      simp
    · have hnew : (∑ a : Fin 8,
          stableRecursive (k + 1) (oldCoord k i) (newBlockCoord k a) *
            stableRecursiveInverse (k + 1) (newBlockCoord k a) (oldCoord k j)) = 0 := by
        simp [hj, stableRecursiveInverse_newBlock_old_ne_zero]
      rw [hnew]
      simp [Matrix.one_apply]
  · have hnew : (∑ a : Fin 8,
        stableRecursive (k + 1) (oldCoord k i) (newBlockCoord k a) *
          stableRecursiveInverse (k + 1) (newBlockCoord k a) (oldCoord k j)) = 0 := by
      simp [stableRecursive_old_ne_zero_newBlock, hi]
    rw [hnew]
    simp

/-- Forward-times-inverse on old rows and new columns reduces to a rank-nine tail identity. -/
theorem stableRecursive_right_inverse_old_new (k : ℕ) (h : stableRecursive k * stableRecursiveInverse k = 1)
    (i : Fin (8 * k + 1)) (b : Fin 8) :
    (stableRecursive (k + 1) * stableRecursiveInverse (k + 1)) (oldCoord k i) (newBlockCoord k b) =
      (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4)) (oldCoord k i) (newBlockCoord k b) := by
  rw [mul_apply_old_newBlock]
  simp_rw [stableRecursive_old_old, stableRecursiveInverse_old_newBlock]
  have hi0prod := congr_fun (congr_fun h i) (0 : Fin (8 * k + 1))
  rw [Matrix.mul_apply] at hi0prod
  rw [hi0prod]
  rw [one_oldCoord_newBlock]
  by_cases hi : i.val = 0
  · have hi0 : i = 0 := by ext; exact hi
    subst i
    have htail := stableNine_tail_right_inverse_one_add (0 : Fin 9) ⟨b.val + 1, by omega⟩
    simp at htail
    simpa [stableRecursive_line_newBlock, stableRecursiveInverse_newBlock_newBlock, Matrix.one_apply] using htail
  · have hnew : (∑ a : Fin 8,
        stableRecursive (k + 1) (oldCoord k i) (newBlockCoord k a) *
          stableRecursiveInverse (k + 1) (newBlockCoord k a) (newBlockCoord k b)) = 0 := by
      simp [stableRecursive_old_ne_zero_newBlock, hi]
    rw [hnew]
    have hio : (1 : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4)) i 0 = 0 := by
      simp [Matrix.one_apply]
      intro heq
      exfalso
      exact hi (by simp [heq])
    simp [hio]

/-- Forward-times-inverse on new rows and old columns reduces to a rank-nine tail identity. -/
theorem stableRecursive_right_inverse_new_old (k : ℕ) (h : stableRecursive k * stableRecursiveInverse k = 1)
    (a : Fin 8) (j : Fin (8 * k + 1)) :
    (stableRecursive (k + 1) * stableRecursiveInverse (k + 1)) (newBlockCoord k a) (oldCoord k j) =
      (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4)) (newBlockCoord k a) (oldCoord k j) := by
  rw [mul_apply_old_newBlock]
  simp_rw [stableRecursive_newBlock_old, stableRecursiveInverse_old_old]
  have h0j := congr_fun (congr_fun h (0 : Fin (8 * k + 1))) j
  rw [Matrix.mul_apply] at h0j
  rw [h0j]
  rw [one_newBlock_oldCoord]
  by_cases hj : j.val = 0
  · have hj0 : j = 0 := by ext; exact hj
    subst j
    have htail := stableNine_tail_right_inverse_one_add ⟨a.val + 1, by omega⟩ (0 : Fin 9)
    simp at htail
    simpa [stableRecursive_newBlock_newBlock, stableRecursiveInverse_newBlock_old_zero,
      Matrix.one_apply] using htail
  · have hnew : (∑ b : Fin 8,
        stableRecursive (k + 1) (newBlockCoord k a) (newBlockCoord k b) *
          stableRecursiveInverse (k + 1) (newBlockCoord k b) (oldCoord k j)) = 0 := by
      simp [stableRecursiveInverse_newBlock_old_ne_zero, hj]
    rw [hnew]
    have h0jzero : (1 : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4)) 0 j = 0 := by
      simp [Matrix.one_apply]
      intro heq
      exfalso
      exact hj (by simp [← heq])
    simp [h0jzero]

/-- Forward-times-inverse on the new block is the rank-nine tail right-inverse identity. -/
theorem stableRecursive_right_inverse_new_new (k : ℕ) (h : stableRecursive k * stableRecursiveInverse k = 1)
    (a b : Fin 8) :
    (stableRecursive (k + 1) * stableRecursiveInverse (k + 1)) (newBlockCoord k a) (newBlockCoord k b) =
      (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4)) (newBlockCoord k a) (newBlockCoord k b) := by
  rw [mul_apply_old_newBlock]
  simp_rw [stableRecursive_newBlock_old, stableRecursiveInverse_old_newBlock]
  have h00 := congr_fun (congr_fun h (0 : Fin (8 * k + 1))) (0 : Fin (8 * k + 1))
  rw [Matrix.mul_apply] at h00
  rw [h00]
  rw [one_newBlock_newBlock]
  have htail := stableNine_tail_right_inverse_one_add ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩
  simpa [stableRecursive_newBlock_newBlock, stableRecursiveInverse_newBlock_newBlock, Matrix.one_apply] using htail

/-- Inverse-times-forward on old rows and old columns reduces to the previous rank. -/
theorem stableRecursive_left_inverse_old_old (k : ℕ) (h : stableRecursiveInverse k * stableRecursive k = 1) (i j : Fin (8 * k + 1)) :
    (stableRecursiveInverse (k + 1) * stableRecursive (k + 1)) (oldCoord k i) (oldCoord k j) =
      (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4)) (oldCoord k i) (oldCoord k j) := by
  rw [mul_apply_old_newBlock]
  simp_rw [stableRecursiveInverse_old_old, stableRecursive_old_old]
  have hij := congr_fun (congr_fun h i) j
  rw [Matrix.mul_apply] at hij
  rw [hij]
  rw [one_oldCoord_oldCoord]
  have hnew : (∑ a : Fin 8,
      stableRecursiveInverse (k + 1) (oldCoord k i) (newBlockCoord k a) *
        stableRecursive (k + 1) (newBlockCoord k a) (oldCoord k j)) = 0 := by
    simp_rw [stableRecursiveInverse_old_newBlock, stableRecursive_newBlock_old]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
    have h8 : ((8 : ℕ) : ZMod 4) = 0 := by decide
    rw [h8]
    simp
  rw [hnew]
  simp

/-- Inverse-times-forward on old rows and new columns reduces to the zeroth-row rank-nine left-inverse identity. -/
theorem stableRecursive_left_inverse_old_new (k : ℕ)
    (i : Fin (8 * k + 1)) (b : Fin 8) :
    (stableRecursiveInverse (k + 1) * stableRecursive (k + 1)) (oldCoord k i) (newBlockCoord k b) =
      (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4)) (oldCoord k i) (newBlockCoord k b) := by
  rw [mul_apply_old_newBlock]
  simp_rw [stableRecursiveInverse_old_old]
  rw [one_oldCoord_newBlock]
  have hsum := stableNine_tail_left_inverse_row_zero ⟨b.val + 1, by omega⟩
  have hold : (∑ x : Fin (8 * k + 1),
      stableRecursiveInverse k i x * stableRecursive (k + 1) (oldCoord k x) (newBlockCoord k b)) =
        stableRecursiveInverse k i 0 * stableNineEntry 0 (b.val + 1) := by
    rw [Fintype.sum_eq_single (0 : Fin (8*k+1))]
    · simp [stableRecursive_line_newBlock]
    · intro x hx
      have hxv : x.val ≠ 0 := by
        intro h0
        apply hx
        ext
        exact h0
      simp [stableRecursive_old_ne_zero_newBlock, hxv]
  rw [hold]
  simp_rw [stableRecursiveInverse_old_newBlock, stableRecursive_newBlock_newBlock]
  rw [← Finset.mul_sum]
  rw [← mul_add]
  have hz : stableNineEntry 0 (b.val + 1) +
      (∑ a : Fin 8, stableNineEntry (a.val + 1) (b.val + 1)) = 0 := by
    simpa [Matrix.one_apply] using hsum
  rw [hz]
  simp

/-- Inverse-times-forward on new rows and old columns reduces to the zeroth-column rank-nine left-inverse identity. -/
theorem stableRecursive_left_inverse_new_old (k : ℕ)
    (a : Fin 8) (j : Fin (8 * k + 1)) :
    (stableRecursiveInverse (k + 1) * stableRecursive (k + 1)) (newBlockCoord k a) (oldCoord k j) =
      (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4)) (newBlockCoord k a) (oldCoord k j) := by
  rw [mul_apply_old_newBlock]
  rw [one_newBlock_oldCoord]
  have hsum := stableNine_tail_left_inverse_col_zero ⟨a.val + 1, by omega⟩
  have hold : (∑ x : Fin (8 * k + 1),
      stableRecursiveInverse (k + 1) (newBlockCoord k a) (oldCoord k x) *
        stableRecursive (k + 1) (oldCoord k x) (oldCoord k j)) =
        stableNineInverseEntry (a.val + 1) 0 * stableRecursive k 0 j := by
    rw [Fintype.sum_eq_single (0 : Fin (8*k+1))]
    · simp [stableRecursiveInverse_newBlock_old_zero, stableRecursive_old_old]
    · intro x hx
      have hxv : x.val ≠ 0 := by
        intro h0
        apply hx
        ext
        exact h0
      simp [stableRecursiveInverse_newBlock_old_ne_zero, hxv]
  rw [hold]
  simp_rw [stableRecursiveInverse_newBlock_newBlock, stableRecursive_newBlock_old]
  rw [← Finset.sum_mul]
  rw [← add_mul]
  have hz : stableNineInverseEntry (a.val + 1) 0 +
      (∑ b : Fin 8, stableNineInverseEntry (a.val + 1) (b.val + 1)) = 0 := by
    simpa [Matrix.one_apply] using hsum
  rw [hz]
  simp

/-- Inverse-times-forward on the new block is the rank-nine tail left-inverse identity. -/
theorem stableRecursive_left_inverse_new_new (k : ℕ)
    (a b : Fin 8) :
    (stableRecursiveInverse (k + 1) * stableRecursive (k + 1)) (newBlockCoord k a) (newBlockCoord k b) =
      (1 : Matrix (Fin (8 * (k + 1) + 1)) (Fin (8 * (k + 1) + 1)) (ZMod 4)) (newBlockCoord k a) (newBlockCoord k b) := by
  rw [mul_apply_old_newBlock]
  rw [one_newBlock_newBlock]
  have hsum := stableNine_tail_left_inverse ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩
  have hold : (∑ x : Fin (8 * k + 1),
      stableRecursiveInverse (k + 1) (newBlockCoord k a) (oldCoord k x) *
        stableRecursive (k + 1) (oldCoord k x) (newBlockCoord k b)) =
        stableNineInverseEntry (a.val + 1) 0 * stableNineEntry 0 (b.val + 1) := by
    rw [Fintype.sum_eq_single (0 : Fin (8*k+1))]
    · simp [stableRecursiveInverse_newBlock_old_zero, stableRecursive_line_newBlock]
    · intro x hx
      have hxv : x.val ≠ 0 := by
        intro h0
        apply hx
        ext
        exact h0
      simp [stableRecursiveInverse_newBlock_old_ne_zero, hxv]
  rw [hold]
  simp_rw [stableRecursiveInverse_newBlock_newBlock, stableRecursive_newBlock_newBlock]
  simpa using hsum

/-- The recursive forward matrix specializes to the checked rank-nine matrix. -/
theorem stableRecursive_one :
    stableRecursive 1 = stableNineModFour := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The recursive inverse matrix specializes to the checked rank-nine inverse. -/
theorem stableRecursiveInverse_one :
    stableRecursiveInverse 1 = stableNineInverseModFour := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The recursive matrices are inverse in the one-block base case. -/
theorem stableRecursive_right_inverse_one :
    stableRecursive 1 * stableRecursiveInverse 1 = 1 := by
  rw [stableRecursive_one, stableRecursiveInverse_one]
  exact StableIdentityComparisonCertificate.stableNine_right_inverse_four

/-- The recursive inverse matrices multiply back to the identity in the one-block base case. -/
theorem stableRecursive_left_inverse_one :
    stableRecursiveInverse 1 * stableRecursive 1 = 1 := by
  rw [stableRecursive_one, stableRecursiveInverse_one]
  exact StableIdentityComparisonCertificate.stableNine_left_inverse_four

/-- The forward recursive matrix is a right inverse one step higher if it was so in the previous rank. -/
theorem stableRecursive_right_inverse_succ (k : ℕ) (h : stableRecursive k * stableRecursiveInverse k = 1) :
    stableRecursive (k + 1) * stableRecursiveInverse (k + 1) = 1 := by
  ext i j
  cases hiei : (oldNewEquiv k).symm i with
  | inl i0 =>
      cases hjej : (oldNewEquiv k).symm j with
      | inl j0 =>
          have hi : i = oldCoord k i0 := by
            rw [← (oldNewEquiv k).apply_symm_apply i, hiei, oldNewEquiv_inl]
          have hj : j = oldCoord k j0 := by
            rw [← (oldNewEquiv k).apply_symm_apply j, hjej, oldNewEquiv_inl]
          rw [hi, hj]
          exact stableRecursive_right_inverse_old_old k h i0 j0
      | inr b =>
          have hi : i = oldCoord k i0 := by
            rw [← (oldNewEquiv k).apply_symm_apply i, hiei, oldNewEquiv_inl]
          have hj : j = newBlockCoord k b := by
            rw [← (oldNewEquiv k).apply_symm_apply j, hjej, oldNewEquiv_inr]
          rw [hi, hj]
          exact stableRecursive_right_inverse_old_new k h i0 b
  | inr a =>
      cases hjej : (oldNewEquiv k).symm j with
      | inl j0 =>
          have hi : i = newBlockCoord k a := by
            rw [← (oldNewEquiv k).apply_symm_apply i, hiei, oldNewEquiv_inr]
          have hj : j = oldCoord k j0 := by
            rw [← (oldNewEquiv k).apply_symm_apply j, hjej, oldNewEquiv_inl]
          rw [hi, hj]
          exact stableRecursive_right_inverse_new_old k h a j0
      | inr b =>
          have hi : i = newBlockCoord k a := by
            rw [← (oldNewEquiv k).apply_symm_apply i, hiei, oldNewEquiv_inr]
          have hj : j = newBlockCoord k b := by
            rw [← (oldNewEquiv k).apply_symm_apply j, hjej, oldNewEquiv_inr]
          rw [hi, hj]
          exact stableRecursive_right_inverse_new_new k h a b

/-- The recursive inverse matrix is a left inverse one step higher if it was so in the previous rank. -/
theorem stableRecursive_left_inverse_succ (k : ℕ) (h : stableRecursiveInverse k * stableRecursive k = 1) :
    stableRecursiveInverse (k + 1) * stableRecursive (k + 1) = 1 := by
  ext i j
  cases hiei : (oldNewEquiv k).symm i with
  | inl i0 =>
      cases hjej : (oldNewEquiv k).symm j with
      | inl j0 =>
          have hi : i = oldCoord k i0 := by
            rw [← (oldNewEquiv k).apply_symm_apply i, hiei, oldNewEquiv_inl]
          have hj : j = oldCoord k j0 := by
            rw [← (oldNewEquiv k).apply_symm_apply j, hjej, oldNewEquiv_inl]
          rw [hi, hj]
          exact stableRecursive_left_inverse_old_old k h i0 j0
      | inr b =>
          have hi : i = oldCoord k i0 := by
            rw [← (oldNewEquiv k).apply_symm_apply i, hiei, oldNewEquiv_inl]
          have hj : j = newBlockCoord k b := by
            rw [← (oldNewEquiv k).apply_symm_apply j, hjej, oldNewEquiv_inr]
          rw [hi, hj]
          exact stableRecursive_left_inverse_old_new k i0 b
  | inr a =>
      cases hjej : (oldNewEquiv k).symm j with
      | inl j0 =>
          have hi : i = newBlockCoord k a := by
            rw [← (oldNewEquiv k).apply_symm_apply i, hiei, oldNewEquiv_inr]
          have hj : j = oldCoord k j0 := by
            rw [← (oldNewEquiv k).apply_symm_apply j, hjej, oldNewEquiv_inl]
          rw [hi, hj]
          exact stableRecursive_left_inverse_new_old k a j0
      | inr b =>
          have hi : i = newBlockCoord k a := by
            rw [← (oldNewEquiv k).apply_symm_apply i, hiei, oldNewEquiv_inr]
          have hj : j = newBlockCoord k b := by
            rw [← (oldNewEquiv k).apply_symm_apply j, hjej, oldNewEquiv_inr]
          rw [hi, hj]
          exact stableRecursive_left_inverse_new_new k a b

/-- The recursive forward matrix is a right inverse to the recursive inverse in every positive rank. -/
theorem stableRecursive_right_inverse (k : ℕ) (hk : 0 < k) :
    stableRecursive k * stableRecursiveInverse k = 1 := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero => simpa using stableRecursive_right_inverse_one
      | succ k =>
          have hprev : stableRecursive (k + 1) * stableRecursiveInverse (k + 1) = 1 :=
            ih (by omega)
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            stableRecursive_right_inverse_succ (k + 1) hprev

/-- The recursive inverse matrix is a left inverse to the recursive forward matrix in every positive rank. -/
theorem stableRecursive_left_inverse (k : ℕ) (hk : 0 < k) :
    stableRecursiveInverse k * stableRecursive k = 1 := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero => simpa using stableRecursive_left_inverse_one
      | succ k =>
          have hprev : stableRecursiveInverse (k + 1) * stableRecursive (k + 1) = 1 :=
            ih (by omega)
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            stableRecursive_left_inverse_succ (k + 1) hprev

/-- Every recursive forward matrix sends the distinguished line to the all-odd characteristic vector. -/
theorem stableRecursive_mulVec_line (k : ℕ) :
    (stableRecursive k).mulVec (StableIdentityFixedLine.e (8 * k)) =
      StableIdentityComparison.characteristic (8 * k + 1) := by
  funext i
  simp [stableRecursive, stableRecursiveEntry, StableIdentityFixedLine.e,
    StableIdentityComparison.characteristic, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The exact remaining recursive identities needed to turn the closed-form
recursive matrices into a pointed stable certificate. -/
def certificateOfRecursiveIdentities (k : ℕ)
    (hUV : stableRecursive k * stableRecursiveInverse k = 1)
    (hVU : stableRecursiveInverse k * stableRecursive k = 1)
    (hQ : ∀ x : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight ((stableRecursive k).mulVec x) =
        StableIdentityFixedLine.lineNorm
          (StableIdentityComparisonSeedNormAdapter.seedNormModEight k) x) :
    StableIdentityComparisonStableCertificate.PointedStableCertificate k where
  U := stableRecursive k
  V := stableRecursiveInverse k
  hUV := hUV
  hVU := hVU
  hQ := hQ
  hw := stableRecursive_mulVec_line k

/-- If the recursive stable matrices satisfy their inverse and quadratic
identities in every positive rank, then the all-positive E8-power seed masses
follow through the existing certificate interface. -/
theorem all_positive_seed_mass_of_recursive_identities
    (hrec : ∀ k : ℕ, 0 < k →
      (stableRecursive k * stableRecursiveInverse k = 1) ∧
      (stableRecursiveInverse k * stableRecursive k = 1) ∧
      (∀ x : Fin (8 * k + 1) → ZMod 4,
        identityQuadraticModEight ((stableRecursive k).mulVec x) =
          StableIdentityFixedLine.lineNorm
            (StableIdentityComparisonSeedNormAdapter.seedNormModEight k) x))
    (k : ℕ) (hk : 0 < k) :
    (typeIISeed k).ordinaryGenusMass = typeIIConstant (8 * k) := by
  rcases hrec k hk with ⟨hUV, hVU, hQ⟩
  exact (certificateOfRecursiveIdentities k hUV hVU hQ).seed_mass k hk

/-- Literal genus-sum form of `all_positive_seed_mass_of_recursive_identities`. -/
theorem all_positive_seed_literal_sum_of_recursive_identities
    (hrec : ∀ k : ℕ, 0 < k →
      (stableRecursive k * stableRecursiveInverse k = 1) ∧
      (stableRecursiveInverse k * stableRecursive k = 1) ∧
      (∀ x : Fin (8 * k + 1) → ZMod 4,
        identityQuadraticModEight ((stableRecursive k).mulVec x) =
          StableIdentityFixedLine.lineNorm
            (StableIdentityComparisonSeedNormAdapter.seedNormModEight k) x))
    (k : ℕ) (hk : 0 < k) :
    (∑ A : (typeIISeed k).genus,
      ((Fintype.card (genusClassRepresentative (typeIISeed k) A).IsometryGroup : ℚ)⁻¹)) =
        typeIIConstant (8 * k) := by
  rcases hrec k hk with ⟨hUV, hVU, hQ⟩
  exact (certificateOfRecursiveIdentities k hUV hVU hQ).seed_literal_sum k hk

/-- If the recursive stable matrices satisfy the fixed-line quadratic identity in every positive rank,
then the all-positive E8-power seed masses follow; the two inverse-product identities are proved. -/
theorem all_positive_seed_mass_of_recursive_quadratic_identity
    (hQ : ∀ k : ℕ, 0 < k → ∀ x : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight ((stableRecursive k).mulVec x) =
        StableIdentityFixedLine.lineNorm
          (StableIdentityComparisonSeedNormAdapter.seedNormModEight k) x)
    (k : ℕ) (hk : 0 < k) :
    (typeIISeed k).ordinaryGenusMass = typeIIConstant (8 * k) := by
  exact all_positive_seed_mass_of_recursive_identities
    (fun k hk => ⟨stableRecursive_right_inverse k hk, stableRecursive_left_inverse k hk, hQ k hk⟩) k hk

/-- Literal genus-sum form of `all_positive_seed_mass_of_recursive_quadratic_identity`. -/
theorem all_positive_seed_literal_sum_of_recursive_quadratic_identity
    (hQ : ∀ k : ℕ, 0 < k → ∀ x : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight ((stableRecursive k).mulVec x) =
        StableIdentityFixedLine.lineNorm
          (StableIdentityComparisonSeedNormAdapter.seedNormModEight k) x)
    (k : ℕ) (hk : 0 < k) :
    (∑ A : (typeIISeed k).genus,
      ((Fintype.card (genusClassRepresentative (typeIISeed k) A).IsometryGroup : ℚ)⁻¹)) =
        typeIIConstant (8 * k) := by
  exact all_positive_seed_literal_sum_of_recursive_identities
    (fun k hk => ⟨stableRecursive_right_inverse k hk, stableRecursive_left_inverse k hk, hQ k hk⟩) k hk

/-- The rank-one-block base case of the recursive fixed-line quadratic identity. -/
theorem stableRecursive_quadratic_identity_one_fin9 (x : Fin 9 → ZMod 4) :
    identityQuadraticModEight ((stableRecursive 1).mulVec x) =
      StableIdentityFixedLine.lineNorm
        (StableIdentityComparisonSeedNormAdapter.seedNormModEight 1) x := by
  rw [stableRecursive_one]
  rw [show identityQuadraticModEight (stableNineModFour.mulVec x) =
      StableIdentityComparisonCertificate.onePlusE8NormModEight x by
    simpa [stableNineModFour] using
      (StableIdentityComparisonCertificate.stableNine_identityQuadraticModEight_eq_onePlusE8Norm x)]
  rw [StableIdentityComparisonCountAdapter.onePlusE8NormModEight_eq_lineNorm]
  rw [StableIdentityComparisonSeedNormAdapter.seedNormModEight_one_eq_e8TailNorm]

/-- The recursive stable matrices satisfy the fixed-line quadratic identity in every positive rank. -/
theorem stableRecursive_quadratic_identity :
    ∀ k : ℕ, 0 < k → ∀ x : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight ((stableRecursive k).mulVec x) =
        StableIdentityFixedLine.lineNorm
          (StableIdentityComparisonSeedNormAdapter.seedNormModEight k) x := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero =>
          intro x
          simpa using stableRecursive_quadratic_identity_one_fin9 x
      | succ k =>
          intro x
          exact stableRecursive_quadratic_identity_succ_step (k + 1) (ih (by omega)) x

/-- Unconditional all-positive E8-power seed mass endpoint from the recursive stable certificate. -/
theorem all_positive_typeIISeed_ordinaryGenusMass_eq_typeIIConstant
    (k : ℕ) (hk : 0 < k) :
    (typeIISeed k).ordinaryGenusMass = typeIIConstant (8 * k) := by
  exact all_positive_seed_mass_of_recursive_quadratic_identity
    stableRecursive_quadratic_identity k hk

/-- Literal genus-sum form of `all_positive_typeIISeed_ordinaryGenusMass_eq_typeIIConstant`. -/
theorem all_positive_typeIISeed_literal_sum_eq_typeIIConstant
    (k : ℕ) (hk : 0 < k) :
    (∑ A : (typeIISeed k).genus,
      ((Fintype.card (genusClassRepresentative (typeIISeed k) A).IsometryGroup : ℚ)⁻¹)) =
        typeIIConstant (8 * k) := by
  exact all_positive_seed_literal_sum_of_recursive_quadratic_identity
    stableRecursive_quadratic_identity k hk

end StableIdentityComparisonStableRecursive

#assert_standard_axioms StableIdentityComparisonStableRecursive.stableNineEntry_col_zero
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableNineInverseEntry_row_zero
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableNine_tail_right_inverse
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableNine_tail_right_inverse_one_add
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableNine_tail_left_inverse
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableNine_tail_left_inverse_row_zero
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableNine_tail_left_inverse_col_zero
#assert_standard_axioms StableIdentityComparisonStableRecursive.oldNewEquiv_inl
#assert_standard_axioms StableIdentityComparisonStableRecursive.oldNewEquiv_inr
#assert_standard_axioms StableIdentityComparisonStableRecursive.sum_old_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.sum_old_newBlock_zmodEight
#assert_standard_axioms StableIdentityComparisonStableRecursive.mul_apply_old_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.one_oldCoord_oldCoord
#assert_standard_axioms StableIdentityComparisonStableRecursive.one_oldCoord_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.one_newBlock_oldCoord
#assert_standard_axioms StableIdentityComparisonStableRecursive.one_newBlock_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_old_old
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_line_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_old_ne_zero_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_newBlock_old
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_newBlock_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.oldPart
#assert_standard_axioms StableIdentityComparisonStableRecursive.newBlockPart
#assert_standard_axioms StableIdentityComparisonStableRecursive.recursiveNineInput
#assert_standard_axioms StableIdentityComparisonStableRecursive.oldTailPart
#assert_standard_axioms StableIdentityComparisonStableRecursive.newTailPart
#assert_standard_axioms StableIdentityComparisonStableRecursive.blockSumMatrix_quadratic_split_zmodEight
#assert_standard_axioms StableIdentityComparisonStableRecursive.seedNormModEight_succ_split
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_quadratic_identity_succ_step
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_mulVec_old_ne_zero
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_mulVec_old_zero
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_mulVec_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.identityQuadraticModEight_old_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_identityQuadratic_succ_split
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursiveInverse_old_old
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursiveInverse_old_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursiveInverse_newBlock_old_zero
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursiveInverse_newBlock_old_ne_zero
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursiveInverse_newBlock_newBlock
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_right_inverse_old_old
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_right_inverse_old_new
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_right_inverse_new_old
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_right_inverse_new_new
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_left_inverse_old_old
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_left_inverse_old_new
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_left_inverse_new_old
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_left_inverse_new_new
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_one
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursiveInverse_one
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_right_inverse_one
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_left_inverse_one
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_right_inverse_succ
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_left_inverse_succ
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_right_inverse
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_left_inverse
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_mulVec_line
#assert_standard_axioms StableIdentityComparisonStableRecursive.certificateOfRecursiveIdentities
#assert_standard_axioms StableIdentityComparisonStableRecursive.all_positive_seed_mass_of_recursive_identities
#assert_standard_axioms StableIdentityComparisonStableRecursive.all_positive_seed_literal_sum_of_recursive_identities
#assert_standard_axioms StableIdentityComparisonStableRecursive.all_positive_seed_mass_of_recursive_quadratic_identity
#assert_standard_axioms StableIdentityComparisonStableRecursive.all_positive_seed_literal_sum_of_recursive_quadratic_identity
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_quadratic_identity_one_fin9
#assert_standard_axioms StableIdentityComparisonStableRecursive.stableRecursive_quadratic_identity
#assert_standard_axioms StableIdentityComparisonStableRecursive.all_positive_typeIISeed_ordinaryGenusMass_eq_typeIIConstant
#assert_standard_axioms StableIdentityComparisonStableRecursive.all_positive_typeIISeed_literal_sum_eq_typeIIConstant
