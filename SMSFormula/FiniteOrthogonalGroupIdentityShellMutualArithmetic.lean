import SMSFormula.FiniteOrthogonalGroupOddToEvenShellState

/-!
# Arithmetic states for the mutual identity-shell recurrence

The even identity-shell formulas are indexed by `m` so that their dimension
is `2 * (m + 1)`.  This avoids negative exponents.  The two orientations
record whether the zero shell or the nonzero shell is larger.  The odd states
are named from the exact even-to-odd transition, and separate arithmetic
lemmas identify their correction and the next even shell values.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Main term of the identity shell in dimension `2 * (m + 1)`. -/
def evenIdentityShellMain (q m : ℕ) : ℕ := q ^ (2 * m + 1)

/-- Lower-order correction in dimension `2 * (m + 1)`. -/
def evenIdentityShellCorrection (q m : ℕ) : ℕ := q ^ m

/-- Zero-shell value in the orientation where the zero shell is larger. -/
def evenIdentitySplitZero (q m : ℕ) : ℕ :=
  evenIdentityShellMain q m +
    (q - 1) * evenIdentityShellCorrection q m

/-- Nonzero-shell value in the orientation where the zero shell is larger. -/
def evenIdentitySplitNonzero (q m : ℕ) : ℕ :=
  evenIdentityShellMain q m - evenIdentityShellCorrection q m

/-- Zero-shell value in the orientation where the nonzero shell is larger. -/
def evenIdentityNonsplitZero (q m : ℕ) : ℕ :=
  evenIdentityShellMain q m -
    (q - 1) * evenIdentityShellCorrection q m

/-- Nonzero-shell value in the orientation where the nonzero shell is larger. -/
def evenIdentityNonsplitNonzero (q m : ℕ) : ℕ :=
  evenIdentityShellMain q m + evenIdentityShellCorrection q m

/-- Correction of the odd shell reached from dimension `2 * (m + 1)`. -/
def oddIdentityShellCorrection (q m : ℕ) : ℕ := q ^ (m + 1)

/-- Root-affine odd base obtained from the larger-zero even state. -/
def oddIdentityAffineBase (q m : ℕ) : ℕ :=
  q * evenIdentitySplitNonzero q m

/-- Root-coaffine odd base obtained from the larger-nonzero even state. -/
def oddIdentityCoaffineBase (q m : ℕ) : ℕ :=
  q * evenIdentityNonsplitNonzero q m

private theorem evenIdentityShellCorrection_le_main
    {q m : ℕ} (hq : 2 ≤ q) :
    evenIdentityShellCorrection q m ≤ evenIdentityShellMain q m := by
  exact Nat.pow_le_pow_right (by omega) (by omega)

private theorem evenIdentityNonsplitCorrection_le_main
    {q m : ℕ} (hq : 2 ≤ q) :
    (q - 1) * evenIdentityShellCorrection q m ≤
      evenIdentityShellMain q m := by
  calc
    (q - 1) * evenIdentityShellCorrection q m ≤
        q * evenIdentityShellCorrection q m :=
      Nat.mul_le_mul_right _ (Nat.sub_le q 1)
    _ = q ^ (m + 1) := by
      rw [pow_succ]
      simp only [evenIdentityShellCorrection]
      ac_rfl
    _ ≤ q ^ (2 * m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = evenIdentityShellMain q m := rfl

private theorem q_mul_correction_eq_oddCorrection
    (q m : ℕ) :
    q * evenIdentityShellCorrection q m =
      oddIdentityShellCorrection q m := by
  simp [evenIdentityShellCorrection, oddIdentityShellCorrection, pow_succ,
    Nat.mul_comm]

/-- In the split orientation the zero shell exceeds the nonzero shell by the
next odd correction. -/
theorem evenIdentitySplitZero_eq_nonzero_add_oddCorrection
    {q m : ℕ} (hq : 2 ≤ q) :
    evenIdentitySplitZero q m =
      evenIdentitySplitNonzero q m + oddIdentityShellCorrection q m := by
  have hle := evenIdentityShellCorrection_le_main (q := q) (m := m) hq
  have hsub : evenIdentitySplitNonzero q m +
      evenIdentityShellCorrection q m = evenIdentityShellMain q m := by
    exact Nat.sub_add_cancel hle
  have hqsplit : q * evenIdentityShellCorrection q m =
      evenIdentityShellCorrection q m +
        (q - 1) * evenIdentityShellCorrection q m := by
    calc
      q * evenIdentityShellCorrection q m =
          ((q - 1) + 1) * evenIdentityShellCorrection q m := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = evenIdentityShellCorrection q m +
          (q - 1) * evenIdentityShellCorrection q m := by ring
  rw [← q_mul_correction_eq_oddCorrection q m, hqsplit]
  calc
    evenIdentitySplitZero q m = evenIdentityShellMain q m +
        (q - 1) * evenIdentityShellCorrection q m := rfl
    _ = (evenIdentitySplitNonzero q m +
          evenIdentityShellCorrection q m) +
        (q - 1) * evenIdentityShellCorrection q m := by rw [hsub]
    _ = evenIdentitySplitNonzero q m +
        (evenIdentityShellCorrection q m +
          (q - 1) * evenIdentityShellCorrection q m) := by omega

/-- In the nonsplit orientation the nonzero shell exceeds the zero shell by
the next odd correction. -/
theorem evenIdentityNonsplitNonzero_eq_zero_add_oddCorrection
    {q m : ℕ} (hq : 2 ≤ q) :
    evenIdentityNonsplitNonzero q m =
      evenIdentityNonsplitZero q m + oddIdentityShellCorrection q m := by
  have hle := evenIdentityNonsplitCorrection_le_main (q := q) (m := m) hq
  have hsub : evenIdentityNonsplitZero q m +
      (q - 1) * evenIdentityShellCorrection q m =
        evenIdentityShellMain q m := Nat.sub_add_cancel hle
  have hqsplit : q * evenIdentityShellCorrection q m =
      (q - 1) * evenIdentityShellCorrection q m +
        evenIdentityShellCorrection q m := by
    calc
      q * evenIdentityShellCorrection q m =
          ((q - 1) + 1) * evenIdentityShellCorrection q m := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = (q - 1) * evenIdentityShellCorrection q m +
          evenIdentityShellCorrection q m := by ring
  rw [← q_mul_correction_eq_oddCorrection q m, hqsplit]
  calc
    evenIdentityNonsplitNonzero q m = evenIdentityShellMain q m +
        evenIdentityShellCorrection q m := rfl
    _ = (evenIdentityNonsplitZero q m +
          (q - 1) * evenIdentityShellCorrection q m) +
        evenIdentityShellCorrection q m := by rw [hsub]
    _ = evenIdentityNonsplitZero q m +
        ((q - 1) * evenIdentityShellCorrection q m +
          evenIdentityShellCorrection q m) := by omega

/-! ### Structural even-to-odd step -/

/-- The standard larger-zero even state gives the named root-affine odd
state. -/
theorem rootAffineShellCardinality_finSuccGramBlock_of_evenIdentitySplit
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (m : ℕ)
    (hq : 2 ≤ Nat.card K)
    (h : ZeroNonzeroShellCardinality B
      (evenIdentitySplitZero (Nat.card K) m)
      (evenIdentitySplitNonzero (Nat.card K) m)) :
    RootAffineShellCardinality (finSuccGramBlock 1 B) 1
      (oddIdentityAffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m) := by
  exact rootAffineShellCardinality_finSuccGramBlock_of_zero_eq_nonzero_add
    B _ _ _ h (evenIdentitySplitZero_eq_nonzero_add_oddCorrection hq)

/-- The standard larger-nonzero even state gives the named root-coaffine odd
state. -/
theorem rootCoaffineShellCardinality_finSuccGramBlock_of_evenIdentityNonsplit
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (m : ℕ)
    (hq : 2 ≤ Nat.card K)
    (h : ZeroNonzeroShellCardinality B
      (evenIdentityNonsplitZero (Nat.card K) m)
      (evenIdentityNonsplitNonzero (Nat.card K) m)) :
    RootCoaffineShellCardinality (finSuccGramBlock 1 B) 1
      (oddIdentityCoaffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m) := by
  exact rootCoaffineShellCardinality_finSuccGramBlock_of_nonzero_eq_zero_add
    B _ _ _ h (evenIdentityNonsplitNonzero_eq_zero_add_oddCorrection hq)

/-! ### Standard odd bases and successor arithmetic -/

private theorem oddIdentityShellCorrection_pos
    {q m : ℕ} (hq : 2 ≤ q) : 0 < oddIdentityShellCorrection q m := by
  exact pow_pos (by omega) _

/-- The root-affine base has the standard factored form. -/
theorem oddIdentityAffineBase_eq
    {q m : ℕ} (hq : 2 ≤ q) :
    oddIdentityAffineBase q m =
      oddIdentityShellCorrection q m *
        (oddIdentityShellCorrection q m - 1) := by
  let A := oddIdentityShellCorrection q m
  have hA : 1 ≤ A := oddIdentityShellCorrection_pos hq
  have hC := evenIdentityShellCorrection_le_main (q := q) (m := m) hq
  have hsub : evenIdentitySplitNonzero q m +
      evenIdentityShellCorrection q m = evenIdentityShellMain q m :=
    Nat.sub_add_cancel hC
  change oddIdentityAffineBase q m = A * (A - 1)
  have hcancel : oddIdentityAffineBase q m + A = A * (A - 1) + A := by
    calc
      oddIdentityAffineBase q m + A =
          q * evenIdentitySplitNonzero q m +
            q * evenIdentityShellCorrection q m := by
        dsimp only [oddIdentityAffineBase, A]
        rw [q_mul_correction_eq_oddCorrection]
      _ = q * (evenIdentitySplitNonzero q m +
            evenIdentityShellCorrection q m) := by ring
      _ = q * evenIdentityShellMain q m := by rw [hsub]
      _ = q ^ (2 * m + 2) := by
        rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ]
        simp only [evenIdentityShellMain]
        ac_rfl
      _ = A * A := by
        dsimp [A, oddIdentityShellCorrection]
        rw [← pow_add]
        congr 1
        omega
      _ = A * (A - 1) + A := by
        calc
          A * A = A * ((A - 1) + 1) := by rw [Nat.sub_add_cancel hA]
          _ = A * (A - 1) + A := by ring
  exact Nat.add_right_cancel hcancel

/-- The root-coaffine base has the standard factored form. -/
theorem oddIdentityCoaffineBase_eq (q m : ℕ) :
    oddIdentityCoaffineBase q m =
      oddIdentityShellCorrection q m *
        (oddIdentityShellCorrection q m + 1) := by
  calc
    oddIdentityCoaffineBase q m =
        q * (evenIdentityShellMain q m +
          evenIdentityShellCorrection q m) := rfl
    _ = q * evenIdentityShellMain q m +
        q * evenIdentityShellCorrection q m := by rw [Nat.mul_add]
    _ = q ^ (2 * m + 2) + q ^ (m + 1) := by
      rw [q_mul_correction_eq_oddCorrection]
      simp only [oddIdentityShellCorrection]
      congr 1
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ]
      simp only [evenIdentityShellMain]
      ac_rfl
    _ = oddIdentityShellCorrection q m *
        (oddIdentityShellCorrection q m + 1) := by
      rw [Nat.mul_add]
      simp only [Nat.mul_one, oddIdentityShellCorrection]
      congr 1
      rw [← pow_add]
      congr 1
      omega

private theorem evenIdentityShellMain_succ (q m : ℕ) :
    evenIdentityShellMain q (m + 1) =
      q * oddIdentityShellCorrection q m *
        oddIdentityShellCorrection q m := by
  simp only [evenIdentityShellMain, oddIdentityShellCorrection]
  rw [show 2 * (m + 1) + 1 = (m + 1) + (m + 1) + 1 by omega,
    pow_succ, pow_add]
  ac_rfl

private theorem affine_split_zero_arithmetic
    {q A : ℕ} (hq : 2 ≤ q) (hA : 1 ≤ A) :
    q * (A * (A - 1)) + A * (2 * q - 1) =
      q * A * A + (q - 1) * A := by
  let k := q - 1
  let a := A - 1
  have hqeq : q = k + 1 := by dsimp [k]; omega
  have hAeq : A = a + 1 := by dsimp [a]; omega
  rw [hqeq, hAeq]
  have htwo : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  simp only [Nat.add_sub_cancel, htwo]
  ring

private theorem affine_split_nonzero_arithmetic
    {q A : ℕ} (hq : 2 ≤ q) (hA : 1 ≤ A) :
    q * (A * (A - 1)) + A * (q - 1) = q * A * A - A := by
  apply Nat.eq_sub_of_add_eq
  let k := q - 1
  let a := A - 1
  have hqeq : q = k + 1 := by dsimp [k]; omega
  have hAeq : A = a + 1 := by dsimp [a]; omega
  rw [hqeq, hAeq]
  simp only [Nat.add_sub_cancel]
  ring

private theorem affine_nonsplit_zero_arithmetic
    {q A : ℕ} (hq : 2 ≤ q) (hA : 1 ≤ A) :
    q * (A * (A - 1)) + A = q * A * A - (q - 1) * A := by
  apply Nat.eq_sub_of_add_eq
  let k := q - 1
  let a := A - 1
  have hqeq : q = k + 1 := by dsimp [k]; omega
  have hAeq : A = a + 1 := by dsimp [a]; omega
  rw [hqeq, hAeq]
  simp only [Nat.add_sub_cancel]
  ring

private theorem affine_nonsplit_nonzero_arithmetic
    {q A : ℕ} (hq : 2 ≤ q) (hA : 1 ≤ A) :
    q * (A * (A - 1)) + A * (q + 1) = q * A * A + A := by
  let k := q - 1
  let a := A - 1
  have hqeq : q = k + 1 := by dsimp [k]; omega
  have hAeq : A = a + 1 := by dsimp [a]; omega
  rw [hqeq, hAeq]
  simp only [Nat.add_sub_cancel]
  ring

private theorem coaffine_square_zero_arithmetic
    {q A : ℕ} (hq : 2 ≤ q) (hA : 1 ≤ A) :
    (q * A * A - (q - 1) * A) + A * (2 * q - 1) =
      q * (A * (A + 1)) := by
  have hle : (q - 1) * A ≤ q * A * A := by
    calc
      (q - 1) * A ≤ q * A := Nat.mul_le_mul_right _ (Nat.sub_le q 1)
      _ ≤ q * (A * A) := Nat.mul_le_mul_left q (by nlinarith)
      _ = q * A * A := by ring
  have hsub := Nat.sub_add_cancel hle
  have hcorr : A * (2 * q - 1) = (q - 1) * A + q * A := by
    let k := q - 1
    have hqeq : q = k + 1 := by dsimp [k]; omega
    rw [hqeq]
    have htwo : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have hk : k + 1 - 1 = k := by omega
    rw [htwo, hk]
    ring
  rw [hcorr]
  calc
    q * A * A - (q - 1) * A + ((q - 1) * A + q * A) =
        (q * A * A - (q - 1) * A + (q - 1) * A) + q * A := by
      omega
    _ = q * A * A + q * A := by rw [hsub]
    _ = q * (A * (A + 1)) := by ring

private theorem coaffine_square_nonzero_arithmetic
    {q A : ℕ} (hq : 2 ≤ q) :
    (q * A * A + A) + A * (q - 1) = q * (A * (A + 1)) := by
  let k := q - 1
  have hqeq : q = k + 1 := by dsimp [k]; omega
  rw [hqeq]
  simp only [Nat.add_sub_cancel]
  ring

private theorem coaffine_nonsplit_zero_arithmetic
    {q A : ℕ} (hq : 2 ≤ q) :
    (q * A * A + (q - 1) * A) + A = q * (A * (A + 1)) := by
  let k := q - 1
  have hqeq : q = k + 1 := by dsimp [k]; omega
  rw [hqeq]
  simp only [Nat.add_sub_cancel]
  ring

private theorem coaffine_nonsplit_nonzero_arithmetic
    {q A : ℕ} (hq : 2 ≤ q) (hA : 1 ≤ A) :
    (q * A * A - A) + A * (q + 1) = q * (A * (A + 1)) := by
  have hle : A ≤ q * A * A := by
    calc
      A ≤ A * A := by nlinarith
      _ ≤ q * (A * A) := Nat.le_mul_of_pos_left _ (by omega)
      _ = q * A * A := by ring
  have hsub := Nat.sub_add_cancel hle
  calc
    q * A * A - A + A * (q + 1) =
        (q * A * A - A + A) + q * A := by ring
    _ = q * A * A + q * A := by rw [hsub]
    _ = q * (A * (A + 1)) := by ring

/-- Split weighted-binary evaluation of the affine odd state gives the next
split zero-shell expression. -/
theorem oddIdentityAffine_nextSplitZero
    {q m : ℕ} (hq : 2 ≤ q) :
    q * oddIdentityAffineBase q m +
        oddIdentityShellCorrection q m * (2 * q - 1) =
      evenIdentitySplitZero q (m + 1) := by
  let A := oddIdentityShellCorrection q m
  have hA : 1 ≤ A := oddIdentityShellCorrection_pos hq
  rw [oddIdentityAffineBase_eq hq]
  change q * (A * (A - 1)) + A * (2 * q - 1) = _
  rw [affine_split_zero_arithmetic hq hA,
    ← evenIdentityShellMain_succ q m]
  rfl

/-- Split weighted-binary evaluation of the affine odd state gives the next
split nonzero-shell expression. -/
theorem oddIdentityAffine_nextSplitNonzero
    {q m : ℕ} (hq : 2 ≤ q) :
    q * oddIdentityAffineBase q m +
        oddIdentityShellCorrection q m * (q - 1) =
      evenIdentitySplitNonzero q (m + 1) := by
  let A := oddIdentityShellCorrection q m
  have hA : 1 ≤ A := oddIdentityShellCorrection_pos hq
  rw [oddIdentityAffineBase_eq hq]
  change q * (A * (A - 1)) + A * (q - 1) = _
  rw [affine_split_nonzero_arithmetic hq hA,
    ← evenIdentityShellMain_succ q m]
  rfl

/-- Nonsplit weighted-binary evaluation of the affine odd state gives the
next nonsplit zero-shell expression. -/
theorem oddIdentityAffine_nextNonsplitZero
    {q m : ℕ} (hq : 2 ≤ q) :
    q * oddIdentityAffineBase q m + oddIdentityShellCorrection q m =
      evenIdentityNonsplitZero q (m + 1) := by
  let A := oddIdentityShellCorrection q m
  have hA : 1 ≤ A := oddIdentityShellCorrection_pos hq
  rw [oddIdentityAffineBase_eq hq]
  change q * (A * (A - 1)) + A = _
  rw [affine_nonsplit_zero_arithmetic hq hA,
    ← evenIdentityShellMain_succ q m]
  rfl

/-- Nonsplit weighted-binary evaluation of the affine odd state gives the
next nonsplit nonzero-shell expression. -/
theorem oddIdentityAffine_nextNonsplitNonzero
    {q m : ℕ} (hq : 2 ≤ q) :
    q * oddIdentityAffineBase q m +
        oddIdentityShellCorrection q m * (q + 1) =
      evenIdentityNonsplitNonzero q (m + 1) := by
  let A := oddIdentityShellCorrection q m
  have hA : 1 ≤ A := oddIdentityShellCorrection_pos hq
  rw [oddIdentityAffineBase_eq hq]
  change q * (A * (A - 1)) + A * (q + 1) = _
  rw [affine_nonsplit_nonzero_arithmetic hq hA,
    ← evenIdentityShellMain_succ q m]
  rfl

/-- In the split binary case, the next nonsplit zero expression satisfies the
coaffine complementary equation. -/
theorem oddIdentityCoaffine_nextNonsplitZero_add
    {q m : ℕ} (hq : 2 ≤ q) :
    evenIdentityNonsplitZero q (m + 1) +
        oddIdentityShellCorrection q m * (2 * q - 1) =
      q * oddIdentityCoaffineBase q m := by
  let A := oddIdentityShellCorrection q m
  have hA : 1 ≤ A := oddIdentityShellCorrection_pos hq
  change (evenIdentityShellMain q (m + 1) - (q - 1) * A) +
      A * (2 * q - 1) = _
  rw [evenIdentityShellMain_succ q m,
    coaffine_square_zero_arithmetic hq hA,
    oddIdentityCoaffineBase_eq]

/-- In the split binary case, the next nonsplit nonzero expression satisfies
the coaffine complementary equation. -/
theorem oddIdentityCoaffine_nextNonsplitNonzero_add
    {q m : ℕ} (hq : 2 ≤ q) :
    evenIdentityNonsplitNonzero q (m + 1) +
        oddIdentityShellCorrection q m * (q - 1) =
      q * oddIdentityCoaffineBase q m := by
  let A := oddIdentityShellCorrection q m
  change (evenIdentityShellMain q (m + 1) + A) + A * (q - 1) = _
  rw [evenIdentityShellMain_succ q m,
    coaffine_square_nonzero_arithmetic hq,
    oddIdentityCoaffineBase_eq]

/-- In the nonsplit binary case, the next split zero expression satisfies the
coaffine complementary equation. -/
theorem oddIdentityCoaffine_nextSplitZero_add
    {q m : ℕ} (hq : 2 ≤ q) :
    evenIdentitySplitZero q (m + 1) + oddIdentityShellCorrection q m =
      q * oddIdentityCoaffineBase q m := by
  let A := oddIdentityShellCorrection q m
  change (evenIdentityShellMain q (m + 1) + (q - 1) * A) + A = _
  rw [evenIdentityShellMain_succ q m,
    coaffine_nonsplit_zero_arithmetic hq,
    oddIdentityCoaffineBase_eq]

/-- In the nonsplit binary case, the next split nonzero expression satisfies
the coaffine complementary equation. -/
theorem oddIdentityCoaffine_nextSplitNonzero_add
    {q m : ℕ} (hq : 2 ≤ q) :
    evenIdentitySplitNonzero q (m + 1) +
        oddIdentityShellCorrection q m * (q + 1) =
      q * oddIdentityCoaffineBase q m := by
  let A := oddIdentityShellCorrection q m
  have hA : 1 ≤ A := oddIdentityShellCorrection_pos hq
  change (evenIdentityShellMain q (m + 1) - A) + A * (q + 1) = _
  rw [evenIdentityShellMain_succ q m,
    coaffine_nonsplit_nonzero_arithmetic hq hA,
    oddIdentityCoaffineBase_eq]

/-! ### One complete two-dimension successor step -/

/-- A larger-zero even state remains larger-zero after two dimensions when
`-1` is square. -/
theorem zeroNonzeroShellCardinality_twoStep_of_evenIdentitySplit_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (m : ℕ)
    (hq : 2 ≤ Nat.card K)
    (h : ZeroNonzeroShellCardinality B
      (evenIdentitySplitZero (Nat.card K) m)
      (evenIdentitySplitNonzero (Nat.card K) m))
    (t : K) (ht : t ^ 2 = -1) :
    ZeroNonzeroShellCardinality
      (finSuccGramBlock 1 (finSuccGramBlock 1 B))
      (evenIdentitySplitZero (Nat.card K) (m + 1))
      (evenIdentitySplitNonzero (Nat.card K) (m + 1)) := by
  have hodd := rootAffineShellCardinality_finSuccGramBlock_of_evenIdentitySplit
    B m hq h
  have hout :=
    zeroNonzeroShellCardinality_finSuccGramBlock_of_rootAffine_of_neg_square
      hchar (finSuccGramBlock 1 B) 1
      (oddIdentityAffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m)
      hodd one_ne_zero t ht
  rw [oddIdentityAffine_nextSplitZero hq,
    oddIdentityAffine_nextSplitNonzero hq] at hout
  exact hout

/-- A larger-zero even state becomes larger-nonzero after two dimensions when
`-1` is nonsquare. -/
theorem zeroNonzeroShellCardinality_twoStep_of_evenIdentitySplit_of_neg_one_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (m : ℕ)
    (hq : 2 ≤ Nat.card K)
    (h : ZeroNonzeroShellCardinality B
      (evenIdentitySplitZero (Nat.card K) m)
      (evenIdentitySplitNonzero (Nat.card K) m))
    (hneg : ∀ r : K, r ^ 2 ≠ -1) :
    ZeroNonzeroShellCardinality
      (finSuccGramBlock 1 (finSuccGramBlock 1 B))
      (evenIdentityNonsplitZero (Nat.card K) (m + 1))
      (evenIdentityNonsplitNonzero (Nat.card K) (m + 1)) := by
  by_cases hbad : ringChar K = 2
  · exact (hchar hbad).elim
  · have hodd :=
      rootAffineShellCardinality_finSuccGramBlock_of_evenIdentitySplit B m hq h
    have hout :=
      zeroNonzeroShellCardinality_finSuccGramBlock_of_rootAffine_of_neg_nonsquare
        (finSuccGramBlock 1 B) 1
        (oddIdentityAffineBase (Nat.card K) m)
        (oddIdentityShellCorrection (Nat.card K) m)
        hodd one_ne_zero hneg
    rw [oddIdentityAffine_nextNonsplitZero hq,
      oddIdentityAffine_nextNonsplitNonzero hq] at hout
    exact hout

/-- A larger-nonzero even state remains larger-nonzero after two dimensions
when `-1` is square. -/
theorem zeroNonzeroShellCardinality_twoStep_of_evenIdentityNonsplit_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (m : ℕ)
    (hq : 2 ≤ Nat.card K)
    (h : ZeroNonzeroShellCardinality B
      (evenIdentityNonsplitZero (Nat.card K) m)
      (evenIdentityNonsplitNonzero (Nat.card K) m))
    (t : K) (ht : t ^ 2 = -1) :
    ZeroNonzeroShellCardinality
      (finSuccGramBlock 1 (finSuccGramBlock 1 B))
      (evenIdentityNonsplitZero (Nat.card K) (m + 1))
      (evenIdentityNonsplitNonzero (Nat.card K) (m + 1)) := by
  have hodd :=
    rootCoaffineShellCardinality_finSuccGramBlock_of_evenIdentityNonsplit
      B m hq h
  exact
    zeroNonzeroShellCardinality_finSuccGramBlock_of_rootCoaffine_of_neg_square
      hchar (finSuccGramBlock 1 B) 1
      (oddIdentityCoaffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m)
      hodd one_ne_zero t ht
      (evenIdentityNonsplitZero (Nat.card K) (m + 1))
      (evenIdentityNonsplitNonzero (Nat.card K) (m + 1))
      (oddIdentityCoaffine_nextNonsplitZero_add hq)
      (oddIdentityCoaffine_nextNonsplitNonzero_add hq)

/-- A larger-nonzero even state becomes larger-zero after two dimensions when
`-1` is nonsquare. -/
theorem zeroNonzeroShellCardinality_twoStep_of_evenIdentityNonsplit_of_neg_one_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (m : ℕ)
    (hq : 2 ≤ Nat.card K)
    (h : ZeroNonzeroShellCardinality B
      (evenIdentityNonsplitZero (Nat.card K) m)
      (evenIdentityNonsplitNonzero (Nat.card K) m))
    (hneg : ∀ r : K, r ^ 2 ≠ -1) :
    ZeroNonzeroShellCardinality
      (finSuccGramBlock 1 (finSuccGramBlock 1 B))
      (evenIdentitySplitZero (Nat.card K) (m + 1))
      (evenIdentitySplitNonzero (Nat.card K) (m + 1)) := by
  by_cases hbad : ringChar K = 2
  · exact (hchar hbad).elim
  · have hodd :=
      rootCoaffineShellCardinality_finSuccGramBlock_of_evenIdentityNonsplit
        B m hq h
    exact
      zeroNonzeroShellCardinality_finSuccGramBlock_of_rootCoaffine_of_neg_nonsquare
        (finSuccGramBlock 1 B) 1
        (oddIdentityCoaffineBase (Nat.card K) m)
        (oddIdentityShellCorrection (Nat.card K) m)
        hodd one_ne_zero hneg
        (evenIdentitySplitZero (Nat.card K) (m + 1))
        (evenIdentitySplitNonzero (Nat.card K) (m + 1))
        (oddIdentityCoaffine_nextSplitZero_add hq)
        (oddIdentityCoaffine_nextSplitNonzero_add hq)

end PositiveDefiniteIntegralLattice
