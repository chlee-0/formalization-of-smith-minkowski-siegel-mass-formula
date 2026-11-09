import SMSFormula.FiniteOrthogonalGroupIdentityOrderMultiplier

/-!
# Closed finite orthogonal-order arithmetic

This module defines the standard odd, split-even, and nonsplit-even natural
order expressions.  It proves only their finite-product successor arithmetic;
no expression is identified with a finite orthogonal-group cardinality here.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The finite Euler product `∏_{j=1}^s (q^(2j)-1)` occurring in every
finite orthogonal-group order formula. -/
def finiteOrthogonalOrderEulerProduct (q s : ℕ) : ℕ :=
  (Finset.Icc 1 s).prod fun j => q ^ (2 * j) - 1

/-- The standard order expression for an odd orthogonal group of dimension
`2s+1`. -/
def oddIdentityOrthogonalOrderExpression (q s : ℕ) : ℕ :=
  2 * q ^ (s * s) * finiteOrthogonalOrderEulerProduct q s

/-- The standard split order expression for an even orthogonal group of
dimension `2s`. -/
def splitEvenIdentityOrthogonalOrderExpression (q s : ℕ) : ℕ :=
  2 * q ^ (s * (s - 1)) * (q ^ s - 1) *
    finiteOrthogonalOrderEulerProduct q (s - 1)

/-- The standard nonsplit order expression for an even orthogonal group of
dimension `2s`. -/
def nonsplitEvenIdentityOrthogonalOrderExpression (q s : ℕ) : ℕ :=
  2 * q ^ (s * (s - 1)) * (q ^ s + 1) *
    finiteOrthogonalOrderEulerProduct q (s - 1)

/-! ### Euler-product endpoints -/

@[simp] theorem finiteOrthogonalOrderEulerProduct_zero (q : ℕ) :
    finiteOrthogonalOrderEulerProduct q 0 = 1 := by
  simp [finiteOrthogonalOrderEulerProduct]

/-- Adjoining the literal top index `s+1` appends its Euler factor. -/
theorem finiteOrthogonalOrderEulerProduct_succ (q s : ℕ) :
    finiteOrthogonalOrderEulerProduct q (s + 1) =
      finiteOrthogonalOrderEulerProduct q s * (q ^ (2 * (s + 1)) - 1) := by
  unfold finiteOrthogonalOrderEulerProduct
  exact Finset.prod_Icc_succ_top (by omega) _

/-- Positive-index predecessor form of the Euler-product successor. -/
theorem finiteOrthogonalOrderEulerProduct_eq_pred_mul
    (q : ℕ) {s : ℕ} (hs : 0 < s) :
    finiteOrthogonalOrderEulerProduct q s =
      finiteOrthogonalOrderEulerProduct q (s - 1) * (q ^ (2 * s) - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    finiteOrthogonalOrderEulerProduct_succ q r

/-! ### Mutual closed-order successor arithmetic -/

/-- The split even-to-odd multiplier turns the split even expression into the
odd expression at the same half-rank. -/
theorem splitEvenToOddOrthogonalOrderExpression
    (q : ℕ) {s : ℕ} (hs : 0 < s) :
    (q ^ (2 * s) + q ^ s) *
        splitEvenIdentityOrthogonalOrderExpression q s =
      oddIdentityOrthogonalOrderExpression q s := by
  have hprod := finiteOrthogonalOrderEulerProduct_eq_pred_mul q hs
  have hsq : q ^ (2 * s) = (q ^ s) ^ 2 := by
    rw [show 2 * s = s + s by omega, pow_add, pow_two]
  have hfactor : q ^ (2 * s) - 1 =
      (q ^ s + 1) * (q ^ s - 1) := by
    rw [hsq]
    exact sq_tsub_sq (q ^ s) 1
  have hpower : q ^ (s * s) = q ^ s * q ^ (s * (s - 1)) := by
    let r := s - 1
    have hsr : s = r + 1 := by dsimp only [r]; omega
    rw [← pow_add]
    congr 1
    rw [hsr]
    simp only [Nat.add_sub_cancel]
    ring
  unfold splitEvenIdentityOrthogonalOrderExpression
    oddIdentityOrthogonalOrderExpression
  rw [hprod, hfactor, hsq, hpower]
  ring

/-- The nonsplit even-to-odd multiplier turns the nonsplit even expression
into the same odd expression. -/
theorem nonsplitEvenToOddOrthogonalOrderExpression
    (q : ℕ) {s : ℕ} (hs : 0 < s) :
    (q ^ (2 * s) - q ^ s) *
        nonsplitEvenIdentityOrthogonalOrderExpression q s =
      oddIdentityOrthogonalOrderExpression q s := by
  have hprod := finiteOrthogonalOrderEulerProduct_eq_pred_mul q hs
  have hsq : q ^ (2 * s) = (q ^ s) ^ 2 := by
    rw [show 2 * s = s + s by omega, pow_add, pow_two]
  have hminus : q ^ (2 * s) - q ^ s = q ^ s * (q ^ s - 1) := by
    calc
      q ^ (2 * s) - q ^ s = q ^ s * q ^ s - q ^ s * 1 := by
        rw [hsq, pow_two, Nat.mul_one]
      _ = q ^ s * (q ^ s - 1) := by rw [Nat.mul_sub_left_distrib]
  have hfactor : q ^ (2 * s) - 1 =
      (q ^ s + 1) * (q ^ s - 1) := by
    rw [hsq]
    exact sq_tsub_sq (q ^ s) 1
  have hpower : q ^ (s * s) = q ^ s * q ^ (s * (s - 1)) := by
    let r := s - 1
    have hsr : s = r + 1 := by dsimp only [r]; omega
    rw [← pow_add]
    congr 1
    rw [hsr]
    simp only [Nat.add_sub_cancel]
    ring
  unfold nonsplitEvenIdentityOrthogonalOrderExpression
    oddIdentityOrthogonalOrderExpression
  rw [hprod, hminus, hfactor, hpower]
  ring

/-- The split nonzero shell multiplier turns the odd expression at `s` into
the split even expression at `s+1`. -/
theorem oddToSplitEvenOrthogonalOrderExpression (q s : ℕ) :
    evenIdentitySplitNonzero q s *
        oddIdentityOrthogonalOrderExpression q s =
      splitEvenIdentityOrthogonalOrderExpression q (s + 1) := by
  have hmain : q ^ (2 * s + 1) = q ^ s * q ^ (s + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hmultiplier : evenIdentitySplitNonzero q s =
      q ^ s * (q ^ (s + 1) - 1) := by
    change q ^ (2 * s + 1) - q ^ s = _
    calc
      q ^ (2 * s + 1) - q ^ s =
          q ^ s * q ^ (s + 1) - q ^ s * 1 := by
        rw [hmain, Nat.mul_one]
      _ = q ^ s * (q ^ (s + 1) - 1) := by
        rw [Nat.mul_sub_left_distrib]
  have hpower : q ^ s * q ^ (s * s) = q ^ ((s + 1) * s) := by
    rw [← pow_add]
    congr 1
    ring
  unfold oddIdentityOrthogonalOrderExpression
    splitEvenIdentityOrthogonalOrderExpression
  rw [hmultiplier]
  simp only [Nat.add_sub_cancel]
  calc
    q ^ s * (q ^ (s + 1) - 1) *
          (2 * q ^ (s * s) * finiteOrthogonalOrderEulerProduct q s) =
        2 * (q ^ s * q ^ (s * s)) * (q ^ (s + 1) - 1) *
          finiteOrthogonalOrderEulerProduct q s := by ring
    _ = 2 * q ^ ((s + 1) * s) * (q ^ (s + 1) - 1) *
          finiteOrthogonalOrderEulerProduct q s := by rw [hpower]

/-- The nonsplit nonzero shell multiplier turns the odd expression at `s`
into the nonsplit even expression at `s+1`. -/
theorem oddToNonsplitEvenOrthogonalOrderExpression (q s : ℕ) :
    evenIdentityNonsplitNonzero q s *
        oddIdentityOrthogonalOrderExpression q s =
      nonsplitEvenIdentityOrthogonalOrderExpression q (s + 1) := by
  have hmain : q ^ (2 * s + 1) = q ^ s * q ^ (s + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hmultiplier : evenIdentityNonsplitNonzero q s =
      q ^ s * (q ^ (s + 1) + 1) := by
    change q ^ (2 * s + 1) + q ^ s = _
    rw [hmain]
    ring
  have hpower : q ^ s * q ^ (s * s) = q ^ ((s + 1) * s) := by
    rw [← pow_add]
    congr 1
    ring
  unfold oddIdentityOrthogonalOrderExpression
    nonsplitEvenIdentityOrthogonalOrderExpression
  rw [hmultiplier]
  simp only [Nat.add_sub_cancel]
  calc
    q ^ s * (q ^ (s + 1) + 1) *
          (2 * q ^ (s * s) * finiteOrthogonalOrderEulerProduct q s) =
        2 * (q ^ s * q ^ (s * s)) * (q ^ (s + 1) + 1) *
          finiteOrthogonalOrderEulerProduct q s := by ring
    _ = 2 * q ^ ((s + 1) * s) * (q ^ (s + 1) + 1) *
          finiteOrthogonalOrderEulerProduct q s := by rw [hpower]

end PositiveDefiniteIntegralLattice
