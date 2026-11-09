import SMSFormula.FiniteOrthogonalGroupIdentityShellInduction
import SMSFormula.FiniteOrthogonalGroupIdentityOrderRecurrence

/-!
# Identity-form orthogonal-order recurrence multipliers

The completed identity-shell induction is inserted into the arbitrary-rank
orbit--stabilizer recurrence.  This module first proves the exact natural
arithmetic of the split and nonsplit norm-one shell multipliers, retaining all
bounds behind natural subtraction, and then records the resulting square and
nonsquare identity-group recurrences.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-! ### Closed natural shell multipliers -/

/-- The split even shell contributes `q^(2(m+1)) + q^(m+1)` to the next
norm-one shell. -/
theorem two_mul_evenIdentitySplitZero_add_nonzero_eq
    {q m : ℕ} (hq : 2 ≤ q) :
    2 * evenIdentitySplitZero q m +
        (q - 2) * evenIdentitySplitNonzero q m =
      q ^ (2 * (m + 1)) + q ^ (m + 1) := by
  let M := evenIdentityShellMain q m
  let C := evenIdentityShellCorrection q m
  let U := M - C
  have hCM : C ≤ M := by
    dsimp only [C, M, evenIdentityShellCorrection, evenIdentityShellMain]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hMU : U + C = M := Nat.sub_add_cancel hCM
  have hpowMain : q ^ (2 * (m + 1)) = q * M := by
    dsimp only [M, evenIdentityShellMain]
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, pow_succ]
    ac_rfl
  have hpowCorrection : q ^ (m + 1) = q * C := by
    dsimp only [C, evenIdentityShellCorrection]
    rw [pow_succ]
    ac_rfl
  change 2 * (M + (q - 1) * C) + (q - 2) * U = _
  rw [hpowMain, hpowCorrection]
  let k := q - 2
  have hq : q = k + 2 := by dsimp only [k]; omega
  have hq1 : q - 1 = k + 1 := by dsimp only [k]; omega
  rw [hq1, hq]
  simp only [Nat.add_sub_cancel]
  rw [← hMU]
  ring

/-- The nonsplit even shell contributes `q^(2(m+1)) - q^(m+1)` to the next
norm-one shell. -/
theorem two_mul_evenIdentityNonsplitZero_add_nonzero_eq
    {q m : ℕ} (hq : 2 ≤ q) :
    2 * evenIdentityNonsplitZero q m +
        (q - 2) * evenIdentityNonsplitNonzero q m =
      q ^ (2 * (m + 1)) - q ^ (m + 1) := by
  let M := evenIdentityShellMain q m
  let C := evenIdentityShellCorrection q m
  let Z := M - (q - 1) * C
  have hCM : (q - 1) * C ≤ M := by
    calc
      (q - 1) * C ≤ q * C :=
        Nat.mul_le_mul_right C (Nat.sub_le q 1)
      _ = q ^ (m + 1) := by
        dsimp only [C, evenIdentityShellCorrection]
        rw [pow_succ]
        ac_rfl
      _ ≤ q ^ (2 * m + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ = M := by rfl
  have hMZ : Z + (q - 1) * C = M := Nat.sub_add_cancel hCM
  have hpowMain : q ^ (2 * (m + 1)) = q * M := by
    dsimp only [M, evenIdentityShellMain]
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, pow_succ]
    ac_rfl
  have hpowCorrection : q ^ (m + 1) = q * C := by
    dsimp only [C, evenIdentityShellCorrection]
    rw [pow_succ]
    ac_rfl
  change 2 * Z + (q - 2) * (M + C) = _
  rw [hpowMain, hpowCorrection]
  apply Nat.eq_sub_of_add_eq
  let k := q - 2
  have hq : q = k + 2 := by dsimp only [k]; omega
  have hq1 : q - 1 = k + 1 := by dsimp only [k]; omega
  have hMZ' : Z + (k + 1) * C = M := by simpa only [hq1] using hMZ
  rw [hq]
  simp only [Nat.add_sub_cancel]
  rw [← hMZ']
  ring

/-! ### Even identity group to odd identity group -/

/-- If `-1` is square, the exact multiplier from rank `2(m+1)` to rank
`2(m+1)+1` is the split norm-one shell. -/
theorem splitIdentityEvenToOddOrthogonalOrderMultiplier_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (t : K) (ht : t ^ 2 = -1) (m : ℕ) :
    ((Nat.card K) ^ (2 * (m + 1)) + (Nat.card K) ^ (m + 1)) *
        Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K)) =
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * (m + 1) + 1))
          (Fin (2 * (m + 1) + 1)) K)) := by
  have hshell := evenIdentitySplitShellCardinality_of_neg_one_square
    hchar hq t ht m
  have hrec := two_mul_zeroShell_add_nonzeroShell_mul_orthogonal_eq
    (n := 2 * (m + 1)) hchar
    (evenIdentitySplitZero (Nat.card K) m)
    (evenIdentitySplitNonzero (Nat.card K) m)
    hshell.1 hshell.2
  rw [two_mul_evenIdentitySplitZero_add_nonzero_eq hq] at hrec
  exact hrec

/-- If `-1` is nonsquare, the even identity state at index `2r` is nonsplit,
and its exact multiplier to the next odd rank has the minus orientation. -/
theorem nonsplitIdentityEvenToOddOrthogonalOrderMultiplier_of_neg_one_nonsquare_even
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hneg : ∀ x : K, x ^ 2 ≠ -1) (r : ℕ) :
    ((Nat.card K) ^ (2 * (2 * r + 1)) - (Nat.card K) ^ (2 * r + 1)) *
        Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (2 * r + 1)))
            (Fin (2 * (2 * r + 1))) K)) =
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * (2 * r + 1) + 1))
          (Fin (2 * (2 * r + 1) + 1)) K)) := by
  have hshell :=
    (evenIdentityShellCardinality_pair_of_neg_one_nonsquare
      hchar hq hneg r).1
  have hrec := two_mul_zeroShell_add_nonzeroShell_mul_orthogonal_eq
    (n := 2 * (2 * r + 1)) hchar
    (evenIdentityNonsplitZero (Nat.card K) (2 * r))
    (evenIdentityNonsplitNonzero (Nat.card K) (2 * r))
    hshell.1 hshell.2
  rw [two_mul_evenIdentityNonsplitZero_add_nonzero_eq hq] at hrec
  exact hrec

/-- If `-1` is nonsquare, the even identity state at index `2r+1` is split,
and its exact multiplier to the next odd rank has the plus orientation. -/
theorem splitIdentityEvenToOddOrthogonalOrderMultiplier_of_neg_one_nonsquare_odd
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hneg : ∀ x : K, x ^ 2 ≠ -1) (r : ℕ) :
    ((Nat.card K) ^ (2 * (2 * r + 2)) + (Nat.card K) ^ (2 * r + 2)) *
        Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (2 * r + 2)))
            (Fin (2 * (2 * r + 2))) K)) =
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * (2 * r + 2) + 1))
          (Fin (2 * (2 * r + 2) + 1)) K)) := by
  have hshell :=
    (evenIdentityShellCardinality_pair_of_neg_one_nonsquare
      hchar hq hneg r).2
  have hrec := two_mul_zeroShell_add_nonzeroShell_mul_orthogonal_eq
    (n := 2 * (2 * r + 2)) hchar
    (evenIdentitySplitZero (Nat.card K) (2 * r + 1))
    (evenIdentitySplitNonzero (Nat.card K) (2 * r + 1))
    hshell.1 hshell.2
  rw [two_mul_evenIdentitySplitZero_add_nonzero_eq hq] at hrec
  exact hrec

/-! ### Odd identity group to the next even identity group -/

/-- A named split shell state in the next even rank gives the exact
odd-to-even order multiplier. -/
theorem evenIdentitySplitNonzero_mul_oddOrthogonal_eq_nextEven
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (h : EvenIdentitySplitShellCardinality K (m + 1)) :
    evenIdentitySplitNonzero (Nat.card K) (m + 1) *
        Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (m + 1) + 1))
            (Fin (2 * (m + 1) + 1)) K)) =
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * ((m + 1) + 1)))
          (Fin (2 * ((m + 1) + 1))) K)) := by
  have hrec := natCard_identityFixedNorm_mul_identityOrthogonal_eq
    (n := 2 * (m + 1) + 1) hchar
  have hone := h.2 (1 : K) one_ne_zero
  rw [hone] at hrec
  simpa only [show 2 * (m + 1) + 1 + 1 = 2 * ((m + 1) + 1) by omega]
    using hrec

/-- A named nonsplit shell state in the next even rank gives the exact
odd-to-even order multiplier. -/
theorem evenIdentityNonsplitNonzero_mul_oddOrthogonal_eq_nextEven
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (h : EvenIdentityNonsplitShellCardinality K (m + 1)) :
    evenIdentityNonsplitNonzero (Nat.card K) (m + 1) *
        Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (m + 1) + 1))
            (Fin (2 * (m + 1) + 1)) K)) =
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * ((m + 1) + 1)))
          (Fin (2 * ((m + 1) + 1))) K)) := by
  have hrec := natCard_identityFixedNorm_mul_identityOrthogonal_eq
    (n := 2 * (m + 1) + 1) hchar
  have hone := h.2 (1 : K) one_ne_zero
  rw [hone] at hrec
  simpa only [show 2 * (m + 1) + 1 + 1 = 2 * ((m + 1) + 1) by omega]
    using hrec

end PositiveDefiniteIntegralLattice
