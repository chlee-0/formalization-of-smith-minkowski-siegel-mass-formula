import SMSFormula.FiniteOrthogonalGroupIdentityOrderNonsquare

/-!
# Arbitrary-rank identity-form orthogonal-group orders

The square and nonsquare `-1` inductions are packaged here into clean
arbitrary-rank corollaries.  In odd dimension the order is independent of the
square class of `-1`.  In even dimension the square case is always split,
while the nonsquare case alternates with the parity of the half-rank.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Every positive odd-dimensional identity orthogonal group has the standard
odd order expression, independently of whether `-1` is square. -/
theorem natCard_oddIdentityOrthogonalGroup_eq_closedExpression
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (s : ℕ) (hs : 0 < s) :
    Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * s + 1)) (Fin (2 * s + 1)) K)) =
      oddIdentityOrthogonalOrderExpression (Nat.card K) s := by
  by_cases hsq : ∃ t : K, t ^ 2 = -1
  · obtain ⟨t, ht⟩ := hsq
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.mpr hs
    exact (natCard_identityOrthogonalGroups_eq_closedExpressions_of_neg_one_square
      hchar hq t ht m).2
  · have hneg : ∀ x : K, x ^ 2 ≠ -1 := by
      intro x hx
      exact hsq ⟨x, hx⟩
    obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' s
    · subst s
      have hrpos : 0 < r := by omega
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_one.mpr hrpos
      simpa only [show 2 * (u + 1) = 2 * u + 2 by omega] using
        (natCard_identityOrthogonalGroups_eq_closedExpressions_of_neg_one_nonsquare
          hchar hq hneg u).2.2.2
    · subst s
      simpa only using
        (natCard_identityOrthogonalGroups_eq_closedExpressions_of_neg_one_nonsquare
          hchar hq hneg r).2.1

/-- If `-1` is square, every positive even-dimensional identity orthogonal
group has the standard split order expression. -/
theorem natCard_evenIdentityOrthogonalGroup_eq_splitExpression_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (t : K) (ht : t ^ 2 = -1) (s : ℕ) (hs : 0 < s) :
    Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * s)) (Fin (2 * s)) K)) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.mpr hs
  exact (natCard_identityOrthogonalGroups_eq_closedExpressions_of_neg_one_square
    hchar hq t ht m).1

/-- If `-1` is nonsquare and the half-rank is odd, the even-dimensional
identity orthogonal group has the standard nonsplit order expression. -/
theorem natCard_evenIdentityOrthogonalGroup_eq_nonsplitExpression_of_neg_one_nonsquare_odd
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hneg : ∀ x : K, x ^ 2 ≠ -1) (r : ℕ) :
    Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * (2 * r + 1)))
          (Fin (2 * (2 * r + 1))) K)) =
      nonsplitEvenIdentityOrthogonalOrderExpression
        (Nat.card K) (2 * r + 1) :=
  (natCard_identityOrthogonalGroups_eq_closedExpressions_of_neg_one_nonsquare
    hchar hq hneg r).1

/-- If `-1` is nonsquare and the positive half-rank is even, the
even-dimensional identity orthogonal group has the standard split order
expression. -/
theorem natCard_evenIdentityOrthogonalGroup_eq_splitExpression_of_neg_one_nonsquare_even
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hneg : ∀ x : K, x ^ 2 ≠ -1) (r : ℕ) :
    Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * (2 * r + 2)))
          (Fin (2 * (2 * r + 2))) K)) =
      splitEvenIdentityOrthogonalOrderExpression
        (Nat.card K) (2 * r + 2) :=
  (natCard_identityOrthogonalGroups_eq_closedExpressions_of_neg_one_nonsquare
    hchar hq hneg r).2.2.1

/-- Parity-facing form of the nonsquare odd-half-rank identity order. -/
theorem natCard_evenIdentityOrthogonalGroup_eq_nonsplitExpression_of_neg_one_nonsquare_of_odd
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hneg : ∀ x : K, x ^ 2 ≠ -1) (s : ℕ) (hs : Odd s) :
    Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * s)) (Fin (2 * s)) K)) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨r, rfl⟩ := hs
  simpa only [two_mul, add_assoc] using
    natCard_evenIdentityOrthogonalGroup_eq_nonsplitExpression_of_neg_one_nonsquare_odd
      hchar hq hneg r

/-- Parity-facing form of the nonsquare positive even-half-rank identity
order. -/
theorem natCard_evenIdentityOrthogonalGroup_eq_splitExpression_of_neg_one_nonsquare_of_even
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hneg : ∀ x : K, x ^ 2 ≠ -1)
    (s : ℕ) (hspos : 0 < s) (hs : Even s) :
    Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (2 * s)) (Fin (2 * s)) K)) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨r, rfl⟩ := hs
  have hrpos : 0 < r := by omega
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_one.mpr hrpos
  have hdim : u + 1 + (u + 1) = 2 * u + 2 := by omega
  rw [hdim]
  exact
    natCard_evenIdentityOrthogonalGroup_eq_splitExpression_of_neg_one_nonsquare_even
      hchar hq hneg u

end PositiveDefiniteIntegralLattice
