import SMSFormula.FiniteOrthogonalGroupClosedOrderArithmetic

/-!
# Identity-form orthogonal-group orders when `-1` is square

The binary arbitrary-form order theorem gives the rank-two base.  The actual
orbit--stabilizer recurrences and the closed order-expression arithmetic then
give a mutual induction for every positive even identity rank and the
following odd rank.  No recurrence multiplier is cancelled.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-! ### Rank-two cardinal bases -/

/-- If `-1` is square, the rank-two identity orthogonal group has the standard
split even order expression. -/
theorem natCard_rankTwoIdentityOrthogonalGroup_eq_splitExpression
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (t : K) (ht : t ^ 2 = -1) :
    Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin 2) (Fin 2) K)) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) 1 := by
  have ht' : t * t =
      -(1 : Matrix (Fin 2) (Fin 2) K).det := by
    simpa [pow_two] using ht
  have hcard := natCard_binaryFiniteGramOrthogonalGroup_of_neg_det_eq_sq
    (1 : Matrix (Fin 2) (Fin 2) K) (by simp) (by simp) hchar t ht'
  rw [hcard]
  simp [splitEvenIdentityOrthogonalOrderExpression,
    finiteOrthogonalOrderEulerProduct]

/-- If `-1` is nonsquare, the rank-two identity orthogonal group has the
standard nonsplit even order expression. -/
theorem natCard_rankTwoIdentityOrthogonalGroup_eq_nonsplitExpression
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hneg : ∀ x : K, x ^ 2 ≠ -1) :
    Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin 2) (Fin 2) K)) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) 1 := by
  have hneg' : ∀ x : K,
      x ^ 2 ≠ -(1 : Matrix (Fin 2) (Fin 2) K).det := by
    intro x
    simpa using hneg x
  have hcard := natCard_binaryFiniteGramOrthogonalGroup_of_neg_det_nonsquare
    (1 : Matrix (Fin 2) (Fin 2) K) (by simp) hneg' hchar
  rw [hcard]
  simp [nonsplitEvenIdentityOrthogonalOrderExpression,
    finiteOrthogonalOrderEulerProduct]

/-! ### Square-`-1` mutual order induction -/

/-- Under a square root of `-1`, the identity orthogonal groups in ranks
`2(m+1)` and `2(m+1)+1` have respectively the standard split-even and odd
orders. -/
theorem natCard_identityOrthogonalGroups_eq_closedExpressions_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (t : K) (ht : t ^ 2 = -1) :
    ∀ m : ℕ,
      Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K)) =
        splitEvenIdentityOrthogonalOrderExpression (Nat.card K) (m + 1) ∧
      Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (m + 1) + 1))
            (Fin (2 * (m + 1) + 1)) K)) =
        oddIdentityOrthogonalOrderExpression (Nat.card K) (m + 1) := by
  intro m
  induction m with
  | zero =>
      have heven := natCard_rankTwoIdentityOrthogonalGroup_eq_splitExpression
        hchar t ht
      have hrec :=
        splitIdentityEvenToOddOrthogonalOrderMultiplier_of_neg_one_square
          hchar hq t ht 0
      have hodd :
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin 3) (Fin 3) K)) =
            oddIdentityOrthogonalOrderExpression (Nat.card K) 1 := by
        calc
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin 3) (Fin 3) K)) =
              ((Nat.card K) ^ 2 + Nat.card K) *
                Nat.card (finiteGramOrthogonalGroup
                  (1 : Matrix (Fin 2) (Fin 2) K)) := by
            simpa using hrec.symm
          _ = ((Nat.card K) ^ (2 * 1) + (Nat.card K) ^ 1) *
                splitEvenIdentityOrthogonalOrderExpression (Nat.card K) 1 := by
            rw [heven]
            norm_num
          _ = oddIdentityOrthogonalOrderExpression (Nat.card K) 1 :=
            splitEvenToOddOrthogonalOrderExpression (Nat.card K) (by omega)
      constructor
      · simpa using heven
      · simpa using hodd
  | succ m ih =>
      have hshell := evenIdentitySplitShellCardinality_of_neg_one_square
        hchar hq t ht (m + 1)
      have hrecEven :=
        evenIdentitySplitNonzero_mul_oddOrthogonal_eq_nextEven
          hchar m hshell
      have hevenNext :
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * ((m + 1) + 1)))
                (Fin (2 * ((m + 1) + 1))) K)) =
            splitEvenIdentityOrthogonalOrderExpression
              (Nat.card K) ((m + 1) + 1) := by
        calc
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * ((m + 1) + 1)))
                (Fin (2 * ((m + 1) + 1))) K)) =
              evenIdentitySplitNonzero (Nat.card K) (m + 1) *
                Nat.card (finiteGramOrthogonalGroup
                  (1 : Matrix (Fin (2 * (m + 1) + 1))
                    (Fin (2 * (m + 1) + 1)) K)) := hrecEven.symm
          _ = evenIdentitySplitNonzero (Nat.card K) (m + 1) *
                oddIdentityOrthogonalOrderExpression (Nat.card K) (m + 1) := by
            rw [ih.2]
          _ = splitEvenIdentityOrthogonalOrderExpression
                (Nat.card K) ((m + 1) + 1) :=
            oddToSplitEvenOrthogonalOrderExpression (Nat.card K) (m + 1)
      have hrecOdd :=
        splitIdentityEvenToOddOrthogonalOrderMultiplier_of_neg_one_square
          hchar hq t ht (m + 1)
      have hoddNext :
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * ((m + 1) + 1) + 1))
                (Fin (2 * ((m + 1) + 1) + 1)) K)) =
            oddIdentityOrthogonalOrderExpression
              (Nat.card K) ((m + 1) + 1) := by
        calc
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * ((m + 1) + 1) + 1))
                (Fin (2 * ((m + 1) + 1) + 1)) K)) =
              ((Nat.card K) ^ (2 * ((m + 1) + 1)) +
                (Nat.card K) ^ ((m + 1) + 1)) *
                Nat.card (finiteGramOrthogonalGroup
                  (1 : Matrix (Fin (2 * ((m + 1) + 1)))
                    (Fin (2 * ((m + 1) + 1))) K)) := hrecOdd.symm
          _ = ((Nat.card K) ^ (2 * ((m + 1) + 1)) +
                (Nat.card K) ^ ((m + 1) + 1)) *
                splitEvenIdentityOrthogonalOrderExpression
                  (Nat.card K) ((m + 1) + 1) := by
            rw [hevenNext]
          _ = oddIdentityOrthogonalOrderExpression
                (Nat.card K) ((m + 1) + 1) :=
            splitEvenToOddOrthogonalOrderExpression
              (Nat.card K) (by omega)
      constructor
      · simpa only [Nat.succ_eq_add_one] using hevenNext
      · simpa only [Nat.succ_eq_add_one] using hoddNext

end PositiveDefiniteIntegralLattice
