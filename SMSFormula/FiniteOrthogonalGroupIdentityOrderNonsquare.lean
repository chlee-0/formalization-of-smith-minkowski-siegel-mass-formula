import SMSFormula.FiniteOrthogonalGroupIdentityOrderSquare

/-!
# Identity-form orthogonal-group orders when `-1` is nonsquare

When `-1` is nonsquare, the even identity form alternates between nonsplit and
split orientations.  A paired induction tracks a complete two-step cycle:
two even cardinalities and the odd cardinality following each of them.  Every
step uses an orbit--stabilizer recurrence and a closed-order arithmetic
identity; no natural multiplier is cancelled.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- If `-1` is nonsquare, the identity orthogonal-group orders occur in the
four-term cycle indexed by `r`: nonsplit even and its following odd order,
then split even and its following odd order. -/
theorem natCard_identityOrthogonalGroups_eq_closedExpressions_of_neg_one_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hneg : ∀ x : K, x ^ 2 ≠ -1) :
    ∀ r : ℕ,
      Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (2 * r + 1)))
            (Fin (2 * (2 * r + 1))) K)) =
        nonsplitEvenIdentityOrthogonalOrderExpression
          (Nat.card K) (2 * r + 1) ∧
      Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (2 * r + 1) + 1))
            (Fin (2 * (2 * r + 1) + 1)) K)) =
        oddIdentityOrthogonalOrderExpression (Nat.card K) (2 * r + 1) ∧
      Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (2 * r + 2)))
            (Fin (2 * (2 * r + 2))) K)) =
        splitEvenIdentityOrthogonalOrderExpression
          (Nat.card K) (2 * r + 2) ∧
      Nat.card (finiteGramOrthogonalGroup
          (1 : Matrix (Fin (2 * (2 * r + 2) + 1))
            (Fin (2 * (2 * r + 2) + 1)) K)) =
        oddIdentityOrthogonalOrderExpression (Nat.card K) (2 * r + 2) := by
  intro r
  induction r with
  | zero =>
      have heven0 :=
        natCard_rankTwoIdentityOrthogonalGroup_eq_nonsplitExpression
          hchar hneg
      have hrecOdd0 :=
        nonsplitIdentityEvenToOddOrthogonalOrderMultiplier_of_neg_one_nonsquare_even
          hchar hq hneg 0
      have hodd0 :
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin 3) (Fin 3) K)) =
            oddIdentityOrthogonalOrderExpression (Nat.card K) 1 := by
        calc
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin 3) (Fin 3) K)) =
              ((Nat.card K) ^ 2 - Nat.card K) *
                Nat.card (finiteGramOrthogonalGroup
                  (1 : Matrix (Fin 2) (Fin 2) K)) := by
            simpa using hrecOdd0.symm
          _ = ((Nat.card K) ^ (2 * 1) - (Nat.card K) ^ 1) *
                nonsplitEvenIdentityOrthogonalOrderExpression
                  (Nat.card K) 1 := by
            rw [heven0]
            norm_num
          _ = oddIdentityOrthogonalOrderExpression (Nat.card K) 1 :=
            nonsplitEvenToOddOrthogonalOrderExpression
              (Nat.card K) (by omega)
      have hshell1 :=
        (evenIdentityShellCardinality_pair_of_neg_one_nonsquare
          hchar hq hneg 0).2
      have hrecEven1 :=
        evenIdentitySplitNonzero_mul_oddOrthogonal_eq_nextEven
          hchar 0 hshell1
      have heven1 :
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin 4) (Fin 4) K)) =
            splitEvenIdentityOrthogonalOrderExpression (Nat.card K) 2 := by
        calc
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin 4) (Fin 4) K)) =
              evenIdentitySplitNonzero (Nat.card K) 1 *
                Nat.card (finiteGramOrthogonalGroup
                  (1 : Matrix (Fin 3) (Fin 3) K)) := by
            simpa using hrecEven1.symm
          _ = evenIdentitySplitNonzero (Nat.card K) 1 *
                oddIdentityOrthogonalOrderExpression (Nat.card K) 1 := by
            rw [hodd0]
          _ = splitEvenIdentityOrthogonalOrderExpression (Nat.card K) 2 :=
            oddToSplitEvenOrthogonalOrderExpression (Nat.card K) 1
      have hrecOdd1 :=
        splitIdentityEvenToOddOrthogonalOrderMultiplier_of_neg_one_nonsquare_odd
          hchar hq hneg 0
      have hodd1 :
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin 5) (Fin 5) K)) =
            oddIdentityOrthogonalOrderExpression (Nat.card K) 2 := by
        calc
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin 5) (Fin 5) K)) =
              ((Nat.card K) ^ 4 + (Nat.card K) ^ 2) *
                Nat.card (finiteGramOrthogonalGroup
                  (1 : Matrix (Fin 4) (Fin 4) K)) := by
            simpa using hrecOdd1.symm
          _ = ((Nat.card K) ^ (2 * 2) + (Nat.card K) ^ 2) *
                splitEvenIdentityOrthogonalOrderExpression
                  (Nat.card K) 2 := by rw [heven1]
          _ = oddIdentityOrthogonalOrderExpression (Nat.card K) 2 :=
            splitEvenToOddOrthogonalOrderExpression
              (Nat.card K) (by omega)
      exact ⟨by simpa using heven0, by simpa using hodd0,
        by simpa using heven1, by simpa using hodd1⟩
  | succ r ih =>
      have hshellNonsplit :=
        (evenIdentityShellCardinality_pair_of_neg_one_nonsquare
          hchar hq hneg (r + 1)).1
      have hrecEvenNonsplit :=
        evenIdentityNonsplitNonzero_mul_oddOrthogonal_eq_nextEven
          hchar (2 * r + 1) hshellNonsplit
      have hevenNonsplit :
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * (2 * r + 3)))
                (Fin (2 * (2 * r + 3))) K)) =
            nonsplitEvenIdentityOrthogonalOrderExpression
              (Nat.card K) (2 * r + 3) := by
        calc
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * (2 * r + 3)))
                (Fin (2 * (2 * r + 3))) K)) =
              evenIdentityNonsplitNonzero (Nat.card K) (2 * r + 2) *
                Nat.card (finiteGramOrthogonalGroup
                  (1 : Matrix (Fin (2 * (2 * r + 2) + 1))
                    (Fin (2 * (2 * r + 2) + 1)) K)) := by
            simpa only [show 2 * r + 1 + 1 = 2 * r + 2 by omega,
              show 2 * ((2 * r + 1) + 1) + 1 =
                2 * (2 * r + 2) + 1 by omega,
              show 2 * (((2 * r + 1) + 1) + 1) =
                2 * (2 * r + 3) by omega] using hrecEvenNonsplit.symm
          _ = evenIdentityNonsplitNonzero (Nat.card K) (2 * r + 2) *
                oddIdentityOrthogonalOrderExpression
                  (Nat.card K) (2 * r + 2) := by rw [ih.2.2.2]
          _ = nonsplitEvenIdentityOrthogonalOrderExpression
                (Nat.card K) (2 * r + 3) :=
            oddToNonsplitEvenOrthogonalOrderExpression
              (Nat.card K) (2 * r + 2)
      have hrecOddNonsplit :=
        nonsplitIdentityEvenToOddOrthogonalOrderMultiplier_of_neg_one_nonsquare_even
          hchar hq hneg (r + 1)
      have hoddNonsplit :
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * (2 * r + 3) + 1))
                (Fin (2 * (2 * r + 3) + 1)) K)) =
            oddIdentityOrthogonalOrderExpression
              (Nat.card K) (2 * r + 3) := by
        calc
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * (2 * r + 3) + 1))
                (Fin (2 * (2 * r + 3) + 1)) K)) =
              ((Nat.card K) ^ (2 * (2 * r + 3)) -
                (Nat.card K) ^ (2 * r + 3)) *
                Nat.card (finiteGramOrthogonalGroup
                  (1 : Matrix (Fin (2 * (2 * r + 3)))
                    (Fin (2 * (2 * r + 3))) K)) := by
            simpa only [show 2 * (r + 1) + 1 = 2 * r + 3 by omega]
              using hrecOddNonsplit.symm
          _ = ((Nat.card K) ^ (2 * (2 * r + 3)) -
                (Nat.card K) ^ (2 * r + 3)) *
                nonsplitEvenIdentityOrthogonalOrderExpression
                  (Nat.card K) (2 * r + 3) := by rw [hevenNonsplit]
          _ = oddIdentityOrthogonalOrderExpression
                (Nat.card K) (2 * r + 3) :=
            nonsplitEvenToOddOrthogonalOrderExpression
              (Nat.card K) (by omega)
      have hshellSplit :=
        (evenIdentityShellCardinality_pair_of_neg_one_nonsquare
          hchar hq hneg (r + 1)).2
      have hrecEvenSplit :=
        evenIdentitySplitNonzero_mul_oddOrthogonal_eq_nextEven
          hchar (2 * r + 2) hshellSplit
      have hevenSplit :
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * (2 * r + 4)))
                (Fin (2 * (2 * r + 4))) K)) =
            splitEvenIdentityOrthogonalOrderExpression
              (Nat.card K) (2 * r + 4) := by
        calc
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * (2 * r + 4)))
                (Fin (2 * (2 * r + 4))) K)) =
              evenIdentitySplitNonzero (Nat.card K) (2 * r + 3) *
                Nat.card (finiteGramOrthogonalGroup
                  (1 : Matrix (Fin (2 * (2 * r + 3) + 1))
                    (Fin (2 * (2 * r + 3) + 1)) K)) := by
            simpa only [show 2 * r + 2 + 1 = 2 * r + 3 by omega,
              show 2 * ((2 * r + 2) + 1) + 1 =
                2 * (2 * r + 3) + 1 by omega,
              show 2 * (((2 * r + 2) + 1) + 1) =
                2 * (2 * r + 4) by omega] using hrecEvenSplit.symm
          _ = evenIdentitySplitNonzero (Nat.card K) (2 * r + 3) *
                oddIdentityOrthogonalOrderExpression
                  (Nat.card K) (2 * r + 3) := by rw [hoddNonsplit]
          _ = splitEvenIdentityOrthogonalOrderExpression
                (Nat.card K) (2 * r + 4) :=
            oddToSplitEvenOrthogonalOrderExpression
              (Nat.card K) (2 * r + 3)
      have hrecOddSplit :=
        splitIdentityEvenToOddOrthogonalOrderMultiplier_of_neg_one_nonsquare_odd
          hchar hq hneg (r + 1)
      have hoddSplit :
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * (2 * r + 4) + 1))
                (Fin (2 * (2 * r + 4) + 1)) K)) =
            oddIdentityOrthogonalOrderExpression
              (Nat.card K) (2 * r + 4) := by
        calc
          Nat.card (finiteGramOrthogonalGroup
              (1 : Matrix (Fin (2 * (2 * r + 4) + 1))
                (Fin (2 * (2 * r + 4) + 1)) K)) =
              ((Nat.card K) ^ (2 * (2 * r + 4)) +
                (Nat.card K) ^ (2 * r + 4)) *
                Nat.card (finiteGramOrthogonalGroup
                  (1 : Matrix (Fin (2 * (2 * r + 4)))
                    (Fin (2 * (2 * r + 4))) K)) := by
            simpa only [show 2 * (r + 1) + 2 = 2 * r + 4 by omega]
              using hrecOddSplit.symm
          _ = ((Nat.card K) ^ (2 * (2 * r + 4)) +
                (Nat.card K) ^ (2 * r + 4)) *
                splitEvenIdentityOrthogonalOrderExpression
                  (Nat.card K) (2 * r + 4) := by rw [hevenSplit]
          _ = oddIdentityOrthogonalOrderExpression
                (Nat.card K) (2 * r + 4) :=
            splitEvenToOddOrthogonalOrderExpression
              (Nat.card K) (by omega)
      exact ⟨by simpa only [Nat.succ_eq_add_one,
          show 2 * (r + 1) + 1 = 2 * r + 3 by omega] using hevenNonsplit,
        by simpa only [Nat.succ_eq_add_one,
          show 2 * (r + 1) + 1 = 2 * r + 3 by omega] using hoddNonsplit,
        by simpa only [Nat.succ_eq_add_one,
          show 2 * (r + 1) + 2 = 2 * r + 4 by omega] using hevenSplit,
        by simpa only [Nat.succ_eq_add_one,
          show 2 * (r + 1) + 2 = 2 * r + 4 by omega] using hoddSplit⟩

end PositiveDefiniteIntegralLattice
