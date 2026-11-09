import SMSFormula.FiniteOrthogonalGroupStandardModelTransport
import SMSFormula.FiniteOrthogonalGroupIdentityOrder

/-!
# Odd-dimensional weighted-identity orthogonal-group orders

For a nonzero head weight, the residual targets `d - d*z^2` and
`1 - z^2` vanish at exactly the same leading coordinates.  An even-dimensional
identity tail has a uniform shell cardinality away from zero, so the weighted
and unweighted norm shells have the same size.  The two literal
orbit--stabilizer recurrences then identify the weighted odd-dimensional order
with the already completed identity-form order.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Scaling `1-z²` by a nonzero field element preserves the closed shell sum
whenever the tail has one cardinality at zero and another at every nonzero
target. -/
theorem sum_natCard_finiteGramNormVectors_sub_mul_sq_of_constant_nonzero
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (a b : ℕ)
    (hzero : Nat.card (finiteGramNormVectors B 0) = a)
    (hnonzero : ∀ c : K, c ≠ 0 →
      Nat.card (finiteGramNormVectors B c) = b)
    (d : K) (hd : d ≠ 0) :
    ∑ z : K, Nat.card (finiteGramNormVectors B (d - d * z ^ 2)) =
      2 * a + (Nat.card K - 2) * b := by
  classical
  calc
    ∑ z : K, Nat.card (finiteGramNormVectors B (d - d * z ^ 2)) =
        ∑ z : K, Nat.card (finiteGramNormVectors B (1 - z ^ 2)) := by
      apply Finset.sum_congr rfl
      intro z _
      have hfactor : d - d * z ^ 2 = d * (1 - z ^ 2) := by ring
      by_cases hz : 1 - z ^ 2 = 0
      · have hdz : d - d * z ^ 2 = 0 := by rw [hfactor, hz, mul_zero]
        rw [hdz, hz, hzero]
      · have hdz : d - d * z ^ 2 ≠ 0 := by
          rw [hfactor]
          exact mul_ne_zero hd hz
        rw [hnonzero _ hdz, hnonzero _ hz]
    _ = 2 * a + (Nat.card K - 2) * b :=
      sum_natCard_finiteGramNormVectors_one_sub_sq_of_constant_nonzero
        hchar B a b hzero hnonzero

/-- For a tail whose nonzero shells are uniform, a nonzero head weight gives
the same distinguished fixed-norm shell cardinality as head weight one. -/
theorem natCard_finSuccGramBlock_fixedNorm_eq_one_of_constant_nonzero
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (a b : ℕ)
    (hzero : Nat.card (finiteGramNormVectors B 0) = a)
    (hnonzero : ∀ c : K, c ≠ 0 →
      Nat.card (finiteGramNormVectors B c) = b)
    (d : K) (hd : d ≠ 0) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock d B) d) =
      Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) 1) := by
  rw [natCard_finiteGramNormVectors_finSucc_eq_sum,
    natCard_finiteGramNormVectors_finSucc_eq_sum]
  calc
    ∑ z : K, Nat.card (finiteGramNormVectors B (d - d * z ^ 2)) =
        2 * a + (Nat.card K - 2) * b :=
      sum_natCard_finiteGramNormVectors_sub_mul_sq_of_constant_nonzero
        hchar B a b hzero hnonzero d hd
    _ = ∑ z : K, Nat.card (finiteGramNormVectors B (1 - 1 * z ^ 2)) := by
      simpa only [one_mul] using
        (sum_natCard_finiteGramNormVectors_one_sub_sq_of_constant_nonzero
          hchar B a b hzero hnonzero).symm

/-- Every positive odd-dimensional weighted-identity orthogonal group has the
standard odd order expression.  The result is independent of the nonzero head
weight. -/
theorem natCard_oddWeightedIdentityOrthogonalGroup_eq_closedExpression
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (s : ℕ) (hs : 0 < s) (d : K) (hd : d ≠ 0) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * s) d)) =
      oddIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.mpr hs
  have close_of_state (a b : ℕ)
      (hstate : ZeroNonzeroShellCardinality
        (1 : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K) a b) :
      Nat.card (finiteGramOrthogonalGroup
          (finSuccIdentityGramMatrix (n := 2 * (m + 1)) d)) =
        oddIdentityOrthogonalOrderExpression (Nat.card K) (m + 1) := by
    have hshell :=
      natCard_finSuccGramBlock_fixedNorm_eq_one_of_constant_nonzero
        hchar (1 : Matrix (Fin (2 * (m + 1)))
          (Fin (2 * (m + 1))) K) a b hstate.1 hstate.2 d hd
    have hweighted :=
      natCard_finSuccIdentityFixedNorm_mul_identityOrthogonal_eq
        (n := 2 * (m + 1)) hchar d hd
    have hidentity := natCard_identityFixedNorm_mul_identityOrthogonal_eq
      (n := 2 * (m + 1)) hchar
    have hgroups :
        Nat.card (finiteGramOrthogonalGroup
            (finSuccIdentityGramMatrix (n := 2 * (m + 1)) d)) =
          Nat.card (finiteGramOrthogonalGroup
            (1 : Matrix (Fin (2 * (m + 1) + 1))
              (Fin (2 * (m + 1) + 1)) K)) := by
      calc
        Nat.card (finiteGramOrthogonalGroup
            (finSuccIdentityGramMatrix (n := 2 * (m + 1)) d)) =
            Nat.card (finiteGramNormVectors
                (finSuccIdentityGramMatrix (n := 2 * (m + 1)) d) d) *
              Nat.card (finiteGramOrthogonalGroup
                (1 : Matrix (Fin (2 * (m + 1)))
                  (Fin (2 * (m + 1))) K)) := hweighted.symm
        _ = Nat.card (finiteGramNormVectors
                (1 : Matrix (Fin (2 * (m + 1) + 1))
                  (Fin (2 * (m + 1) + 1)) K) 1) *
              Nat.card (finiteGramOrthogonalGroup
                (1 : Matrix (Fin (2 * (m + 1)))
                  (Fin (2 * (m + 1))) K)) := by
            simpa only [finSuccIdentityGramMatrix, finSuccGramBlock_one] using
              congrArg (fun x => x * Nat.card (finiteGramOrthogonalGroup
                (1 : Matrix (Fin (2 * (m + 1)))
                  (Fin (2 * (m + 1))) K))) hshell
        _ = Nat.card (finiteGramOrthogonalGroup
            (1 : Matrix (Fin (2 * (m + 1) + 1))
              (Fin (2 * (m + 1) + 1)) K)) := hidentity
    rw [hgroups]
    exact natCard_oddIdentityOrthogonalGroup_eq_closedExpression
      hchar hq (m + 1) (by omega)
  by_cases hsq : ∃ t : K, t ^ 2 = -1
  · obtain ⟨t, ht⟩ := hsq
    exact close_of_state
      (evenIdentitySplitZero (Nat.card K) m)
      (evenIdentitySplitNonzero (Nat.card K) m)
      (evenIdentitySplitShellCardinality_of_neg_one_square
        hchar hq t ht m)
  · have hneg : ∀ x : K, x ^ 2 ≠ -1 := by
      intro x hx
      exact hsq ⟨x, hx⟩
    obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' m
    · subst m
      exact close_of_state
        (evenIdentityNonsplitZero (Nat.card K) (2 * r))
        (evenIdentityNonsplitNonzero (Nat.card K) (2 * r))
        ((evenIdentityShellCardinality_pair_of_neg_one_nonsquare
          hchar hq hneg r).1)
    · subst m
      exact close_of_state
        (evenIdentitySplitZero (Nat.card K) (2 * r + 1))
        (evenIdentitySplitNonzero (Nat.card K) (2 * r + 1))
        ((evenIdentityShellCardinality_pair_of_neg_one_nonsquare
          hchar hq hneg r).2)

end PositiveDefiniteIntegralLattice
