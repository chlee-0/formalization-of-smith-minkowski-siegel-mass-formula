import SMSFormula.FiniteOrthogonalGroupIdentityShellRankTwoBase

/-!
# Mutual induction for identity-form shell cardinalities

The binary identity shell supplies the base at dimension two.  The four
completed two-dimension shell transitions are transported to literal identity
matrices and then iterated.  When `-1` is square the split orientation is
preserved.  When `-1` is nonsquare the split and nonsplit orientations
alternate, so the induction is packaged in pairs.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The named larger-zero shell state for the identity form of dimension
`2 * (m + 1)`. -/
def EvenIdentitySplitShellCardinality
    (K : Type*) [Field K] [Fintype K] (m : ℕ) : Prop :=
  ZeroNonzeroShellCardinality
    (1 : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K)
    (evenIdentitySplitZero (Nat.card K) m)
    (evenIdentitySplitNonzero (Nat.card K) m)

/-- The named larger-nonzero shell state for the identity form of dimension
`2 * (m + 1)`. -/
def EvenIdentityNonsplitShellCardinality
    (K : Type*) [Field K] [Fintype K] (m : ℕ) : Prop :=
  ZeroNonzeroShellCardinality
    (1 : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K)
    (evenIdentityNonsplitZero (Nat.card K) m)
    (evenIdentityNonsplitNonzero (Nat.card K) m)

/-! ### Identity-specialized two-dimension successors -/

/-- For identity forms, the split state remains split after two dimensions
when `-1` is square. -/
theorem evenIdentitySplitShellCardinality_succ_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (m : ℕ) (h : EvenIdentitySplitShellCardinality K m)
    (t : K) (ht : t ^ 2 = -1) :
    EvenIdentitySplitShellCardinality K (m + 1) := by
  have hblocks :=
    zeroNonzeroShellCardinality_twoStep_of_evenIdentitySplit_of_neg_one_square
      hchar (1 : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K)
      m hq h t ht
  have hid := zeroNonzeroShellCardinality_identity_of_twoBlocks hblocks
  simpa only [EvenIdentitySplitShellCardinality,
    show 2 * (m + 1) + 2 = 2 * ((m + 1) + 1) by omega] using hid

/-- For identity forms, the split state becomes nonsplit after two dimensions
when `-1` is nonsquare. -/
theorem evenIdentityNonsplitShellCardinality_succ_of_split_of_neg_one_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (m : ℕ) (h : EvenIdentitySplitShellCardinality K m)
    (hneg : ∀ r : K, r ^ 2 ≠ -1) :
    EvenIdentityNonsplitShellCardinality K (m + 1) := by
  have hblocks :=
    zeroNonzeroShellCardinality_twoStep_of_evenIdentitySplit_of_neg_one_nonsquare
      hchar (1 : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K)
      m hq h hneg
  have hid := zeroNonzeroShellCardinality_identity_of_twoBlocks hblocks
  simpa only [EvenIdentityNonsplitShellCardinality,
    show 2 * (m + 1) + 2 = 2 * ((m + 1) + 1) by omega] using hid

/-- For identity forms, the nonsplit state remains nonsplit after two
dimensions when `-1` is square. -/
theorem evenIdentityNonsplitShellCardinality_succ_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (m : ℕ) (h : EvenIdentityNonsplitShellCardinality K m)
    (t : K) (ht : t ^ 2 = -1) :
    EvenIdentityNonsplitShellCardinality K (m + 1) := by
  have hblocks :=
    zeroNonzeroShellCardinality_twoStep_of_evenIdentityNonsplit_of_neg_one_square
      hchar (1 : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K)
      m hq h t ht
  have hid := zeroNonzeroShellCardinality_identity_of_twoBlocks hblocks
  simpa only [EvenIdentityNonsplitShellCardinality,
    show 2 * (m + 1) + 2 = 2 * ((m + 1) + 1) by omega] using hid

/-- For identity forms, the nonsplit state becomes split after two dimensions
when `-1` is nonsquare. -/
theorem evenIdentitySplitShellCardinality_succ_of_nonsplit_of_neg_one_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (m : ℕ) (h : EvenIdentityNonsplitShellCardinality K m)
    (hneg : ∀ r : K, r ^ 2 ≠ -1) :
    EvenIdentitySplitShellCardinality K (m + 1) := by
  have hblocks :=
    zeroNonzeroShellCardinality_twoStep_of_evenIdentityNonsplit_of_neg_one_nonsquare
      hchar (1 : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K)
      m hq h hneg
  have hid := zeroNonzeroShellCardinality_identity_of_twoBlocks hblocks
  simpa only [EvenIdentitySplitShellCardinality,
    show 2 * (m + 1) + 2 = 2 * ((m + 1) + 1) by omega] using hid

/-! ### Closed identity-shell induction -/

/-- If `-1` is square, every positive even-dimensional identity form has the
named split shell state. -/
theorem evenIdentitySplitShellCardinality_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (t : K) (ht : t ^ 2 = -1) :
    ∀ m : ℕ, EvenIdentitySplitShellCardinality K m := by
  intro m
  induction m with
  | zero =>
      simpa only [EvenIdentitySplitShellCardinality] using
        zeroNonzeroShellCardinality_rankTwoIdentity_of_neg_one_square
          hchar hq t ht
  | succ m ih =>
      simpa only [Nat.succ_eq_add_one] using
        evenIdentitySplitShellCardinality_succ_of_neg_one_square
          hchar hq m ih t ht

/-- If `-1` is nonsquare, the identity-form shell orientation alternates:
the state at index `2r` is nonsplit and the state at index `2r+1` is split. -/
theorem evenIdentityShellCardinality_pair_of_neg_one_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hneg : ∀ x : K, x ^ 2 ≠ -1) :
    ∀ r : ℕ,
      EvenIdentityNonsplitShellCardinality K (2 * r) ∧
      EvenIdentitySplitShellCardinality K (2 * r + 1) := by
  intro r
  induction r with
  | zero =>
      have hbase : EvenIdentityNonsplitShellCardinality K 0 := by
        simpa only [EvenIdentityNonsplitShellCardinality] using
          zeroNonzeroShellCardinality_rankTwoIdentity_of_neg_one_nonsquare
            hchar hq hneg
      refine ⟨by simpa using hbase, ?_⟩
      simpa using
        evenIdentitySplitShellCardinality_succ_of_nonsplit_of_neg_one_nonsquare
          hchar hq 0 hbase hneg
  | succ r ih =>
      have hnonsplit : EvenIdentityNonsplitShellCardinality K (2 * r + 2) := by
        simpa only [show 2 * r + 1 + 1 = 2 * r + 2 by omega] using
          evenIdentityNonsplitShellCardinality_succ_of_split_of_neg_one_nonsquare
            hchar hq (2 * r + 1) ih.2 hneg
      have hsplit : EvenIdentitySplitShellCardinality K (2 * r + 3) := by
        simpa only [show 2 * r + 2 + 1 = 2 * r + 3 by omega] using
          evenIdentitySplitShellCardinality_succ_of_nonsplit_of_neg_one_nonsquare
            hchar hq (2 * r + 2) hnonsplit hneg
      constructor
      · simpa only [Nat.succ_eq_add_one,
          show 2 * (r + 1) = 2 * r + 2 by omega] using hnonsplit
      · simpa only [Nat.succ_eq_add_one,
          show 2 * (r + 1) + 1 = 2 * r + 3 by omega] using hsplit

end PositiveDefiniteIntegralLattice
