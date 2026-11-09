import SMSFormula.FiniteOrthogonalGroupWeightedEvenShell

/-!
# Even-dimensional weighted-identity orthogonal-group orders

The binary endpoint is obtained from the arbitrary binary Gram order theorem.
In higher rank, the completed identity-shell induction supplies the standard
root-affine or root-coaffine odd tail, and the four weighted-even branch
theorems give the closed split or nonsplit order.  The theorem-facing API keeps
the square class of `-1`, the parity of the half-rank, and the square class of
`-d` explicit; no character formula or cardinality inference is used.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-! ### Binary endpoint -/

/-- The rank-two weighted identity form has the split order when its negative
determinant is a square. -/
theorem natCard_rankTwoWeightedIdentityOrthogonalGroup_eq_splitExpression
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (d : K) (hd : d ≠ 0)
    (t : K) (ht : t ^ 2 = -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 1) d)) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) 1 := by
  have ht' : t * t =
      -(finSuccIdentityGramMatrix (n := 1) d).det := by
    simpa [pow_two, finSuccIdentityGramMatrix_det] using ht
  have hcard := natCard_binaryFiniteGramOrthogonalGroup_of_neg_det_eq_sq
    (finSuccIdentityGramMatrix (n := 1) d)
    (finSuccIdentityGramMatrix_isSymm d)
    (by simpa [finSuccIdentityGramMatrix_det] using hd)
    hchar t ht'
  rw [hcard]
  simp [splitEvenIdentityOrthogonalOrderExpression,
    finiteOrthogonalOrderEulerProduct]

/-- The rank-two weighted identity form has the nonsplit order when its
negative determinant is nonsquare. -/
theorem natCard_rankTwoWeightedIdentityOrthogonalGroup_eq_nonsplitExpression
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (d : K)
    (hneg : ∀ x : K, x ^ 2 ≠ -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 1) d)) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) 1 := by
  have hneg' : ∀ x : K,
      x ^ 2 ≠ -(finSuccIdentityGramMatrix (n := 1) d).det := by
    intro x
    simpa [finSuccIdentityGramMatrix_det] using hneg x
  have hcard := natCard_binaryFiniteGramOrthogonalGroup_of_neg_det_nonsquare
    (finSuccIdentityGramMatrix (n := 1) d)
    (finSuccIdentityGramMatrix_isSymm d) hneg' hchar
  rw [hcard]
  simp [nonsplitEvenIdentityOrthogonalOrderExpression,
    finiteOrthogonalOrderEulerProduct]

/-! ### Square `-1` -/

/-- When `-1` and `-d` are both square, every positive even weighted identity
rank has the split order. -/
theorem natCard_evenWeightedIdentityOrthogonalGroup_eq_split_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (u : K) (hu : u ^ 2 = -1)
    (s : ℕ) (hs : 0 < s) (d : K) (hd : d ≠ 0)
    (t : K) (ht : t ^ 2 = -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one.mpr hs
  cases r with
  | zero =>
      simpa using
        natCard_rankTwoWeightedIdentityOrthogonalGroup_eq_splitExpression
          hchar d hd t ht
  | succ m =>
      have heven := evenIdentitySplitShellCardinality_of_neg_one_square
        hchar hq u hu m
      have hroot :=
        rootAffineShellCardinality_finSuccGramBlock_of_evenIdentitySplit
          (1 : Matrix (Fin (2 * (m + 1)))
            (Fin (2 * (m + 1))) K) m hq heven
      have hroot' : RootAffineShellCardinality
          (1 : Matrix (Fin (2 * (m + 1) + 1))
            (Fin (2 * (m + 1) + 1)) K) 1
          (oddIdentityAffineBase (Nat.card K) m)
          (oddIdentityShellCorrection (Nat.card K) m) := by
        simpa only [finSuccGramBlock_one] using hroot
      simpa only [Nat.succ_eq_add_one,
        show 2 * ((m + 1) + 1) - 1 = 2 * (m + 1) + 1 by omega,
        show (m + 1) + 1 = m + 2 by omega] using
          natCard_weightedEvenOrthogonalGroup_eq_split_of_rootAffine_of_neg_square
            hchar hq m hroot' d hd t ht

/-- When `-1` is square and `-d` is nonsquare, every positive even weighted
identity rank has the nonsplit order. -/
theorem natCard_evenWeightedIdentityOrthogonalGroup_eq_nonsplit_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (u : K) (hu : u ^ 2 = -1)
    (s : ℕ) (hs : 0 < s) (d : K) (hd : d ≠ 0)
    (hneg : ∀ x : K, x ^ 2 ≠ -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one.mpr hs
  cases r with
  | zero =>
      simpa using
        natCard_rankTwoWeightedIdentityOrthogonalGroup_eq_nonsplitExpression
          hchar d hneg
  | succ m =>
      have heven := evenIdentitySplitShellCardinality_of_neg_one_square
        hchar hq u hu m
      have hroot :=
        rootAffineShellCardinality_finSuccGramBlock_of_evenIdentitySplit
          (1 : Matrix (Fin (2 * (m + 1)))
            (Fin (2 * (m + 1))) K) m hq heven
      have hroot' : RootAffineShellCardinality
          (1 : Matrix (Fin (2 * (m + 1) + 1))
            (Fin (2 * (m + 1) + 1)) K) 1
          (oddIdentityAffineBase (Nat.card K) m)
          (oddIdentityShellCorrection (Nat.card K) m) := by
        simpa only [finSuccGramBlock_one] using hroot
      simpa only [Nat.succ_eq_add_one,
        show 2 * ((m + 1) + 1) - 1 = 2 * (m + 1) + 1 by omega,
        show (m + 1) + 1 = m + 2 by omega] using
          natCard_weightedEvenOrthogonalGroup_eq_nonsplit_of_rootAffine_of_neg_nonsquare
            hchar hq m hroot' d hd hneg

/-! ### Nonsquare `-1`: odd half-rank -/

/-- If `-1` is nonsquare, an odd half-rank and square `-d` give the split
weighted even order. -/
theorem natCard_evenWeightedIdentityOrthogonalGroup_eq_split_of_neg_one_nonsquare_of_odd
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hminus : ∀ x : K, x ^ 2 ≠ -1)
    (s : ℕ) (hs : Odd s) (d : K) (hd : d ≠ 0)
    (t : K) (ht : t ^ 2 = -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨r, rfl⟩ := hs
  cases r with
  | zero =>
      simpa using
        natCard_rankTwoWeightedIdentityOrthogonalGroup_eq_splitExpression
          hchar d hd t ht
  | succ m =>
      have heven :=
        (evenIdentityShellCardinality_pair_of_neg_one_nonsquare
          hchar hq hminus m).2
      have hroot :=
        rootAffineShellCardinality_finSuccGramBlock_of_evenIdentitySplit
          (1 : Matrix (Fin (2 * (2 * m + 2)))
            (Fin (2 * (2 * m + 2))) K) (2 * m + 1) hq heven
      have hroot' : RootAffineShellCardinality
          (1 : Matrix (Fin (2 * (2 * m + 1 + 1) + 1))
            (Fin (2 * (2 * m + 1 + 1) + 1)) K) 1
          (oddIdentityAffineBase (Nat.card K) (2 * m + 1))
          (oddIdentityShellCorrection (Nat.card K) (2 * m + 1)) := by
        simpa only [finSuccGramBlock_one,
          show 2 * (2 * m + 2) = 2 * (2 * m + 1 + 1) by omega] using hroot
      simpa only [Nat.succ_eq_add_one,
        show 2 * ((m + 1) + (m + 1) + 1) - 1 =
          2 * (2 * m + 1 + 1) + 1 by omega,
        show (m + 1) + (m + 1) + 1 = (2 * m + 1) + 2 by omega] using
          natCard_weightedEvenOrthogonalGroup_eq_split_of_rootAffine_of_neg_square
            hchar hq (2 * m + 1) hroot' d hd t ht

/-- If `-1` is nonsquare, an odd half-rank and nonsquare `-d` give the
nonsplit weighted even order. -/
theorem natCard_evenWeightedIdentityOrthogonalGroup_eq_nonsplit_of_neg_one_nonsquare_of_odd
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hminus : ∀ x : K, x ^ 2 ≠ -1)
    (s : ℕ) (hs : Odd s) (d : K) (hd : d ≠ 0)
    (hneg : ∀ x : K, x ^ 2 ≠ -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨r, rfl⟩ := hs
  cases r with
  | zero =>
      simpa using
        natCard_rankTwoWeightedIdentityOrthogonalGroup_eq_nonsplitExpression
          hchar d hneg
  | succ m =>
      have heven :=
        (evenIdentityShellCardinality_pair_of_neg_one_nonsquare
          hchar hq hminus m).2
      have hroot :=
        rootAffineShellCardinality_finSuccGramBlock_of_evenIdentitySplit
          (1 : Matrix (Fin (2 * (2 * m + 2)))
            (Fin (2 * (2 * m + 2))) K) (2 * m + 1) hq heven
      have hroot' : RootAffineShellCardinality
          (1 : Matrix (Fin (2 * (2 * m + 1 + 1) + 1))
            (Fin (2 * (2 * m + 1 + 1) + 1)) K) 1
          (oddIdentityAffineBase (Nat.card K) (2 * m + 1))
          (oddIdentityShellCorrection (Nat.card K) (2 * m + 1)) := by
        simpa only [finSuccGramBlock_one,
          show 2 * (2 * m + 2) = 2 * (2 * m + 1 + 1) by omega] using hroot
      simpa only [Nat.succ_eq_add_one,
        show 2 * ((m + 1) + (m + 1) + 1) - 1 =
          2 * (2 * m + 1 + 1) + 1 by omega,
        show (m + 1) + (m + 1) + 1 = (2 * m + 1) + 2 by omega] using
          natCard_weightedEvenOrthogonalGroup_eq_nonsplit_of_rootAffine_of_neg_nonsquare
            hchar hq (2 * m + 1) hroot' d hd hneg

/-! ### Nonsquare `-1`: even half-rank -/

/-- If `-1` is nonsquare, a positive even half-rank and square `-d` give the
nonsplit weighted even order. -/
theorem natCard_evenWeightedIdentityOrthogonalGroup_eq_nonsplit_of_neg_one_nonsquare_of_even
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hminus : ∀ x : K, x ^ 2 ≠ -1)
    (s : ℕ) (hspos : 0 < s) (hs : Even s)
    (d : K) (hd : d ≠ 0) (t : K) (ht : t ^ 2 = -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨r, rfl⟩ := hs
  have hrpos : 0 < r := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.mpr hrpos
  have heven :=
    (evenIdentityShellCardinality_pair_of_neg_one_nonsquare
      hchar hq hminus m).1
  have hroot :=
    rootCoaffineShellCardinality_finSuccGramBlock_of_evenIdentityNonsplit
      (1 : Matrix (Fin (2 * (2 * m + 1)))
        (Fin (2 * (2 * m + 1))) K) (2 * m) hq heven
  have hroot' : RootCoaffineShellCardinality
      (1 : Matrix (Fin (2 * (2 * m + 1) + 1))
        (Fin (2 * (2 * m + 1) + 1)) K) 1
      (oddIdentityCoaffineBase (Nat.card K) (2 * m))
      (oddIdentityShellCorrection (Nat.card K) (2 * m)) := by
    simpa only [finSuccGramBlock_one] using hroot
  have hdim : 2 * ((m + 1) + (m + 1)) - 1 =
      2 * (2 * m + 1) + 1 := by omega
  rw [hdim]
  simpa only [show (m + 1) + (m + 1) = 2 * m + 2 by omega] using
    natCard_weightedEvenOrthogonalGroup_eq_nonsplit_of_rootCoaffine_of_neg_square
      hchar hq (2 * m) hroot' d hd t ht

/-- If `-1` is nonsquare, a positive even half-rank and nonsquare `-d` give
the split weighted even order. -/
theorem natCard_evenWeightedIdentityOrthogonalGroup_eq_split_of_neg_one_nonsquare_of_even
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hminus : ∀ x : K, x ^ 2 ≠ -1)
    (s : ℕ) (hspos : 0 < s) (hs : Even s)
    (d : K) (hd : d ≠ 0) (hneg : ∀ x : K, x ^ 2 ≠ -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨r, rfl⟩ := hs
  have hrpos : 0 < r := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.mpr hrpos
  have heven :=
    (evenIdentityShellCardinality_pair_of_neg_one_nonsquare
      hchar hq hminus m).1
  have hroot :=
    rootCoaffineShellCardinality_finSuccGramBlock_of_evenIdentityNonsplit
      (1 : Matrix (Fin (2 * (2 * m + 1)))
        (Fin (2 * (2 * m + 1))) K) (2 * m) hq heven
  have hroot' : RootCoaffineShellCardinality
      (1 : Matrix (Fin (2 * (2 * m + 1) + 1))
        (Fin (2 * (2 * m + 1) + 1)) K) 1
      (oddIdentityCoaffineBase (Nat.card K) (2 * m))
      (oddIdentityShellCorrection (Nat.card K) (2 * m)) := by
    simpa only [finSuccGramBlock_one] using hroot
  have hdim : 2 * ((m + 1) + (m + 1)) - 1 =
      2 * (2 * m + 1) + 1 := by omega
  rw [hdim]
  simpa only [show (m + 1) + (m + 1) = 2 * m + 2 by omega] using
    natCard_weightedEvenOrthogonalGroup_eq_split_of_rootCoaffine_of_neg_nonsquare
      hchar hq (2 * m) hroot' d hd hneg

end PositiveDefiniteIntegralLattice
