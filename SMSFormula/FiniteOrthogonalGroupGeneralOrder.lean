import SMSFormula.FiniteOrthogonalGroupWeightedIdentityOrderEven
import SMSFormula.FiniteOrthogonalGroupStandardModelTransport

/-!
# Finite orthogonal-group orders for arbitrary nonsingular forms

The finite-field classification transports every positive-rank
nonsingular symmetric Gram matrix to a head-weighted identity model.  This
module evaluates the transported model.  In even dimension the model
coefficient differs from the original determinant by an explicit nonzero
square, so square and nonsquare witnesses for the negative determinant are
transported before the weighted order theorem is applied.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-! ### Transporting the negative determinant square class -/

/-- Multiplication by an explicit nonzero square preserves whether the
negative of a field element is a square. -/
theorem exists_sq_eq_neg_iff_of_eq_sq_mul
    {K : Type*} [Field K] (c d a : K) (ha : a ≠ 0)
    (hd : d = a ^ 2 * c) :
    (∃ t : K, t ^ 2 = -d) ↔ ∃ t : K, t ^ 2 = -c := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t / a, ?_⟩
    rw [div_pow, ht, hd]
    field_simp [ha]
  · rintro ⟨t, ht⟩
    refine ⟨a * t, ?_⟩
    rw [mul_pow, ht, hd]
    ring

/-- Multiplication by an explicit nonzero square also preserves literal
nonsquareness of the negative field element. -/
theorem forall_sq_ne_neg_iff_of_eq_sq_mul
    {K : Type*} [Field K] (c d a : K) (ha : a ≠ 0)
    (hd : d = a ^ 2 * c) :
    (∀ t : K, t ^ 2 ≠ -d) ↔ ∀ t : K, t ^ 2 ≠ -c := by
  simpa only [not_exists] using
    not_congr (exists_sq_eq_neg_iff_of_eq_sq_mul c d a ha hd)

/-! ### Odd-dimensional forms -/

/-- Every nonsingular symmetric form of positive odd dimension has the
standard odd orthogonal-group order. -/
theorem natCard_oddFiniteGramOrthogonalGroup_eq_closedExpression
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (s : ℕ) (hs : 0 < s)
    (A : Matrix (Fin (2 * s + 1)) (Fin (2 * s + 1)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0) :
    Nat.card (finiteGramOrthogonalGroup A) =
      oddIdentityOrthogonalOrderExpression (Nat.card K) s := by
  obtain ⟨d, a, R, hd, ha, hda, hR, hcard⟩ :=
    exists_natCard_finiteGramOrthogonalGroup_eq_finSuccIdentity_with_det_square
      (2 * s) hchar A hA_symm hA_det
  calc
    Nat.card (finiteGramOrthogonalGroup A) =
        Nat.card (finiteGramOrthogonalGroup
          (finSuccIdentityGramMatrix (n := 2 * s) d)) := hcard
    _ = oddIdentityOrthogonalOrderExpression (Nat.card K) s :=
      natCard_oddWeightedIdentityOrthogonalGroup_eq_closedExpression
        hchar hq s hs d hd

/-! ### Even-dimensional forms: square `-1` -/

/-- If `-1` and the negative determinant are square, every positive even
form has the split order. -/
theorem natCard_evenFiniteGramOrthogonalGroup_eq_split_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (u : K) (hu : u ^ 2 = -1)
    (s : ℕ) (hs : 0 < s)
    (A : Matrix (Fin (2 * s)) (Fin (2 * s)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (t : K) (ht : t ^ 2 = -A.det) :
    Nat.card (finiteGramOrthogonalGroup A) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  have hdim : 2 * s = (2 * s - 1) + 1 := by omega
  generalize hN : 2 * s = N at A hA_symm hA_det ht ⊢
  have hN_eq : N = (2 * s - 1) + 1 := hN.symm.trans hdim
  clear hN
  subst N
  obtain ⟨d, a, R, hd, ha, hda, hR, hcard⟩ :=
    exists_natCard_finiteGramOrthogonalGroup_eq_finSuccIdentity_with_det_square
      (2 * s - 1) hchar A hA_symm hA_det
  obtain ⟨td, htd⟩ :=
    (exists_sq_eq_neg_iff_of_eq_sq_mul A.det d a ha hda).2 ⟨t, ht⟩
  calc
    Nat.card (finiteGramOrthogonalGroup A) =
        Nat.card (finiteGramOrthogonalGroup
          (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) := hcard
    _ = splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s :=
      natCard_evenWeightedIdentityOrthogonalGroup_eq_split_of_neg_one_square
        hchar hq u hu s hs d hd td htd

/-- If `-1` is square and the negative determinant is nonsquare, every
positive even form has the nonsplit order. -/
theorem natCard_evenFiniteGramOrthogonalGroup_eq_nonsplit_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (u : K) (hu : u ^ 2 = -1)
    (s : ℕ) (hs : 0 < s)
    (A : Matrix (Fin (2 * s)) (Fin (2 * s)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hneg : ∀ t : K, t ^ 2 ≠ -A.det) :
    Nat.card (finiteGramOrthogonalGroup A) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  have hdim : 2 * s = (2 * s - 1) + 1 := by omega
  generalize hN : 2 * s = N at A hA_symm hA_det hneg ⊢
  have hN_eq : N = (2 * s - 1) + 1 := hN.symm.trans hdim
  clear hN
  subst N
  obtain ⟨d, a, R, hd, ha, hda, hR, hcard⟩ :=
    exists_natCard_finiteGramOrthogonalGroup_eq_finSuccIdentity_with_det_square
      (2 * s - 1) hchar A hA_symm hA_det
  have hnegd : ∀ t : K, t ^ 2 ≠ -d :=
    (forall_sq_ne_neg_iff_of_eq_sq_mul A.det d a ha hda).2 hneg
  calc
    Nat.card (finiteGramOrthogonalGroup A) =
        Nat.card (finiteGramOrthogonalGroup
          (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) := hcard
    _ = nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) s :=
      natCard_evenWeightedIdentityOrthogonalGroup_eq_nonsplit_of_neg_one_square
        hchar hq u hu s hs d hd hnegd

/-! ### Even-dimensional forms: nonsquare `-1`, odd half-rank -/

/-- If `-1` is nonsquare, an odd half-rank and square negative determinant
give the split order. -/
theorem natCard_evenFiniteGramOrthogonalGroup_eq_split_of_neg_one_nonsquare_of_odd
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hminus : ∀ x : K, x ^ 2 ≠ -1)
    (s : ℕ) (hs : Odd s)
    (A : Matrix (Fin (2 * s)) (Fin (2 * s)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (t : K) (ht : t ^ 2 = -A.det) :
    Nat.card (finiteGramOrthogonalGroup A) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  have hspos : 0 < s := Odd.pos hs
  have hdim : 2 * s = (2 * s - 1) + 1 := by omega
  generalize hN : 2 * s = N at A hA_symm hA_det ht ⊢
  have hN_eq : N = (2 * s - 1) + 1 := hN.symm.trans hdim
  clear hN
  subst N
  obtain ⟨d, a, R, hd, ha, hda, hR, hcard⟩ :=
    exists_natCard_finiteGramOrthogonalGroup_eq_finSuccIdentity_with_det_square
      (2 * s - 1) hchar A hA_symm hA_det
  obtain ⟨td, htd⟩ :=
    (exists_sq_eq_neg_iff_of_eq_sq_mul A.det d a ha hda).2 ⟨t, ht⟩
  calc
    Nat.card (finiteGramOrthogonalGroup A) =
        Nat.card (finiteGramOrthogonalGroup
          (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) := hcard
    _ = splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s :=
      natCard_evenWeightedIdentityOrthogonalGroup_eq_split_of_neg_one_nonsquare_of_odd
        hchar hq hminus s hs d hd td htd

/-- If `-1` and the negative determinant are nonsquare and the half-rank is
odd, the order is nonsplit. -/
theorem natCard_evenFiniteGramOrthogonalGroup_eq_nonsplit_of_neg_one_nonsquare_of_odd
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hminus : ∀ x : K, x ^ 2 ≠ -1)
    (s : ℕ) (hs : Odd s)
    (A : Matrix (Fin (2 * s)) (Fin (2 * s)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hneg : ∀ t : K, t ^ 2 ≠ -A.det) :
    Nat.card (finiteGramOrthogonalGroup A) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  have hspos : 0 < s := Odd.pos hs
  have hdim : 2 * s = (2 * s - 1) + 1 := by omega
  generalize hN : 2 * s = N at A hA_symm hA_det hneg ⊢
  have hN_eq : N = (2 * s - 1) + 1 := hN.symm.trans hdim
  clear hN
  subst N
  obtain ⟨d, a, R, hd, ha, hda, hR, hcard⟩ :=
    exists_natCard_finiteGramOrthogonalGroup_eq_finSuccIdentity_with_det_square
      (2 * s - 1) hchar A hA_symm hA_det
  have hnegd : ∀ t : K, t ^ 2 ≠ -d :=
    (forall_sq_ne_neg_iff_of_eq_sq_mul A.det d a ha hda).2 hneg
  calc
    Nat.card (finiteGramOrthogonalGroup A) =
        Nat.card (finiteGramOrthogonalGroup
          (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) := hcard
    _ = nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) s :=
      natCard_evenWeightedIdentityOrthogonalGroup_eq_nonsplit_of_neg_one_nonsquare_of_odd
        hchar hq hminus s hs d hd hnegd

/-! ### Even-dimensional forms: nonsquare `-1`, even half-rank -/

/-- If `-1` is nonsquare, a positive even half-rank and square negative
determinant give the nonsplit order. -/
theorem natCard_evenFiniteGramOrthogonalGroup_eq_nonsplit_of_neg_one_nonsquare_of_even
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hminus : ∀ x : K, x ^ 2 ≠ -1)
    (s : ℕ) (hspos : 0 < s) (hs : Even s)
    (A : Matrix (Fin (2 * s)) (Fin (2 * s)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (t : K) (ht : t ^ 2 = -A.det) :
    Nat.card (finiteGramOrthogonalGroup A) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  have hdim : 2 * s = (2 * s - 1) + 1 := by omega
  generalize hN : 2 * s = N at A hA_symm hA_det ht ⊢
  have hN_eq : N = (2 * s - 1) + 1 := hN.symm.trans hdim
  clear hN
  subst N
  obtain ⟨d, a, R, hd, ha, hda, hR, hcard⟩ :=
    exists_natCard_finiteGramOrthogonalGroup_eq_finSuccIdentity_with_det_square
      (2 * s - 1) hchar A hA_symm hA_det
  obtain ⟨td, htd⟩ :=
    (exists_sq_eq_neg_iff_of_eq_sq_mul A.det d a ha hda).2 ⟨t, ht⟩
  calc
    Nat.card (finiteGramOrthogonalGroup A) =
        Nat.card (finiteGramOrthogonalGroup
          (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) := hcard
    _ = nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) s :=
      natCard_evenWeightedIdentityOrthogonalGroup_eq_nonsplit_of_neg_one_nonsquare_of_even
        hchar hq hminus s hspos hs d hd td htd

/-- If `-1` is nonsquare, a positive even half-rank and nonsquare negative
determinant give the split order. -/
theorem natCard_evenFiniteGramOrthogonalGroup_eq_split_of_neg_one_nonsquare_of_even
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hminus : ∀ x : K, x ^ 2 ≠ -1)
    (s : ℕ) (hspos : 0 < s) (hs : Even s)
    (A : Matrix (Fin (2 * s)) (Fin (2 * s)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hneg : ∀ t : K, t ^ 2 ≠ -A.det) :
    Nat.card (finiteGramOrthogonalGroup A) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s := by
  have hdim : 2 * s = (2 * s - 1) + 1 := by omega
  generalize hN : 2 * s = N at A hA_symm hA_det hneg ⊢
  have hN_eq : N = (2 * s - 1) + 1 := hN.symm.trans hdim
  clear hN
  subst N
  obtain ⟨d, a, R, hd, ha, hda, hR, hcard⟩ :=
    exists_natCard_finiteGramOrthogonalGroup_eq_finSuccIdentity_with_det_square
      (2 * s - 1) hchar A hA_symm hA_det
  have hnegd : ∀ t : K, t ^ 2 ≠ -d :=
    (forall_sq_ne_neg_iff_of_eq_sq_mul A.det d a ha hda).2 hneg
  calc
    Nat.card (finiteGramOrthogonalGroup A) =
        Nat.card (finiteGramOrthogonalGroup
          (finSuccIdentityGramMatrix (n := 2 * s - 1) d)) := hcard
    _ = splitEvenIdentityOrthogonalOrderExpression (Nat.card K) s :=
      natCard_evenWeightedIdentityOrthogonalGroup_eq_split_of_neg_one_nonsquare_of_even
        hchar hq hminus s hspos hs d hd hnegd

end PositiveDefiniteIntegralLattice
