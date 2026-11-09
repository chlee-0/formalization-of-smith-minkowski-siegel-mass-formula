import SMSFormula.FiniteOrthogonalGroupIdentityOrderRecurrence

/-!
# Square-class shell sums in arbitrary dimension

Odd-dimensional quadratic-shell cardinalities in the existing fixed-rank
proofs have the uniform shape

`base + correction * (# square roots of εc)`.

This module packages that shape independently of the dimension.  Splitting
off one coordinate turns the total square-root correction into one weighted
binary quadratic fiber, so the next shell cardinality is reduced to the
already completed binary finite-field count.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A quadratic shell family whose three square classes are encoded by the
number of square roots of `εc`.  At zero this root count is one, at a nonzero
square it is two, and at a nonsquare it is zero. -/
def RootAffineShellCardinality
    {K : Type*} [Field K] [Finite K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ) : Prop :=
  ∀ c : K,
    Nat.card (finiteGramNormVectors B c) =
      base + correction * Nat.card (squareRootFiber K (ε * c))

lemma RootAffineShellCardinality.zero
    {K : Type*} [Field K] [Finite K]
    {B : Matrix (Fin n) (Fin n) K} {ε : K} {base correction : ℕ}
    (h : RootAffineShellCardinality B ε base correction) :
    Nat.card (finiteGramNormVectors B 0) = base + correction := by
  rw [h 0, mul_zero, natCard_squareRootFiber_zero, Nat.mul_one]

lemma RootAffineShellCardinality.of_sq
    {K : Type*} [Field K] [Finite K]
    {B : Matrix (Fin n) (Fin n) K} {ε : K} {base correction : ℕ}
    (hchar : ringChar K ≠ 2)
    (h : RootAffineShellCardinality B ε base correction)
    (c : K) (hc : ε * c ≠ 0) (t : K) (ht : t ^ 2 = ε * c) :
    Nat.card (finiteGramNormVectors B c) = base + 2 * correction := by
  rw [h c, natCard_squareRootFiber_of_sq hchar (ε * c) hc t ht]
  omega

lemma RootAffineShellCardinality.of_nonsquare
    {K : Type*} [Field K] [Finite K]
    {B : Matrix (Fin n) (Fin n) K} {ε : K} {base correction : ℕ}
    (h : RootAffineShellCardinality B ε base correction)
    (c : K) (hc : ∀ t : K, t ^ 2 ≠ ε * c) :
    Nat.card (finiteGramNormVectors B c) = base := by
  rw [h c, natCard_squareRootFiber_of_nonsquare (ε * c) hc,
    Nat.mul_zero, Nat.add_zero]

/-- The family of square roots of `ε(c-x²)` is exactly the weighted binary
fiber `εx²+y²=εc`. -/
noncomputable def sigmaSquareRootFiberMulSubSqEquivWeightedBinary
    {K : Type*} [Field K] (ε c : K) :
    (Σ x : K, squareRootFiber K (ε * (c - x ^ 2))) ≃
      weightedBinarySumSquaresFiber K ε (ε * c) where
  toFun z := ⟨(z.1, z.2.1), by linear_combination z.2.2⟩
  invFun z := ⟨z.1.1, ⟨z.1.2, by linear_combination z.2⟩⟩
  left_inv z := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      rfl
  right_inv z := Subtype.ext rfl

/-- Summing any root-affine shell family over `c-x²` replaces the total root
correction by the cardinality of one weighted binary fiber.  This is the
dimension-independent square-class recurrence, stated without division or
cancellation. -/
theorem sum_natCard_finiteGramNormVectors_sub_sq_of_rootAffine
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction) (c : K) :
    ∑ x : K, Nat.card (finiteGramNormVectors B (c - x ^ 2)) =
      Nat.card K * base + correction *
        Nat.card (weightedBinarySumSquaresFiber K ε (ε * c)) := by
  classical
  letI (x : K) : Finite (squareRootFiber K (ε * (c - x ^ 2))) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hconst : (∑ _x : K, base) = Nat.card K * base := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    simp
  have hroots :
      (∑ x : K, correction *
          Nat.card (squareRootFiber K (ε * (c - x ^ 2)))) =
        correction * ∑ x : K,
          Nat.card (squareRootFiber K (ε * (c - x ^ 2))) := by
    rw [Finset.mul_sum]
  calc
    ∑ x : K, Nat.card (finiteGramNormVectors B (c - x ^ 2)) =
        ∑ x : K, (base + correction *
          Nat.card (squareRootFiber K (ε * (c - x ^ 2)))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact h (c - x ^ 2)
    _ = Nat.card K * base + correction * ∑ x : K,
          Nat.card (squareRootFiber K (ε * (c - x ^ 2))) := by
      rw [Finset.sum_add_distrib, hconst, hroots]
    _ = Nat.card K * base + correction *
        Nat.card (weightedBinarySumSquaresFiber K ε (ε * c)) := by
      rw [← Nat.card_sigma,
        Nat.card_congr
          (sigmaSquareRootFiberMulSubSqEquivWeightedBinary ε c)]

/-- The leading-coordinate shell recurrence with a root-affine tail already
substituted. -/
theorem natCard_finSuccGramBlock_fixedNorm_of_rootAffine
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction) (c : K) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) c) =
      Nat.card K * base + correction *
        Nat.card (weightedBinarySumSquaresFiber K ε (ε * c)) := by
  rw [natCard_finiteGramNormVectors_finSucc_eq_sum]
  simpa using
    sum_natCard_finiteGramNormVectors_sub_sq_of_rootAffine
      B ε base correction h c

/-- Nonsplit weighted-binary specialization at zero. -/
theorem natCard_finSuccGramBlock_zero_of_rootAffine_of_neg_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction)
    (hneg : ∀ r : K, r ^ 2 ≠ -ε) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) 0) =
      Nat.card K * base + correction := by
  rw [natCard_finSuccGramBlock_fixedNorm_of_rootAffine B ε base correction h 0,
    mul_zero,
    natCard_weightedBinarySumSquaresFiber_zero_of_neg_d_nonsquare ε hneg,
    Nat.mul_one]

/-- Nonsplit weighted-binary specialization at every nonzero target. -/
theorem natCard_finSuccGramBlock_ne_zero_of_rootAffine_of_neg_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (hneg : ∀ r : K, r ^ 2 ≠ -ε)
    (c : K) (hc : c ≠ 0) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) c) =
      Nat.card K * base + correction * (Nat.card K + 1) := by
  rw [natCard_finSuccGramBlock_fixedNorm_of_rootAffine B ε base correction h c,
    natCard_weightedBinarySumSquaresFiber_of_neg_d_nonsquare_ne_zero
      ε hneg (ε * c) (mul_ne_zero hε hc)]

/-- Split weighted-binary specialization at zero. -/
theorem natCard_finSuccGramBlock_zero_of_rootAffine_of_neg_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (t : K) (ht : t ^ 2 = -ε) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) 0) =
      Nat.card K * base + correction * (2 * Nat.card K - 1) := by
  rw [natCard_finSuccGramBlock_fixedNorm_of_rootAffine B ε base correction h 0,
    mul_zero,
    natCard_weightedBinarySumSquaresFiber_zero_of_neg_d_square
      hchar ε hε t ht]

/-- Split weighted-binary specialization at every nonzero target. -/
theorem natCard_finSuccGramBlock_ne_zero_of_rootAffine_of_neg_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (t : K) (ht : t ^ 2 = -ε)
    (c : K) (hc : c ≠ 0) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) c) =
      Nat.card K * base + correction * (Nat.card K - 1) := by
  rw [natCard_finSuccGramBlock_fixedNorm_of_rootAffine B ε base correction h c,
    natCard_weightedBinarySumSquaresFiber_of_neg_d_square_ne_zero
      hchar ε hε t ht (ε * c) (mul_ne_zero hε hc)]

/-! ### The complementary root-affine orientation -/

/-- The subtraction-free complementary orientation of a square-class shell
family.  It records `shell(c) + correction * roots(εc) = base`, so no
truncated natural subtraction is introduced when the square shells are the
smaller ones. -/
def RootCoaffineShellCardinality
    {K : Type*} [Field K] [Finite K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ) : Prop :=
  ∀ c : K,
    Nat.card (finiteGramNormVectors B c) +
      correction * Nat.card (squareRootFiber K (ε * c)) = base

lemma RootCoaffineShellCardinality.zero
    {K : Type*} [Field K] [Finite K]
    {B : Matrix (Fin n) (Fin n) K} {ε : K} {base correction : ℕ}
    (h : RootCoaffineShellCardinality B ε base correction) :
    Nat.card (finiteGramNormVectors B 0) + correction = base := by
  have h0 := h 0
  rw [mul_zero, natCard_squareRootFiber_zero, Nat.mul_one] at h0
  exact h0

lemma RootCoaffineShellCardinality.of_sq
    {K : Type*} [Field K] [Finite K]
    {B : Matrix (Fin n) (Fin n) K} {ε : K} {base correction : ℕ}
    (hchar : ringChar K ≠ 2)
    (h : RootCoaffineShellCardinality B ε base correction)
    (c : K) (hc : ε * c ≠ 0) (t : K) (ht : t ^ 2 = ε * c) :
    Nat.card (finiteGramNormVectors B c) + 2 * correction = base := by
  have hs := h c
  rw [natCard_squareRootFiber_of_sq hchar (ε * c) hc t ht] at hs
  omega

lemma RootCoaffineShellCardinality.of_nonsquare
    {K : Type*} [Field K] [Finite K]
    {B : Matrix (Fin n) (Fin n) K} {ε : K} {base correction : ℕ}
    (h : RootCoaffineShellCardinality B ε base correction)
    (c : K) (hc : ∀ t : K, t ^ 2 ≠ ε * c) :
    Nat.card (finiteGramNormVectors B c) = base := by
  simpa [natCard_squareRootFiber_of_nonsquare (ε * c) hc] using h c

/-- Complementary square-class sum.  The complete correction remains on the
left, giving a literal natural-number equality with no division, cancellation,
or subtraction. -/
theorem sum_natCard_finiteGramNormVectors_sub_sq_of_rootCoaffine
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction) (c : K) :
    (∑ x : K, Nat.card (finiteGramNormVectors B (c - x ^ 2))) +
        correction *
          Nat.card (weightedBinarySumSquaresFiber K ε (ε * c)) =
      Nat.card K * base := by
  classical
  letI (x : K) : Finite (squareRootFiber K (ε * (c - x ^ 2))) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hpoint :
      (∑ x : K, (Nat.card (finiteGramNormVectors B (c - x ^ 2)) +
          correction *
            Nat.card (squareRootFiber K (ε * (c - x ^ 2))))) =
        ∑ _x : K, base := by
    apply Finset.sum_congr rfl
    intro x _
    exact h (c - x ^ 2)
  have hconst : (∑ _x : K, base) = Nat.card K * base := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    simp
  have hroots :
      (∑ x : K, correction *
          Nat.card (squareRootFiber K (ε * (c - x ^ 2)))) =
        correction * ∑ x : K,
          Nat.card (squareRootFiber K (ε * (c - x ^ 2))) := by
    rw [Finset.mul_sum]
  rw [Finset.sum_add_distrib, hroots, hconst] at hpoint
  simpa [← Nat.card_sigma,
    Nat.card_congr (sigmaSquareRootFiberMulSubSqEquivWeightedBinary ε c)]
    using hpoint

/-- Leading-coordinate recurrence for the complementary square-class
orientation. -/
theorem natCard_finSuccGramBlock_fixedNorm_add_of_rootCoaffine
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction) (c : K) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) c) +
      correction *
          Nat.card (weightedBinarySumSquaresFiber K ε (ε * c)) =
      Nat.card K * base := by
  rw [natCard_finiteGramNormVectors_finSucc_eq_sum]
  simpa using
    sum_natCard_finiteGramNormVectors_sub_sq_of_rootCoaffine
      B ε base correction h c

theorem natCard_finSuccGramBlock_zero_add_of_rootCoaffine_of_neg_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction)
    (hneg : ∀ r : K, r ^ 2 ≠ -ε) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) 0) +
      correction = Nat.card K * base := by
  have hmain := natCard_finSuccGramBlock_fixedNorm_add_of_rootCoaffine
    B ε base correction h 0
  rw [mul_zero,
    natCard_weightedBinarySumSquaresFiber_zero_of_neg_d_nonsquare ε hneg,
    Nat.mul_one] at hmain
  exact hmain

theorem natCard_finSuccGramBlock_ne_zero_add_of_rootCoaffine_of_neg_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (hneg : ∀ r : K, r ^ 2 ≠ -ε)
    (c : K) (hc : c ≠ 0) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) c) +
      correction * (Nat.card K + 1) = Nat.card K * base := by
  have hmain := natCard_finSuccGramBlock_fixedNorm_add_of_rootCoaffine
    B ε base correction h c
  rw [natCard_weightedBinarySumSquaresFiber_of_neg_d_nonsquare_ne_zero
    ε hneg (ε * c) (mul_ne_zero hε hc)] at hmain
  exact hmain

theorem natCard_finSuccGramBlock_zero_add_of_rootCoaffine_of_neg_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (t : K) (ht : t ^ 2 = -ε) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) 0) +
      correction * (2 * Nat.card K - 1) = Nat.card K * base := by
  have hmain := natCard_finSuccGramBlock_fixedNorm_add_of_rootCoaffine
    B ε base correction h 0
  rw [mul_zero,
    natCard_weightedBinarySumSquaresFiber_zero_of_neg_d_square
      hchar ε hε t ht] at hmain
  exact hmain

theorem natCard_finSuccGramBlock_ne_zero_add_of_rootCoaffine_of_neg_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (t : K) (ht : t ^ 2 = -ε)
    (c : K) (hc : c ≠ 0) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) c) +
      correction * (Nat.card K - 1) = Nat.card K * base := by
  have hmain := natCard_finSuccGramBlock_fixedNorm_add_of_rootCoaffine
    B ε base correction h c
  rw [natCard_weightedBinarySumSquaresFiber_of_neg_d_square_ne_zero
    hchar ε hε t ht (ε * c) (mul_ne_zero hε hc)] at hmain
  exact hmain

end PositiveDefiniteIntegralLattice
