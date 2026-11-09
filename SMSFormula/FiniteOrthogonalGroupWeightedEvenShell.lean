import SMSFormula.FiniteOrthogonalGroupWeightedIdentityOrderOdd

/-!
# Weighted even-dimensional shell multipliers

Splitting the distinguished norm-`d` shell of `diag(d,B)` leaves the residual
target `d-d*x^2`.  For a root-affine or root-coaffine odd-dimensional tail,
the complete root correction is the weighted binary fiber with coefficient
`ε*d` and target `ε*d`.  This module constructs that equivalence literally and
records the square/nonsquare shell multipliers without natural subtraction or
cancellation.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The square-root correction over the scaled residual targets `d-d*x²` is
literally the weighted binary fiber `(εd)x²+y²=εd`. -/
noncomputable def sigmaSquareRootFiberMulSubMulSqEquivWeightedBinary
    {K : Type*} [Field K] (ε d : K) :
    (Σ x : K, squareRootFiber K (ε * (d - d * x ^ 2))) ≃
      weightedBinarySumSquaresFiber K (ε * d) (ε * d) where
  toFun z := ⟨(z.1, z.2.1), by
    have hz := z.2.2
    linear_combination hz⟩
  invFun z := ⟨z.1.1, ⟨z.1.2, by
    have hz := z.2
    linear_combination hz⟩⟩
  left_inv z := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      rfl
  right_inv z := Subtype.ext rfl

/-- Scaled leading-coordinate sum for a root-affine tail. -/
theorem sum_natCard_finiteGramNormVectors_sub_mul_sq_of_rootAffine
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction) (d : K) :
    ∑ x : K, Nat.card (finiteGramNormVectors B (d - d * x ^ 2)) =
      Nat.card K * base + correction *
        Nat.card (weightedBinarySumSquaresFiber K (ε * d) (ε * d)) := by
  classical
  letI (x : K) : Finite (squareRootFiber K (ε * (d - d * x ^ 2))) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hconst : (∑ _x : K, base) = Nat.card K * base := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    simp
  have hroots :
      (∑ x : K, correction *
          Nat.card (squareRootFiber K (ε * (d - d * x ^ 2)))) =
        correction * ∑ x : K,
          Nat.card (squareRootFiber K (ε * (d - d * x ^ 2))) := by
    rw [Finset.mul_sum]
  calc
    ∑ x : K, Nat.card (finiteGramNormVectors B (d - d * x ^ 2)) =
        ∑ x : K, (base + correction *
          Nat.card (squareRootFiber K (ε * (d - d * x ^ 2)))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact h (d - d * x ^ 2)
    _ = Nat.card K * base + correction * ∑ x : K,
          Nat.card (squareRootFiber K (ε * (d - d * x ^ 2))) := by
      rw [Finset.sum_add_distrib, hconst, hroots]
    _ = Nat.card K * base + correction *
        Nat.card (weightedBinarySumSquaresFiber K (ε * d) (ε * d)) := by
      rw [← Nat.card_sigma,
        Nat.card_congr
          (sigmaSquareRootFiberMulSubMulSqEquivWeightedBinary ε d)]

/-- Nonsquare weighted-binary specialization of the distinguished shell for
a root-affine tail. -/
theorem natCard_finSuccGramBlock_self_of_rootAffine_of_neg_mul_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (d : K) (hd : d ≠ 0)
    (hneg : ∀ r : K, r ^ 2 ≠ -(ε * d)) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock d B) d) =
      Nat.card K * base + correction * (Nat.card K + 1) := by
  rw [natCard_finiteGramNormVectors_finSucc_eq_sum,
    sum_natCard_finiteGramNormVectors_sub_mul_sq_of_rootAffine
      B ε base correction h d,
    natCard_weightedBinarySumSquaresFiber_of_neg_d_nonsquare_ne_zero
      (ε * d) hneg (ε * d) (mul_ne_zero hε hd)]

/-- Square weighted-binary specialization of the distinguished shell for a
root-affine tail. -/
theorem natCard_finSuccGramBlock_self_of_rootAffine_of_neg_mul_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (d : K) (hd : d ≠ 0)
    (t : K) (ht : t ^ 2 = -(ε * d)) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock d B) d) =
      Nat.card K * base + correction * (Nat.card K - 1) := by
  rw [natCard_finiteGramNormVectors_finSucc_eq_sum,
    sum_natCard_finiteGramNormVectors_sub_mul_sq_of_rootAffine
      B ε base correction h d,
    natCard_weightedBinarySumSquaresFiber_of_neg_d_square_ne_zero
      hchar (ε * d) (mul_ne_zero hε hd) t ht
      (ε * d) (mul_ne_zero hε hd)]

/-- Scaled leading-coordinate sum for a root-coaffine tail, retaining the
complete correction on the left. -/
theorem sum_natCard_finiteGramNormVectors_sub_mul_sq_add_of_rootCoaffine
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction) (d : K) :
    (∑ x : K, Nat.card (finiteGramNormVectors B (d - d * x ^ 2))) +
        correction *
          Nat.card (weightedBinarySumSquaresFiber K (ε * d) (ε * d)) =
      Nat.card K * base := by
  classical
  letI (x : K) : Finite (squareRootFiber K (ε * (d - d * x ^ 2))) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hpoint :
      (∑ x : K, (Nat.card (finiteGramNormVectors B (d - d * x ^ 2)) +
          correction *
            Nat.card (squareRootFiber K (ε * (d - d * x ^ 2))))) =
        ∑ _x : K, base := by
    apply Finset.sum_congr rfl
    intro x _
    exact h (d - d * x ^ 2)
  have hconst : (∑ _x : K, base) = Nat.card K * base := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    simp
  have hroots :
      (∑ x : K, correction *
          Nat.card (squareRootFiber K (ε * (d - d * x ^ 2)))) =
        correction * ∑ x : K,
          Nat.card (squareRootFiber K (ε * (d - d * x ^ 2))) := by
    rw [Finset.mul_sum]
  rw [Finset.sum_add_distrib, hroots, hconst] at hpoint
  simpa [← Nat.card_sigma,
    Nat.card_congr
      (sigmaSquareRootFiberMulSubMulSqEquivWeightedBinary ε d)] using hpoint

/-- Nonsquare weighted-binary specialization for a root-coaffine tail. -/
theorem natCard_finSuccGramBlock_self_add_of_rootCoaffine_of_neg_mul_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (d : K) (hd : d ≠ 0)
    (hneg : ∀ r : K, r ^ 2 ≠ -(ε * d)) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock d B) d) +
        correction * (Nat.card K + 1) = Nat.card K * base := by
  rw [natCard_finiteGramNormVectors_finSucc_eq_sum]
  have hmain :=
    sum_natCard_finiteGramNormVectors_sub_mul_sq_add_of_rootCoaffine
      B ε base correction h d
  rw [natCard_weightedBinarySumSquaresFiber_of_neg_d_nonsquare_ne_zero
    (ε * d) hneg (ε * d) (mul_ne_zero hε hd)] at hmain
  exact hmain

/-- Square weighted-binary specialization for a root-coaffine tail. -/
theorem natCard_finSuccGramBlock_self_add_of_rootCoaffine_of_neg_mul_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (d : K) (hd : d ≠ 0)
    (t : K) (ht : t ^ 2 = -(ε * d)) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock d B) d) +
        correction * (Nat.card K - 1) = Nat.card K * base := by
  rw [natCard_finiteGramNormVectors_finSucc_eq_sum]
  have hmain :=
    sum_natCard_finiteGramNormVectors_sub_mul_sq_add_of_rootCoaffine
      B ε base correction h d
  rw [natCard_weightedBinarySumSquaresFiber_of_neg_d_square_ne_zero
    hchar (ε * d) (mul_ne_zero hε hd) t ht
    (ε * d) (mul_ne_zero hε hd)] at hmain
  exact hmain

/-! ### Standard odd identity tails -/

/-- A standard root-affine odd identity tail and square `-d` give the split
weighted even order. -/
theorem natCard_weightedEvenOrthogonalGroup_eq_split_of_rootAffine_of_neg_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K) (m : ℕ)
    (h : RootAffineShellCardinality
      (1 : Matrix (Fin (2 * (m + 1) + 1))
        (Fin (2 * (m + 1) + 1)) K) 1
      (oddIdentityAffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m))
    (d : K) (hd : d ≠ 0) (t : K) (ht : t ^ 2 = -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d)) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) (m + 2) := by
  have hshell :=
    natCard_finSuccGramBlock_self_of_rootAffine_of_neg_mul_square
      hchar
      (1 : Matrix (Fin (2 * (m + 1) + 1))
        (Fin (2 * (m + 1) + 1)) K)
      1 (oddIdentityAffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m)
      h one_ne_zero d hd t (by simpa using ht)
  rw [oddIdentityAffine_nextSplitNonzero hq] at hshell
  have hshell' :
      Nat.card (finiteGramNormVectors
          (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d) d) =
        evenIdentitySplitNonzero (Nat.card K) (m + 1) := by
    simpa only [finSuccIdentityGramMatrix] using hshell
  have hrec := natCard_finSuccIdentityFixedNorm_mul_identityOrthogonal_eq
    (n := 2 * (m + 1) + 1) hchar d hd
  have hodd := natCard_oddIdentityOrthogonalGroup_eq_closedExpression
    hchar hq (m + 1) (by omega)
  calc
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d)) =
        evenIdentitySplitNonzero (Nat.card K) (m + 1) *
          Nat.card (finiteGramOrthogonalGroup
            (1 : Matrix (Fin (2 * (m + 1) + 1))
              (Fin (2 * (m + 1) + 1)) K)) := by
        rw [← hrec, hshell']
    _ = evenIdentitySplitNonzero (Nat.card K) (m + 1) *
          oddIdentityOrthogonalOrderExpression (Nat.card K) (m + 1) := by
        rw [hodd]
    _ = splitEvenIdentityOrthogonalOrderExpression
          (Nat.card K) ((m + 1) + 1) :=
        oddToSplitEvenOrthogonalOrderExpression (Nat.card K) (m + 1)
    _ = splitEvenIdentityOrthogonalOrderExpression
          (Nat.card K) (m + 2) := by
        rw [show (m + 1) + 1 = m + 2 by omega]

/-- A standard root-affine odd identity tail and nonsquare `-d` give the
nonsplit weighted even order. -/
theorem natCard_weightedEvenOrthogonalGroup_eq_nonsplit_of_rootAffine_of_neg_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K) (m : ℕ)
    (h : RootAffineShellCardinality
      (1 : Matrix (Fin (2 * (m + 1) + 1))
        (Fin (2 * (m + 1) + 1)) K) 1
      (oddIdentityAffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m))
    (d : K) (hd : d ≠ 0) (hneg : ∀ r : K, r ^ 2 ≠ -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d)) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) (m + 2) := by
  have hshell :=
    natCard_finSuccGramBlock_self_of_rootAffine_of_neg_mul_nonsquare
      (1 : Matrix (Fin (2 * (m + 1) + 1))
        (Fin (2 * (m + 1) + 1)) K)
      1 (oddIdentityAffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m)
      h one_ne_zero d hd (by simpa using hneg)
  rw [oddIdentityAffine_nextNonsplitNonzero hq] at hshell
  have hshell' :
      Nat.card (finiteGramNormVectors
          (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d) d) =
        evenIdentityNonsplitNonzero (Nat.card K) (m + 1) := by
    simpa only [finSuccIdentityGramMatrix] using hshell
  have hrec := natCard_finSuccIdentityFixedNorm_mul_identityOrthogonal_eq
    (n := 2 * (m + 1) + 1) hchar d hd
  have hodd := natCard_oddIdentityOrthogonalGroup_eq_closedExpression
    hchar hq (m + 1) (by omega)
  calc
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d)) =
        evenIdentityNonsplitNonzero (Nat.card K) (m + 1) *
          Nat.card (finiteGramOrthogonalGroup
            (1 : Matrix (Fin (2 * (m + 1) + 1))
              (Fin (2 * (m + 1) + 1)) K)) := by
        rw [← hrec, hshell']
    _ = evenIdentityNonsplitNonzero (Nat.card K) (m + 1) *
          oddIdentityOrthogonalOrderExpression (Nat.card K) (m + 1) := by
        rw [hodd]
    _ = nonsplitEvenIdentityOrthogonalOrderExpression
          (Nat.card K) ((m + 1) + 1) :=
        oddToNonsplitEvenOrthogonalOrderExpression (Nat.card K) (m + 1)
    _ = nonsplitEvenIdentityOrthogonalOrderExpression
          (Nat.card K) (m + 2) := by
        rw [show (m + 1) + 1 = m + 2 by omega]

/-- A standard root-coaffine odd identity tail and square `-d` give the
nonsplit weighted even order. -/
theorem natCard_weightedEvenOrthogonalGroup_eq_nonsplit_of_rootCoaffine_of_neg_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K) (m : ℕ)
    (h : RootCoaffineShellCardinality
      (1 : Matrix (Fin (2 * (m + 1) + 1))
        (Fin (2 * (m + 1) + 1)) K) 1
      (oddIdentityCoaffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m))
    (d : K) (hd : d ≠ 0) (t : K) (ht : t ^ 2 = -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d)) =
      nonsplitEvenIdentityOrthogonalOrderExpression (Nat.card K) (m + 2) := by
  have hshellAdd :=
    natCard_finSuccGramBlock_self_add_of_rootCoaffine_of_neg_mul_square
      hchar
      (1 : Matrix (Fin (2 * (m + 1) + 1))
        (Fin (2 * (m + 1) + 1)) K)
      1 (oddIdentityCoaffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m)
      h one_ne_zero d hd t (by simpa using ht)
  have harith := oddIdentityCoaffine_nextNonsplitNonzero_add
    (q := Nat.card K) (m := m) hq
  have hshell :
      Nat.card (finiteGramNormVectors
          (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d) d) =
        evenIdentityNonsplitNonzero (Nat.card K) (m + 1) := by
    apply Nat.add_right_cancel
    simpa only [finSuccIdentityGramMatrix] using hshellAdd.trans harith.symm
  have hrec := natCard_finSuccIdentityFixedNorm_mul_identityOrthogonal_eq
    (n := 2 * (m + 1) + 1) hchar d hd
  have hodd := natCard_oddIdentityOrthogonalGroup_eq_closedExpression
    hchar hq (m + 1) (by omega)
  calc
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d)) =
        evenIdentityNonsplitNonzero (Nat.card K) (m + 1) *
          Nat.card (finiteGramOrthogonalGroup
            (1 : Matrix (Fin (2 * (m + 1) + 1))
              (Fin (2 * (m + 1) + 1)) K)) := by
        rw [← hrec, hshell]
    _ = evenIdentityNonsplitNonzero (Nat.card K) (m + 1) *
          oddIdentityOrthogonalOrderExpression (Nat.card K) (m + 1) := by
        rw [hodd]
    _ = nonsplitEvenIdentityOrthogonalOrderExpression
          (Nat.card K) ((m + 1) + 1) :=
        oddToNonsplitEvenOrthogonalOrderExpression (Nat.card K) (m + 1)
    _ = nonsplitEvenIdentityOrthogonalOrderExpression
          (Nat.card K) (m + 2) := by
        rw [show (m + 1) + 1 = m + 2 by omega]

/-- A standard root-coaffine odd identity tail and nonsquare `-d` give the
split weighted even order. -/
theorem natCard_weightedEvenOrthogonalGroup_eq_split_of_rootCoaffine_of_neg_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K) (m : ℕ)
    (h : RootCoaffineShellCardinality
      (1 : Matrix (Fin (2 * (m + 1) + 1))
        (Fin (2 * (m + 1) + 1)) K) 1
      (oddIdentityCoaffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m))
    (d : K) (hd : d ≠ 0) (hneg : ∀ r : K, r ^ 2 ≠ -d) :
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d)) =
      splitEvenIdentityOrthogonalOrderExpression (Nat.card K) (m + 2) := by
  have hshellAdd :=
    natCard_finSuccGramBlock_self_add_of_rootCoaffine_of_neg_mul_nonsquare
      (1 : Matrix (Fin (2 * (m + 1) + 1))
        (Fin (2 * (m + 1) + 1)) K)
      1 (oddIdentityCoaffineBase (Nat.card K) m)
      (oddIdentityShellCorrection (Nat.card K) m)
      h one_ne_zero d hd (by simpa using hneg)
  have harith := oddIdentityCoaffine_nextSplitNonzero_add
    (q := Nat.card K) (m := m) hq
  have hshell :
      Nat.card (finiteGramNormVectors
          (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d) d) =
        evenIdentitySplitNonzero (Nat.card K) (m + 1) := by
    apply Nat.add_right_cancel
    simpa only [finSuccIdentityGramMatrix] using hshellAdd.trans harith.symm
  have hrec := natCard_finSuccIdentityFixedNorm_mul_identityOrthogonal_eq
    (n := 2 * (m + 1) + 1) hchar d hd
  have hodd := natCard_oddIdentityOrthogonalGroup_eq_closedExpression
    hchar hq (m + 1) (by omega)
  calc
    Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := 2 * (m + 1) + 1) d)) =
        evenIdentitySplitNonzero (Nat.card K) (m + 1) *
          Nat.card (finiteGramOrthogonalGroup
            (1 : Matrix (Fin (2 * (m + 1) + 1))
              (Fin (2 * (m + 1) + 1)) K)) := by
        rw [← hrec, hshell]
    _ = evenIdentitySplitNonzero (Nat.card K) (m + 1) *
          oddIdentityOrthogonalOrderExpression (Nat.card K) (m + 1) := by
        rw [hodd]
    _ = splitEvenIdentityOrthogonalOrderExpression
          (Nat.card K) ((m + 1) + 1) :=
        oddToSplitEvenOrthogonalOrderExpression (Nat.card K) (m + 1)
    _ = splitEvenIdentityOrthogonalOrderExpression
          (Nat.card K) (m + 2) := by
        rw [show (m + 1) + 1 = m + 2 by omega]

end PositiveDefiniteIntegralLattice
