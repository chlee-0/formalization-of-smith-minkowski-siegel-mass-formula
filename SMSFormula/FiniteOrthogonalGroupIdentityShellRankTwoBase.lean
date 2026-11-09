import SMSFormula.FiniteOrthogonalGroupIdentityShellMutualArithmetic

/-!
# Binary base of the mutual identity-shell induction

The rank-two identity shell is literally the fiber of the binary
sum-of-squares map.  The existing split and nonsplit binary counts therefore
give the `m = 0` instances of the named even identity-shell states.  A final
matrix-equality transport packages the repeated leading-one block as the
literal identity Gram matrix two dimensions higher.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The rank-two identity fixed-norm shell is the binary sum-of-squares fiber,
with both directions given by the literal two coordinates. -/
noncomputable def rankTwoIdentityFixedNormEquivBinarySumSquares
    {K : Type*} [Field K] (c : K) :
    finiteGramNormVectors (1 : Matrix (Fin 2) (Fin 2) K) c ≃
      binarySumSquaresFiber K c where
  toFun v := ⟨(v.1 0, v.1 1), by
    simpa [finiteGramNormVectors, gramQuadraticValue, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, pow_two] using v.2⟩
  invFun z := ⟨![z.1.1, z.1.2], by
    simpa [finiteGramNormVectors, gramQuadraticValue, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, pow_two] using z.2⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv z := by
    rcases z with ⟨⟨x, y⟩, hxy⟩
    rfl

@[simp] lemma rankTwoIdentityFixedNormEquivBinarySumSquares_apply_val
    {K : Type*} [Field K] (c : K)
    (v : finiteGramNormVectors (1 : Matrix (Fin 2) (Fin 2) K) c) :
    (rankTwoIdentityFixedNormEquivBinarySumSquares c v).1 =
      (v.1 0, v.1 1) := rfl

/-- The split binary identity form supplies the standard `m=0` larger-zero
state. -/
theorem zeroNonzeroShellCardinality_rankTwoIdentity_of_neg_one_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (t : K) (ht : t ^ 2 = -1) :
    ZeroNonzeroShellCardinality
      (1 : Matrix (Fin 2) (Fin 2) K)
      (evenIdentitySplitZero (Nat.card K) 0)
      (evenIdentitySplitNonzero (Nat.card K) 0) := by
  constructor
  · calc
      Nat.card (finiteGramNormVectors
          (1 : Matrix (Fin 2) (Fin 2) K) 0) =
          Nat.card (binarySumSquaresFiber K 0) :=
        Nat.card_congr (rankTwoIdentityFixedNormEquivBinarySumSquares 0)
      _ = 2 * Nat.card K - 1 :=
        natCard_binarySumSquaresFiber_zero_of_neg_one_square hchar t ht
      _ = evenIdentitySplitZero (Nat.card K) 0 := by
        simp only [evenIdentitySplitZero, evenIdentityShellMain,
          evenIdentityShellCorrection, Nat.mul_zero, zero_add, pow_zero,
          pow_one, Nat.mul_one]
        omega
  · intro c hc
    calc
      Nat.card (finiteGramNormVectors
          (1 : Matrix (Fin 2) (Fin 2) K) c) =
          Nat.card (binarySumSquaresFiber K c) :=
        Nat.card_congr (rankTwoIdentityFixedNormEquivBinarySumSquares c)
      _ = Nat.card K - 1 :=
        natCard_binarySumSquaresFiber_of_neg_one_square_ne_zero
          hchar t ht c hc
      _ = evenIdentitySplitNonzero (Nat.card K) 0 := by
        simp [evenIdentitySplitNonzero, evenIdentityShellMain,
          evenIdentityShellCorrection]

/-- The nonsplit binary identity form supplies the standard `m=0`
larger-nonzero state. -/
theorem zeroNonzeroShellCardinality_rankTwoIdentity_of_neg_one_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (hq : 2 ≤ Nat.card K)
    (hneg : ∀ r : K, r ^ 2 ≠ -1) :
    ZeroNonzeroShellCardinality
      (1 : Matrix (Fin 2) (Fin 2) K)
      (evenIdentityNonsplitZero (Nat.card K) 0)
      (evenIdentityNonsplitNonzero (Nat.card K) 0) := by
  by_cases hbad : ringChar K = 2
  · exact (hchar hbad).elim
  · constructor
    · calc
        Nat.card (finiteGramNormVectors
            (1 : Matrix (Fin 2) (Fin 2) K) 0) =
            Nat.card (binarySumSquaresFiber K 0) :=
          Nat.card_congr (rankTwoIdentityFixedNormEquivBinarySumSquares 0)
        _ = 1 := natCard_binarySumSquaresFiber_zero_of_neg_one_nonsquare hneg
        _ = evenIdentityNonsplitZero (Nat.card K) 0 := by
          simp only [evenIdentityNonsplitZero, evenIdentityShellMain,
            evenIdentityShellCorrection, Nat.mul_zero, zero_add, pow_zero,
            pow_one, Nat.mul_one]
          omega
    · intro c hc
      calc
        Nat.card (finiteGramNormVectors
            (1 : Matrix (Fin 2) (Fin 2) K) c) =
            Nat.card (binarySumSquaresFiber K c) :=
          Nat.card_congr (rankTwoIdentityFixedNormEquivBinarySumSquares c)
        _ = Nat.card K + 1 :=
          natCard_binarySumSquaresFiber_of_neg_one_nonsquare_ne_zero hneg c hc
        _ = evenIdentityNonsplitNonzero (Nat.card K) 0 := by
          simp [evenIdentityNonsplitNonzero, evenIdentityShellMain,
            evenIdentityShellCorrection]

/-- Two successive leading-one blocks are the identity Gram matrix two ranks
higher. -/
theorem finSuccGramBlock_two_one
    {K : Type*} [Field K] (n : ℕ) :
    finSuccGramBlock 1
        (finSuccGramBlock 1 (1 : Matrix (Fin n) (Fin n) K)) =
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) K) := by
  rw [finSuccGramBlock_one, finSuccGramBlock_one]

/-- Transport a shell state on two successive leading-one blocks to the
literal identity Gram matrix. -/
theorem zeroNonzeroShellCardinality_identity_of_twoBlocks
    {K : Type*} [Field K] [Finite K]
    {n zeroCard nonzeroCard : ℕ}
    (h : ZeroNonzeroShellCardinality
      (finSuccGramBlock 1
        (finSuccGramBlock 1 (1 : Matrix (Fin n) (Fin n) K)))
      zeroCard nonzeroCard) :
    ZeroNonzeroShellCardinality
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
      zeroCard nonzeroCard := by
  simpa only [finSuccGramBlock_two_one] using h

end PositiveDefiniteIntegralLattice
