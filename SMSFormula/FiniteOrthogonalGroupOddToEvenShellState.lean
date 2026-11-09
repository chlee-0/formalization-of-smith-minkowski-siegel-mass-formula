import SMSFormula.FiniteOrthogonalGroupEvenToOddShellState

/-!
# Odd-to-even quadratic-shell state transition

The completed weighted-binary evaluations turn a root-affine odd-dimensional
shell family into an even-dimensional family with one value at zero and one
uniform value away from zero.  For a root-coaffine family the same evaluation
first produces exact complementary additive equations.  Those equations are
converted to explicit shell values only when matching natural-number witnesses
are supplied, so no truncated subtraction enters the transition.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Complementary zero/nonzero shell data.  The two shell values may have
different corrections, but both corrected values equal the same total. -/
def ComplementaryZeroNonzeroShellCardinality
    {K : Type*} [Field K] [Finite K]
    (B : Matrix (Fin n) (Fin n) K)
    (zeroCorrection nonzeroCorrection total : ℕ) : Prop :=
  Nat.card (finiteGramNormVectors B 0) + zeroCorrection = total ∧
    ∀ c : K, c ≠ 0 →
      Nat.card (finiteGramNormVectors B c) + nonzeroCorrection = total

/-- Matching explicit natural values convert complementary shell equations to
literal zero/nonzero shell cardinalities. -/
theorem ComplementaryZeroNonzeroShellCardinality.toZeroNonzero
    {K : Type*} [Field K] [Finite K]
    {B : Matrix (Fin n) (Fin n) K}
    {zeroCorrection nonzeroCorrection total zeroCard nonzeroCard : ℕ}
    (h : ComplementaryZeroNonzeroShellCardinality B
      zeroCorrection nonzeroCorrection total)
    (hzero : zeroCard + zeroCorrection = total)
    (hnonzero : nonzeroCard + nonzeroCorrection = total) :
    ZeroNonzeroShellCardinality B zeroCard nonzeroCard := by
  constructor
  · exact Nat.add_right_cancel (h.1.trans hzero.symm)
  · intro c hc
    exact Nat.add_right_cancel ((h.2 c hc).trans hnonzero.symm)

/-! ### Root-affine states -/

/-- A root-affine shell with nonsquare `-ε` produces explicit uniform
zero/nonzero data in the next dimension. -/
theorem zeroNonzeroShellCardinality_finSuccGramBlock_of_rootAffine_of_neg_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (hneg : ∀ r : K, r ^ 2 ≠ -ε) :
    ZeroNonzeroShellCardinality (finSuccGramBlock 1 B)
      (Nat.card K * base + correction)
      (Nat.card K * base + correction * (Nat.card K + 1)) := by
  constructor
  · exact natCard_finSuccGramBlock_zero_of_rootAffine_of_neg_nonsquare
      B ε base correction h hneg
  · intro c hc
    exact natCard_finSuccGramBlock_ne_zero_of_rootAffine_of_neg_nonsquare
      B ε base correction h hε hneg c hc

/-- A root-affine shell with square `-ε` produces explicit uniform
zero/nonzero data in the next dimension. -/
theorem zeroNonzeroShellCardinality_finSuccGramBlock_of_rootAffine_of_neg_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootAffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (t : K) (ht : t ^ 2 = -ε) :
    ZeroNonzeroShellCardinality (finSuccGramBlock 1 B)
      (Nat.card K * base + correction * (2 * Nat.card K - 1))
      (Nat.card K * base + correction * (Nat.card K - 1)) := by
  constructor
  · exact natCard_finSuccGramBlock_zero_of_rootAffine_of_neg_square
      hchar B ε base correction h hε t ht
  · intro c hc
    exact natCard_finSuccGramBlock_ne_zero_of_rootAffine_of_neg_square
      hchar B ε base correction h hε t ht c hc

/-! ### Root-coaffine states -/

/-- A root-coaffine shell with nonsquare `-ε` produces exact complementary
zero/nonzero equations in the next dimension. -/
theorem complementaryZeroNonzeroShellCardinality_finSuccGramBlock_of_rootCoaffine_of_neg_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (hneg : ∀ r : K, r ^ 2 ≠ -ε) :
    ComplementaryZeroNonzeroShellCardinality (finSuccGramBlock 1 B)
      correction (correction * (Nat.card K + 1)) (Nat.card K * base) := by
  constructor
  · exact natCard_finSuccGramBlock_zero_add_of_rootCoaffine_of_neg_nonsquare
      B ε base correction h hneg
  · intro c hc
    exact natCard_finSuccGramBlock_ne_zero_add_of_rootCoaffine_of_neg_nonsquare
      B ε base correction h hε hneg c hc

/-- A root-coaffine shell with square `-ε` produces exact complementary
zero/nonzero equations in the next dimension. -/
theorem complementaryZeroNonzeroShellCardinality_finSuccGramBlock_of_rootCoaffine_of_neg_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (t : K) (ht : t ^ 2 = -ε) :
    ComplementaryZeroNonzeroShellCardinality (finSuccGramBlock 1 B)
      (correction * (2 * Nat.card K - 1))
      (correction * (Nat.card K - 1)) (Nat.card K * base) := by
  constructor
  · exact natCard_finSuccGramBlock_zero_add_of_rootCoaffine_of_neg_square
      hchar B ε base correction h hε t ht
  · intro c hc
    exact natCard_finSuccGramBlock_ne_zero_add_of_rootCoaffine_of_neg_square
      hchar B ε base correction h hε t ht c hc

/-- Explicit witnesses for the complementary nonsplit values upgrade the
root-coaffine transition to literal zero/nonzero shell cardinalities. -/
theorem zeroNonzeroShellCardinality_finSuccGramBlock_of_rootCoaffine_of_neg_nonsquare
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (hneg : ∀ r : K, r ^ 2 ≠ -ε)
    (zeroCard nonzeroCard : ℕ)
    (hzero : zeroCard + correction = Nat.card K * base)
    (hnonzero : nonzeroCard + correction * (Nat.card K + 1) =
      Nat.card K * base) :
    ZeroNonzeroShellCardinality (finSuccGramBlock 1 B)
      zeroCard nonzeroCard :=
  (complementaryZeroNonzeroShellCardinality_finSuccGramBlock_of_rootCoaffine_of_neg_nonsquare
    B ε base correction h hε hneg).toZeroNonzero hzero hnonzero

/-- Explicit witnesses for the complementary split values upgrade the
root-coaffine transition to literal zero/nonzero shell cardinalities. -/
theorem zeroNonzeroShellCardinality_finSuccGramBlock_of_rootCoaffine_of_neg_square
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (ε : K) (base correction : ℕ)
    (h : RootCoaffineShellCardinality B ε base correction)
    (hε : ε ≠ 0) (t : K) (ht : t ^ 2 = -ε)
    (zeroCard nonzeroCard : ℕ)
    (hzero : zeroCard + correction * (2 * Nat.card K - 1) =
      Nat.card K * base)
    (hnonzero : nonzeroCard + correction * (Nat.card K - 1) =
      Nat.card K * base) :
    ZeroNonzeroShellCardinality (finSuccGramBlock 1 B)
      zeroCard nonzeroCard :=
  (complementaryZeroNonzeroShellCardinality_finSuccGramBlock_of_rootCoaffine_of_neg_square
    hchar B ε base correction h hε t ht).toZeroNonzero hzero hnonzero

end PositiveDefiniteIntegralLattice
