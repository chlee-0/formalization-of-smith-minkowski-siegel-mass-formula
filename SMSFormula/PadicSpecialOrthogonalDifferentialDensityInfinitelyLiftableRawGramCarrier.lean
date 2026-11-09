import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramInfiniteLiftStabilizer

/-!
# Infinitely liftable selected-depth raw Gram solutions

This module packages the selected-depth complete raw Gram solutions that admit
one coherent infinite compatible lift branch.  It identifies this finite
subtype with the literal ordinary integral-stabilizer reduction range by maps
constructed from actual stabilizer reductions in both directions.

No cardinality of either carrier or local gauge value is computed.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The finite subtype of selected-depth complete raw Gram solutions admitting
one coherent infinite compatible lift branch. -/
def localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :=
  {X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p //
    Nonempty
      (L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) X)}

/-- The selected coherent branch retained by an infinitely liftable raw Gram
solution. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolutionChain
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p) :
    L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) X.1 :=
  Classical.choice X.2

/-- Forgetting invertibility from an actual ordinary stabilizer reduction
produces an infinitely liftable selected-depth raw Gram solution. -/
def localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionToInfinitelyLiftableRawGram
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p →
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p :=
  fun u ↦
    let X :=
      L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) u
    ⟨X, by
      apply
        (L.hasFullInitialRawGramLift_iff_nonempty_infiniteLiftChain p X).mp
      apply
        (L.hasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift_iff_exists_ordinaryReduction
          p X).mpr
      exact ⟨u, rfl⟩⟩

@[simp] theorem
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionToInfinitelyLiftableRawGram_val
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (u : L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p) :
    (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionToInfinitelyLiftableRawGram
      p u).1 =
      L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) u :=
  rfl

/-- A coherent branch gives an actual integral stabilizer, whose selected-
depth reduction lies in the literal ordinary reduction range. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToOrdinaryReduction
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution p →
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p :=
  fun X ↦
    let C :=
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolutionChain
        p X
    ⟨L.localPadicLatticeStabilizerReduction p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        C.padicLimitStabilizer,
      ⟨C.padicLimitStabilizer, rfl⟩⟩

/-- Forgetting invertibility after reconstructing the stabilizer from an
infinite branch recovers the prescribed complete raw Gram solution literally. -/
@[simp] theorem
    localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions_infinitelyLiftableRawGramToOrdinaryReduction
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p) :
    L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToOrdinaryReduction
          p X) =
      X.1 := by
  apply Subtype.ext
  exact
    (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolutionChain
      p X).stabilizerReduction_base_val

/-- The literal ordinary stabilizer reduction range is equivalent to the
selected-depth complete raw Gram solutions admitting a coherent infinite
branch. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionEquivInfinitelyLiftableRawGram
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p ≃
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p :=
  { toFun :=
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionToInfinitelyLiftableRawGram
        p
    invFun :=
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToOrdinaryReduction
        p
    left_inv := by
      intro u
      apply
        L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions_injective
          p (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      rw [L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions_infinitelyLiftableRawGramToOrdinaryReduction]
      rfl
    right_inv := by
      intro X
      apply Subtype.ext
      rw [L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionToInfinitelyLiftableRawGram_val]
      exact
        L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions_infinitelyLiftableRawGramToOrdinaryReduction
          p X }

/-- The ordinary reduction cardinality is exactly the cardinality of the
infinitely liftable selected-depth complete raw Gram subtype. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_infinitelyLiftableRawGram
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p) =
      Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
          p) :=
  Nat.card_congr
    (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionEquivInfinitelyLiftableRawGram
      p)

end PositiveDefiniteIntegralLattice
