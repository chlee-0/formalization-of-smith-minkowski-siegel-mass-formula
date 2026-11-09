import SMSFormula.PadicSpecialOrthogonalDifferentialDensityQuotientFiber
import SMSFormula.Product

/-!
# Bad-prime support of the selected-density-depth quotient fibers

Outside the literal finite Schulze--Pillot bad-prime set, the discriminant is
a p-adic unit.  The selected-depth discriminant-unit results therefore make
every ordinary-reduction fiber a singleton and identify the ordinary reduction
range cardinality with the associated-bilinear quotient count.

This module only localizes the already proved fiber statements.  It does not
evaluate any bad-prime fiber or identify either finite family with raw Gram
solutions.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Outside the Schulze--Pillot bad-prime set, every selected ordinary
reduction-to-quotient fiber is a singleton. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_fiber_eq_one_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    ∀ Y :
        L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
          q.1,
      Nat.card
          {u :
              L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                q.1 //
            L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
                q.1 u = Y} = 1 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  intro Y
  exact
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_fiber_eq_one_of_polarDeterminant_val_eq_zero
      q.1
      (padicValInt_polarDeterminant_eq_zero_of_not_mem_massBadPrimeSet L hq)
      Y

/-- Outside the Schulze--Pillot bad-prime set, the selected ordinary
reduction range has exactly the associated-bilinear quotient cardinality. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
          q.1) =
      associatedBilinearDualQuotientCount L q.1
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
          q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  exact
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_of_polarDeterminant_val_eq_zero
      q.1
      (padicValInt_polarDeterminant_eq_zero_of_not_mem_massBadPrimeSet L hq)

/-- Any failure of the selected ordinary-range/quotient-count equality is
supported on the literal Schulze--Pillot bad-prime set. -/
theorem
    mem_massBadPrimeSet_of_natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_ne_associatedBilinearDualQuotientCount
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hne :
      letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
      Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
            q.1) ≠
        associatedBilinearDualQuotientCount L q.1
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            q.1)) :
    q ∈ massBadPrimeSet L := by
  by_contra hq
  exact hne
    (L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_of_not_mem_massBadPrimeSet
      q hq)

end PositiveDefiniteIntegralLattice
