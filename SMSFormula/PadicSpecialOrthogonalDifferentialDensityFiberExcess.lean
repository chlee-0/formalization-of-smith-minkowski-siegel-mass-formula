import SMSFormula.PadicSpecialOrthogonalDifferentialDensityQuotientFiberBadPrimeSupport

/-!
# The exact selected-density-depth fiber excess

The ordinary finite stabilizer reduction range can be larger than the
associated-bilinear quotient family at a bad prime.  This module packages the
difference as a literal natural-number excess.  The existing lower bound makes
the subtraction exact, while the selected Hensel lift shows that the excess is
the sum of `fiber cardinality - 1`.

The excess vanishes outside the finite Schulze--Pillot bad-prime set.  No
bad-prime value is evaluated here.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The natural-number excess of the selected ordinary reduction range over
the associated-bilinear quotient family. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityFiberExcess
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  Nat.card
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
        p) -
    associatedBilinearDualQuotientCount L p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)

/-- The selected ordinary reduction cardinality is exactly the quotient count
plus its natural-number fiber excess. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_add_fiberExcess
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
          p) =
      associatedBilinearDualQuotientCount L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) +
        L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess p := by
  unfold localPadicSpecialOrthogonalDifferentialDensityFiberExcess
  have hle :=
    L.associatedBilinearDualQuotientCount_le_natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
      p
  omega

/-- Every selected reduction-to-quotient fiber contains the selected Hensel
lift of its quotient-family point. -/
theorem
    one_le_natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_fiber
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    1 ≤
      Nat.card
        {u :
            L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
              p //
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
              p u = Y} := by
  let u :
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p :=
    L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
      p Y
  letI : Nonempty
      {v :
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
            p //
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            p v = Y} :=
    ⟨⟨u,
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_apply_lift
        p Y⟩⟩
  exact Nat.card_pos

/-- The selected fiber excess is exactly the sum of the nontrivial
multiplicities `fiber cardinality - 1`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityFiberExcess_eq_sum_fiber_natCard_sub_one
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess p =
      ∑ Y :
          L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
            p,
        (Nat.card
            {u :
                L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                  p //
              L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
                  p u = Y} -
          1) := by
  classical
  let Q :=
    L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
      p
  let fiberCard : Q → ℕ := fun Y =>
    Nat.card
      {u :
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
            p //
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            p u = Y}
  have hfiber (Y : Q) : 1 ≤ fiberCard Y := by
    exact
      L.one_le_natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_fiber
        p Y
  have hsum :
      (∑ Y : Q, fiberCard Y) =
        Nat.card Q + ∑ Y : Q, (fiberCard Y - 1) := by
    calc
      (∑ Y : Q, fiberCard Y) =
          ∑ Y : Q, (1 + (fiberCard Y - 1)) := by
            apply Finset.sum_congr rfl
            intro Y _hY
            have := hfiber Y
            omega
      _ = (∑ _Y : Q, 1) + ∑ Y : Q, (fiberCard Y - 1) := by
            rw [Finset.sum_add_distrib]
      _ = Nat.card Q + ∑ Y : Q, (fiberCard Y - 1) := by
            rw [Nat.card_eq_fintype_card]
            simp
  have hrange :
      Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
            p) =
        ∑ Y : Q, fiberCard Y := by
    simpa only [Q, fiberCard] using
      L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_sum_fibers
        p
  have hquotient :
      associatedBilinearDualQuotientCount L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) =
        Nat.card Q := by
    simpa only [Q] using
      associatedBilinearDualQuotientCount_eq_natCard_solutionFamily
        L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  change
    Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
            p) -
        associatedBilinearDualQuotientCount L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) =
      ∑ Y : Q, (fiberCard Y - 1)
  rw [hrange, hquotient, hsum]
  omega

/-- Outside the Schulze--Pillot bad-prime set, the selected fiber excess
vanishes. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityFiberExcess_eq_zero_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess q.1 = 0 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold localPadicSpecialOrthogonalDifferentialDensityFiberExcess
  rw [
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_of_not_mem_massBadPrimeSet
      q hq]
  exact Nat.sub_self _

/-- A nonzero selected fiber excess can occur only at a prime in the literal
Schulze--Pillot bad-prime set. -/
theorem
    mem_massBadPrimeSet_of_localPadicSpecialOrthogonalDifferentialDensityFiberExcess_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hne :
      letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
      L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess q.1 ≠ 0) :
    q ∈ massBadPrimeSet L := by
  by_contra hq
  exact hne
    (L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess_eq_zero_of_not_mem_massBadPrimeSet
      q hq)

end PositiveDefiniteIntegralLattice
