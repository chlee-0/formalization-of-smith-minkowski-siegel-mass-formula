import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruence

/-!
# The selected-density-depth quotient fibers

At the selected differential density depth, the Schulze--Pillot Hensel
hypothesis supplies maps between the associated-bilinear quotient
solution family and the ordinary integral stabilizer reduction range.  This
module specializes those maps, records their injection/retraction relation,
and decomposes the ordinary finite reduction cardinality exactly into the
fibers of the reduction-to-source map.

The fiber cardinalities are not evaluated.  In particular, no singleton,
uniformity, or local-density identification is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The associated-bilinear quotient family at the corrected differential
density depth. -/
abbrev
    localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :=
  associatedBilinearDualQuotientSolutionFamily L p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)

/-- The ordinary stabilizer reduction range at the corrected differential
density depth. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :=
  (L.localPadicLatticeStabilizerReduction p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)).range

/-- The existing Hensel lift from the selected associated-bilinear quotient
family into the ordinary stabilizer reduction range. -/
def
    localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily p →
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p :=
  L.associatedBilinearDualQuotientSolutionFamilyToLocalPadicLatticeStabilizerReductionRange
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p).associated_bilinear_quadratic_depth

/-- The ordinary reduction range coarsened to the selected
associated-bilinear quotient family. -/
def
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p →
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily p :=
  L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p).associated_bilinear_quadratic_depth

/-- The selected Hensel lift remains injective. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange_injective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective
      (L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
        p) :=
  L.associatedBilinearDualQuotientSolutionFamilyToLocalPadicLatticeStabilizerReductionRange_injective
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p).associated_bilinear_quadratic_depth

/-- Coarsening the selected Hensel lift recovers the original quotient
solution. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_apply_lift
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
          p Y) = Y :=
  L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily_apply_sourceLift
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p).associated_bilinear_quadratic_depth
    Y

/-- The selected reduction-to-source map is surjective, with the selected
Hensel lift as a right inverse. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_surjective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Surjective
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p) :=
  Function.RightInverse.surjective fun Y =>
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_apply_lift
      p Y

private theorem nat_card_eq_sum_natCard_fiber
    {α β : Type*} [Fintype α] [Fintype β] (f : α → β) :
    Nat.card α = ∑ b : β, Nat.card {a : α // f a = b} := by
  classical
  rw [Nat.card_eq_fintype_card]
  have hcard :
      Fintype.card α =
        ∑ b : β, ((Finset.univ : Finset α).filter fun a => f a = b).card := by
    simpa only [Finset.card_univ, Finset.mem_univ, true_implies] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset α))
        (t := (Finset.univ : Finset β))
        (f := f)
        (by intro a _ha; simp))
  calc
    Fintype.card α =
        ∑ b : β, ((Finset.univ : Finset α).filter fun a => f a = b).card :=
      hcard
    _ = ∑ b : β, Nat.card {a : α // f a = b} := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_subtype]

/-- The ordinary reduction range is the exact finite sum of the fibers over
the associated-bilinear quotient family at the selected density depth. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_sum_fibers
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p) =
      ∑ Y :
          L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
            p,
        Nat.card
          {u :
              L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                p //
            L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
                p u = Y} := by
  classical
  exact
    nat_card_eq_sum_natCard_fiber
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p)

/-- At the selected corrected density depth, every reduction-to-source fiber
is bounded by the full discriminant-controlled denominator fiber. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_fiber_le
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    Nat.card
        {u :
            L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
              p //
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
              p u = Y} ≤
      p ^ (n * padicValInt p L.polarDeterminant) := by
  simpa only
      [localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily] using
    L.natCard_localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily_fiber_le
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
        p).associated_bilinear_quadratic_depth
      (L.padicValInt_polarDeterminant_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
        p)
      Y

/-- At the selected corrected density depth, the ordinary reduction-range
cardinality lies between the quotient count and the quotient count times the
full discriminant-controlled fiber bound. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_natCard_sandwich
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualQuotientCount L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) ≤
        Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
            p) ∧
      Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
            p) ≤
        associatedBilinearDualQuotientCount L p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) *
          p ^ (n * padicValInt p L.polarDeterminant) :=
  L.localPadicLatticeStabilizerReduction_range_natCard_sandwich_of_polarDeterminant_val_le
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p).associated_bilinear_quadratic_depth
    (L.padicValInt_polarDeterminant_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p)

/-- At a discriminant-unit prime, every selected reduction-to-source fiber is
a singleton. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_fiber_eq_one_of_polarDeterminant_val_eq_zero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hdisc : padicValInt p L.polarDeterminant = 0)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    Nat.card
        {u :
            L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
              p //
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
              p u = Y} = 1 := by
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
  have hpos :
      0 <
        Nat.card
          {v :
              L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                p //
            L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
                p v = Y} :=
    Nat.card_pos
  have hle :=
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_fiber_le
      p Y
  rw [hdisc] at hle
  simp only [Nat.mul_zero, pow_zero] at hle
  omega

/-- At a discriminant-unit prime, the ordinary finite reduction range has
exactly the associated-bilinear quotient count. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_of_polarDeterminant_val_eq_zero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hdisc : padicValInt p L.polarDeterminant = 0) :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
          p) =
      associatedBilinearDualQuotientCount L p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
  have hsand :=
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_natCard_sandwich
      p
  apply Nat.le_antisymm
  · have hupp := hsand.2
    rw [hdisc] at hupp
    simpa only [Nat.mul_zero, pow_zero, Nat.mul_one] using hupp
  · exact hsand.1

/-- The established quotient-count lower bound at the selected corrected
density depth. -/
theorem
    associatedBilinearDualQuotientCount_le_natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualQuotientCount L p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) ≤
      Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p) :=
  L.associatedBilinearDualQuotientCount_le_natCard_localPadicLatticeStabilizerReduction_range
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p).associated_bilinear_quadratic_depth

/-- The internal Schulze--Pillot local-density formula specialized to the
selected corrected differential density depth. -/
theorem
    normalizedLocalDensity_eq_associatedBilinearDualQuotientCount_at_localPadicSpecialOrthogonalDifferentialDensityDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    normalizedLocalDensity L p =
      (((1 / 2 : ℚ) * twoPadicNormInvPow p n *
        ((p : ℚ) ^ localDensityDenominatorExponent n
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p))⁻¹ *
        (associatedBilinearDualQuotientCount L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) :
            ℚ) : ℚ) : ℝ) *
        gramDetPadicNormFactor L p :=
  normalizedLocalDensity_eq_associatedBilinearDualQuotientCount L p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p)

end PositiveDefiniteIntegralLattice
