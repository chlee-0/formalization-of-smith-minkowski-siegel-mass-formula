import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityQuotientFiber

/-!
# Raw Gram solutions and the selected quotient family

At an odd prime, every raw Gram-congruence solution coarsens columnwise to
the selected associated-bilinear quotient family.  This module proves that
the resulting map is surjective and that the concrete ordinary stabilizer
reduction square commutes literally.

The complete fiber of the raw map is exactly the already computed full
column-denominator fiber.  The ordinary stabilizer fiber injects into it.
Surjectivity of this last injection is deliberately not asserted: it is the
missing initial-value-preserving Hensel lifting theorem.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Raw Gram-congruence solutions at the selected differential density
depth. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityRawGramSolution
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :=
  let k := L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) //
    X ∈ gramCongruenceSolutionMatrices L p k}

/-- Coarsen the columns of an odd-prime raw Gram solution to the selected
associated-bilinear quotient family. -/
def localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p →
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily p := by
  let k := L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  let E := associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  let hPE : primePowCoordinateSubmodule (n := n) p k ≤ E :=
    L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
      p k
  let hE : IsDualQuotientAdmissible L p k E :=
    L.associatedBilinearDualPadicDenominatorIntegralPreimage_admissible p k
      (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
        p).associated_bilinear_quadratic_depth
  intro X
  exact
    ⟨localDualQuotientFamilyOfLE (n := n) hPE
        (localDualQuotientLiftFamily (n := n) p k X.1),
      localDualQuotientLiftFamilyOfLE_mem_localDualQuotientSolutionFamilies_of_gram_odd
        (L := L) (p := p) (k := k) hp2 hPE hE X.2⟩

@[simp] theorem
    localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily_val
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p) :
    (L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily
        p hp2 X).1 =
      localDualQuotientFamilyOfLE (n := n)
        (L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
          p (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p))
        (localDualQuotientLiftFamily (n := n) p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) X.1) :=
  rfl

/-- Forgetting invertibility and then coarsening a concrete ordinary
stabilizer reduction agrees literally with the existing ordinary-to-quotient
map. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensity_rawGram_ordinaryReduction_commutes
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (u : L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p) :
    L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily
        p hp2
        (L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) u) =
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p u := by
  rfl

/-- The selected raw Gram coarsening is surjective.  A preimage is obtained
by forgetting invertibility from the selected Hensel lift. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily_surjective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Function.Surjective
      (L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily
        p hp2) := by
  intro Y
  let u :=
    L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
      p Y
  refine
    ⟨L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) u, ?_⟩
  rw [L.localPadicSpecialOrthogonalDifferentialDensity_rawGram_ordinaryReduction_commutes
    p hp2]
  exact
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_apply_lift
      p Y

/-- The ordinary stabilizer fiber embeds into the corresponding exact raw
Gram fiber through the literal commuting square. -/
def localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionFiberToRawGramFiber
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily p) :
    {u : L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p //
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p u = Y} →
      {X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p //
        L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily
          p hp2 X = Y} :=
  fun u ↦
    ⟨L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) u.1,
      (L.localPadicSpecialOrthogonalDifferentialDensity_rawGram_ordinaryReduction_commutes
        p hp2 u.1).trans u.2⟩

theorem
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionFiberToRawGramFiber_injective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily p) :
    Function.Injective
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionFiberToRawGramFiber
        p hp2 Y) := by
  intro u v huv
  apply Subtype.ext
  exact
    L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions_injective
      p (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      (congrArg Subtype.val huv)

end PositiveDefiniteIntegralLattice
