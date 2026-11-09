import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDoubledAttainedResidueSubgroup
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceFiberTorsor

/-!
# Quotient descent for shifted dyadic Cayley residues

This module descends the absolute scaled-residue class from the shifted
dyadic denominator subgroup `H₂` to its complete-depth quotient `H₂/K₂`.
The exact equality criterion and surjectivity construct an explicit
equivalence with the finite additive quotient `T₂/N₂'`.

Composing with the already completed ordinary-reduction fiber torsor gives an
explicit equivalence from every dyadic ordinary quotient fiber to `T₂/N₂'`.
No cardinality identity or gauge value is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_dyadic_quotient_descent : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

local instance
    localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence_normal_quotientDescent
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence.Normal := by
  change
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction.ker.Normal
  infer_instance

/-- The absolute scaled-residue class descends from `H₂` to `H₂/K₂`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientToDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotient →
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossQuotient :=
  Quotient.lift
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceToDeterminantLossQuotient
    (fun g h hrel ↦ by
      apply
        (L.dyadicDenominatorCongruenceToDeterminantLossQuotient_eq_iff_mul_inv_mem_principalKernel
          g h).2
      apply QuotientGroup.eq_iff_div_mem.mp
      exact Quotient.sound hrel)

@[simp]
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientToDeterminantLossQuotient_mk
    (L : PositiveDefiniteIntegralLattice n)
    (g :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientToDeterminantLossQuotient
        (QuotientGroup.mk g) =
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceToDeterminantLossQuotient
        g :=
  rfl

/-- The descended absolute scaled-residue class map is surjective. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientToDeterminantLossQuotient_surjective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Surjective
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientToDeterminantLossQuotient := by
  intro t
  obtain ⟨g, hg⟩ :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceToDeterminantLossQuotient_surjective
      t
  exact ⟨QuotientGroup.mk g, hg⟩

/-- The descended absolute-class map is injective by the exact relative
principal-kernel equality criterion, not by finite cardinality. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientToDeterminantLossQuotient_injective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Injective
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientToDeterminantLossQuotient := by
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | _ g =>
      induction r using Quotient.inductionOn' with
      | _ h =>
          apply QuotientGroup.eq_iff_div_mem.mpr
          exact
            (L.dyadicDenominatorCongruenceToDeterminantLossQuotient_eq_iff_mul_inv_mem_principalKernel
              g h).1 hqr

/-- The finite quotient equivalence predicted by the shifted
dyadic denominator-Cayley route. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientEquivDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotient ≃
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossQuotient :=
  Equiv.ofBijective
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientToDeterminantLossQuotient
    ⟨L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientToDeterminantLossQuotient_injective,
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientToDeterminantLossQuotient_surjective⟩

/-- Every complete ordinary dyadic quotient fiber is explicitly equivalent to
the enlarged determinant-loss quotient `T₂/N₂'`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionFiberEquivDyadicDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        2) :
    {u :
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange 2 //
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
          2 u = Y} ≃
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossQuotient :=
  (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientEquivOrdinaryReductionFiber
      Y).symm.trans
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientEquivDeterminantLossQuotient

end PositiveDefiniteIntegralLattice
