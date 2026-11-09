import SMSFormula.PadicSpecialOrthogonalDifferentialDensityAttainedResidueSubgroup
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceFiberTorsor

/-!
# Quotient descent for odd-prime denominator Cayley residues

This module descends the absolute Cayley residue class from `H_k` to the
already defined quotient `H_k/K_k`.  The exact equality criterion and
surjectivity construct an explicit equivalence with the finite additive
quotient `T/N`.

No cardinality or gauge value is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence_normal_quotientDescent
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p).Normal := by
  change
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p).ker.Normal
  infer_instance

/-- The absolute Cayley residue class descends from `H_k` to `H_k/K_k`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientToDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotient p →
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossQuotient p hp2 :=
  Quotient.lift
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceToDeterminantLossQuotient
      p hp2)
    (fun g h hrel ↦ by
      apply
        (L.denominatorCongruenceToDeterminantLossQuotient_eq_iff_mul_inv_mem_principalKernel
          p hp2 g h).2
      apply QuotientGroup.eq_iff_div_mem.mp
      exact Quotient.sound hrel)

@[simp]
theorem
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientToDeterminantLossQuotient_mk
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientToDeterminantLossQuotient
        p hp2 (QuotientGroup.mk g) =
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceToDeterminantLossQuotient
        p hp2 g :=
  rfl

/-- The descended absolute-class map is surjective. -/
theorem
    surjective_denominatorCongruenceQuotientToDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Function.Surjective
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientToDeterminantLossQuotient
        p hp2) := by
  intro t
  obtain ⟨g, hg⟩ :=
    L.surjective_denominatorCongruenceToDeterminantLossQuotient p hp2 t
  exact ⟨QuotientGroup.mk g, hg⟩

/-- The descended absolute-class map is injective, by the exact principal-
kernel equality criterion rather than by finite cardinality. -/
theorem
    injective_denominatorCongruenceQuotientToDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Function.Injective
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientToDeterminantLossQuotient
        p hp2) := by
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | _ g =>
      induction r using Quotient.inductionOn' with
      | _ h =>
          apply QuotientGroup.eq_iff_div_mem.mpr
          exact
            (L.denominatorCongruenceToDeterminantLossQuotient_eq_iff_mul_inv_mem_principalKernel
              p hp2 g h).1 hqr

/-- The finite quotient equivalence predicted by the denominator-
congruence Cayley route. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientEquivDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotient p ≃
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossQuotient p hp2 :=
  Equiv.ofBijective
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientToDeterminantLossQuotient
      p hp2)
    ⟨L.injective_denominatorCongruenceQuotientToDeterminantLossQuotient p hp2,
      L.surjective_denominatorCongruenceQuotientToDeterminantLossQuotient p hp2⟩

/-- Every exact liftable quotient fiber is explicitly equivalent to `T/N`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiberEquivDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily p) :
    L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber p hp2 Y ≃
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossQuotient p hp2 :=
  (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiberEquivDenominatorCongruenceQuotient
      p hp2 Y).trans
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientEquivDeterminantLossQuotient
      p hp2)

end PositiveDefiniteIntegralLattice
