import SMSFormula.Applications.Examples.TernaryElevenLift
import SMSFormula.Applications.Examples.TernaryModelTransport
import SMSFormula.Applications.Examples.TernaryAnalyticFactors
import SMSFormula.FiniteOrthogonalGroupGoodPrimeClosedLimit

/-! The actual ordered inverse-density product for the determinant-22 example. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice

theorem ternary_badPrimes_le_eleven :
    massBadPrimeSet ternaryLattice ⊆ rationalPrimesUpTo 11 := by
  rw [ternary_badPrimes]
  decide

theorem ternary_goodPrimes_eleven :
    rationalPrimesUpTo 11 \ massBadPrimeSet ternaryLattice =
      {⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩} := by
  rw [ternary_badPrimes]
  decide

theorem ternary_badInverseProduct : massBadPrimeInverseProduct ternaryLattice = 121 / 40 := by
  unfold massBadPrimeInverseProduct
  rw [ternary_badPrimes]
  norm_num [massFinitePrimeInverseProduct, massLocalInverseFactorAtPrime, massLocalFactorAtPrime,
    massLocalFactor, ternary_density_two, ternary_density_eleven]

theorem ternary_partialInverseProduct_eleven :
    massPartialPrimeInverseProduct ternaryLattice 11 = 29645 / 8192 := by
  rw [massPartialPrimeInverseProduct_eq_badPrimeSet_mul_goodPrimeClassical
    ternaryLattice 11 ternary_badPrimes_le_eleven]
  rw [massGoodPrimeClassicalInverseProduct_eq_goodPrimeOddEulerProduct
    ternaryLattice _ (by intro p hp; exact (Finset.mem_sdiff.mp hp).2) 2 (by decide) (by decide)]
  rw [ternary_badInverseProduct, ternary_goodPrimes_eleven]
  norm_num [goodPrimeOddEulerFactor, goodPrimeEulerCore, Real.rpow_neg_natCast]

theorem ternary_oddProductExpression :
    massPartialPrimeInverseProduct ternaryLattice 11 *
      (Finset.Icc 1 (2 - 1)).prod (fun j => goodPrimeEulerCoreZetaTailFactor 11 j) =
      3 * Real.pi ^ 2 / 8 := by
  rw [ternary_partialInverseProduct_eleven]
  norm_num only [Nat.reduceSub, Finset.Icc_self, Finset.prod_singleton]
  rw [ternary_zetaTail_eleven]
  ring

theorem ternary_inverseProduct_limit :
    massLocalInverseProductTendsTo ternaryLattice (3 * Real.pi ^ 2 / 8) := by
  have h := massLocalInverseProductTendsTo_of_goodPrimeOddZetaEulerProduct
    ternaryLattice ternary_badPrimes_le_eleven (s := 2) (by decide) (by decide)
  rwa [ternary_oddProductExpression] at h

end MassFormulaReleaseExamples
