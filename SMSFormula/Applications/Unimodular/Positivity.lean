import SMSFormula.Applications.Unimodular.GoodPrimes
import SMSFormula.FiniteOrthogonalGroupGoodPrimeOddPositivity
import SMSFormula.FiniteOrthogonalGroupGoodPrimeEvenPositivity

/-!
# Positivity for unimodular closed product expressions

This module reuses the existing good-prime positivity theorems after the
unimodular dyadic cutoff and zeta-core Euler-factor rewrites.  It proves only
positivity of already-defined product expressions; it does not evaluate the
dyadic local factor or any Dirichlet/L-value special value.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-- The odd-rank unimodular local-product expression with the zeta-core Euler
factor at `2` made explicit is strictly positive. -/
lemma unimodularOddExpandedProduct_pos (m : ℕ) :
    0 < massPartialPrimeInverseProduct L 2 *
      (Finset.Icc 1 m).prod
        (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
          (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) := by
  simpa [prod_goodPrimeEulerCoreZetaTailFactor_two,
    Nat.add_sub_cancel] using
    (oddRankOrdinaryMassProductExpression_pos L 2 (m + 1))

/-- The non-endpoint even-rank unimodular local-product expression with the
zeta-core Euler factor at `2` made explicit is strictly positive, stated with
the non-endpoint Dirichlet-character tail. -/
lemma unimodularEvenExpandedProductOfCharacter_pos_of_one_lt
    {m : ℕ} (hm : 1 < m) (hn : n = 2 * m) :
    0 < massPartialPrimeInverseProduct L 2 *
      ((Finset.Icc 1 (m - 1)).prod
        (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
          (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) *
          goodPrimeEvenDirichletTailFactorOfCharacter L 2 m) := by
  simpa [prod_goodPrimeEulerCoreZetaTailFactor_two] using
    (evenRankOrdinaryMassProductExpression_pos L 2 m hm hn)

/-- The non-endpoint even-rank unimodular local-product expression with the
zeta-core Euler factor at `2` made explicit is strictly positive, stated with
the total Dirichlet-tail factor. -/
lemma unimodularEvenExpandedProduct_pos_of_one_lt
    {m : ℕ} (hm : 1 < m) (hn : n = 2 * m) :
    0 < massPartialPrimeInverseProduct L 2 *
      ((Finset.Icc 1 (m - 1)).prod
        (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
          (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) *
          goodPrimeEvenCharacterDirichletTailFactor L 2 m) := by
  simpa [goodPrimeEvenCharacterDirichletTailFactor,
    if_neg (Nat.ne_of_gt hm)] using
    (unimodularEvenExpandedProductOfCharacter_pos_of_one_lt
      (L := L) hm hn)

end PositiveDefiniteIntegralLattice

end
