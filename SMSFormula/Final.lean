import SMSFormula.AdelicFinitePresentation
import SMSFormula.FiniteOrthogonalGroupGoodPrimeEven
import SMSFormula.ProperMass
import SMSFormula.RationalSpecialOrthogonalMassFormula
import SMSFormula.FiniteOrthogonalGroupGoodPrimeClosedLimit
import SMSFormula.FiniteOrthogonalGroupGoodPrimeOddPositivity
import SMSFormula.FiniteOrthogonalGroupGoodPrimeEvenPositivity

/-!
# Explicit odd- and even-rank forms of the mass formula

The ordinary mass formula `ordinaryGenusMass_eq_massFormulaProductSide`
(`SMSFormula.RationalSpecialOrthogonalMassFormula`) is stated for any limit `P`
of the cutoff inverse local-density products.  For a cutoff `N` containing every
bad prime, this module names that limit through the closed good-prime Euler
products (zeta factors in odd rank; zeta and Dirichlet factors in even rank)
and restates the formula with the limit inserted.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

universe u

variable {n : ℕ}

/-- The product-limit value used by the odd-rank Schulze--Pillot ordinary mass
formula after a cutoff containing all bad primes. -/
def oddRankOrdinaryMassProductLimit
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) : ℝ :=
  massPartialPrimeInverseProduct L N *
    (Finset.Icc 1 (s - 1)).prod
      (fun j => goodPrimeEulerCoreZetaTailFactor N j)

/-- The named closed odd-rank mass inverse-product limit is strictly positive. -/
lemma oddRankOrdinaryMassProductLimit_pos
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) :
    0 < oddRankOrdinaryMassProductLimit L N s := by
  rw [oddRankOrdinaryMassProductLimit]
  exact oddRankOrdinaryMassProductExpression_pos L N s

/-- The product-limit value used by the even-rank Schulze--Pillot ordinary mass
formula after a cutoff containing all bad primes. -/
def evenRankOrdinaryMassProductLimit
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) : ℝ :=
  massPartialPrimeInverseProduct L N *
    ((Finset.Icc 1 (s - 1)).prod
      (fun j => goodPrimeEulerCoreZetaTailFactor N j) *
        goodPrimeEvenCharacterDirichletTailFactor L N s)

/-- The named non-endpoint even-rank mass inverse-product limit is strictly
positive. -/
lemma evenRankOrdinaryMassProductLimit_pos_of_one_lt
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) (hs : 1 < s) (hn : n = 2 * s) :
    0 < evenRankOrdinaryMassProductLimit L N s := by
  rw [evenRankOrdinaryMassProductLimit,
    goodPrimeEvenCharacterDirichletTailFactor,
    if_neg (Nat.ne_of_gt hs)]
  exact evenRankOrdinaryMassProductExpression_pos L N s hs hn

/-- The positive-definite ordinary mass formula in odd rank with
the closed zeta Euler product inserted literally. -/
theorem ordinaryGenusMass_eq_massFormulaProductSide_oddRankProductLimit
    (L : PositiveDefiniteIntegralLattice n) (hn3 : 3 ≤ n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s - 1) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massFormulaProductSide L
        (oddRankOrdinaryMassProductLimit L N s) := by
  apply L.ordinaryGenusMass_eq_massFormulaProductSide hn3
    (oddRankOrdinaryMassProductLimit_pos L N s)
  simpa [oddRankOrdinaryMassProductLimit] using
    (massLocalInverseProductTendsTo_of_goodPrimeOddZetaEulerProduct
      L hB hs hn)

/-- The positive-definite ordinary mass formula in even rank with
the non-endpoint zeta/Dirichlet Euler product inserted literally. -/
theorem ordinaryGenusMass_eq_massFormulaProductSide_evenRankProductLimit
    (L : PositiveDefiniteIntegralLattice n) (hn3 : 3 ≤ n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hn : n = 2 * s) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massFormulaProductSide L
        (evenRankOrdinaryMassProductLimit L N s) := by
  have hs1 : 1 < s := by omega
  apply L.ordinaryGenusMass_eq_massFormulaProductSide hn3
    (evenRankOrdinaryMassProductLimit_pos_of_one_lt L N s hs1 hn)
  simpa [evenRankOrdinaryMassProductLimit,
    goodPrimeEvenCharacterDirichletTailFactor,
    if_neg (Nat.ne_of_gt hs1)] using
    (massLocalInverseProductTendsTo_of_goodPrimeEvenDirichletEulerProduct_one_lt
      L hB hs1 hn)

end PositiveDefiniteIntegralLattice

end
