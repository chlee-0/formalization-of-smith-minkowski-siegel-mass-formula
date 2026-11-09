import SMSFormula.FiniteOrthogonalGroupGoodPrimeClosedLimit

/-!
# Positivity of the closed odd good-prime product

This module proves strict positivity of each closed Riemann-zeta Euler tail
and of the resulting odd mass inverse-product expression.  It is downstream
of the finite orthogonal-group chain.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Every real inverse Euler-core factor is strictly positive in the range
used by the zeta product. -/
lemma goodPrimeEulerCoreInverseFactor_pos
    (p : {p : ℕ // Nat.Prime p}) (j : ℕ) (hj : 1 ≤ j) :
    0 < (1 - (p.1 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))⁻¹ := by
  have hp : (1 : ℝ) < p.1 := by
    exact_mod_cast p.2.one_lt
  have hjR : (0 : ℝ) < j := by
    exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hpow : (p.1 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg hp
      (neg_neg_iff_pos.mpr (mul_pos (by norm_num) hjR))
  exact inv_pos.mpr (sub_pos.mpr hpow)

/-- The finite inverse Euler-core product at the cutoff is strictly positive. -/
lemma goodPrimeEulerCoreInverseProduct_pos
    (S : Finset {p : ℕ // Nat.Prime p}) (j : ℕ) (hj : 1 ≤ j) :
    0 < goodPrimeEulerCoreInverseProduct S j := by
  rw [goodPrimeEulerCoreInverseProduct]
  exact Finset.prod_pos fun p _hp =>
    goodPrimeEulerCoreInverseFactor_pos p j hj

/-- The real value of the Riemann zeta function at `2j` is strictly positive
for every positive exponent index. -/
lemma riemannZeta_two_mul_nat_re_pos (j : ℕ) (hj : 1 ≤ j) :
    0 < (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re := by
  apply riemannZeta_re_pos_of_one_lt
  exact_mod_cast (show 1 < 2 * j by omega)

/-- Removing a finite positive Euler prefix from `ζ(2j)` leaves a strictly
positive closed tail factor. -/
lemma goodPrimeEulerCoreZetaTailFactor_pos
    (N j : ℕ) (hj : 1 ≤ j) :
    0 < goodPrimeEulerCoreZetaTailFactor N j := by
  rw [goodPrimeEulerCoreZetaTailFactor]
  exact mul_pos
    (riemannZeta_two_mul_nat_re_pos j hj)
    (inv_pos.mpr
      (goodPrimeEulerCoreInverseProduct_pos
        (rationalPrimesUpTo N) j hj))

/-- The finite product of closed zeta tails occurring in odd rank is strictly
positive, including the empty-product endpoint. -/
lemma goodPrimeOddZetaTailProduct_pos (N s : ℕ) :
    0 < (Finset.Icc 1 (s - 1)).prod
      (fun j => goodPrimeEulerCoreZetaTailFactor N j) := by
  exact Finset.prod_pos fun j hj =>
    goodPrimeEulerCoreZetaTailFactor_pos N j
      (Finset.mem_Icc.mp hj).1

/-- The explicit real expression used as the odd-rank mass inverse-product
limit is strictly positive. -/
lemma oddRankOrdinaryMassProductExpression_pos
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) :
    0 < massPartialPrimeInverseProduct L N *
      (Finset.Icc 1 (s - 1)).prod
        (fun j => goodPrimeEulerCoreZetaTailFactor N j) := by
  exact mul_pos
    (massPartialPrimeInverseProduct_pos L N)
    (goodPrimeOddZetaTailProduct_pos N s)

end PositiveDefiniteIntegralLattice
