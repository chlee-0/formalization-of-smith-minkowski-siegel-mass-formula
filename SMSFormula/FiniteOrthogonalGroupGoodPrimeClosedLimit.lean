import SMSFormula.FiniteOrthogonalGroupGoodPrimeConvergenceTransport

/-!
# Closed good-prime Euler limits for mass partial products

This module combines the finite-group convergence transport with
the repository's internally proved Riemann-zeta and Dirichlet-character Euler
limits.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The closed odd-rank zeta Euler product gives the mass local inverse-product
limit through the good-prime transport. -/
lemma massLocalInverseProductTendsTo_of_goodPrimeOddZetaEulerProduct
    (L : PositiveDefiniteIntegralLattice n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s - 1) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L N *
        (Finset.Icc 1 (s - 1)).prod
          (fun j => goodPrimeEulerCoreZetaTailFactor N j)) := by
  refine
    massLocalInverseProductTendsTo_of_goodPrimeOddEulerCoreFactors
      (n := n) L hB hs hn
      (fun j => goodPrimeEulerCoreZetaTailFactor N j) ?_
  intro j hj
  exact riemann_zeta_goodPrimeEulerCoreInverseProductTendsTo N j
    (Finset.mem_Icc.mp hj).1

/-- The closed even zeta-core and Dirichlet-character Euler products give the
mass local inverse-product limit through the good-prime transport.
-/
lemma massLocalInverseProductTendsTo_of_goodPrimeEvenDirichletEulerProduct
    (L : PositiveDefiniteIntegralLattice n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L N *
        ((Finset.Icc 1 (s - 1)).prod
          (fun j => goodPrimeEulerCoreZetaTailFactor N j) *
            goodPrimeEvenCharacterDirichletTailFactor L N s)) := by
  refine
    massLocalInverseProductTendsTo_of_goodPrimeEvenCoreAndCharacterTail
      (n := n) L hB hs hn ?_ ?_
  · refine goodPrimeOddEulerCoreInverseProductTendsTo_of_core
      N s (fun j => goodPrimeEulerCoreZetaTailFactor N j) ?_
    intro j hj
    exact riemann_zeta_goodPrimeEulerCoreInverseProductTendsTo N j
      (Finset.mem_Icc.mp hj).1
  · exact dirichlet_L_goodPrimeEvenCharacterInverseProductTendsTo
      L N s hB hs hn

/-- For `1 < s`, the explicit Dirichlet-character tail gives the even mass
local inverse-product limit through the good-prime transport. -/
lemma massLocalInverseProductTendsTo_of_goodPrimeEvenDirichletEulerProduct_one_lt
    (L : PositiveDefiniteIntegralLattice n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hs : 1 < s) (hn : n = 2 * s) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L N *
        ((Finset.Icc 1 (s - 1)).prod
          (fun j => goodPrimeEulerCoreZetaTailFactor N j) *
            goodPrimeEvenDirichletTailFactorOfCharacter L N s)) := by
  refine
    massLocalInverseProductTendsTo_of_goodPrimeEvenCoreAndCharacterTail
      (n := n) L hB (Nat.lt_trans Nat.zero_lt_one hs) hn ?_ ?_
  · refine goodPrimeOddEulerCoreInverseProductTendsTo_of_core
      N s (fun j => goodPrimeEulerCoreZetaTailFactor N j) ?_
    intro j hj
    exact riemann_zeta_goodPrimeEulerCoreInverseProductTendsTo N j
      (Finset.mem_Icc.mp hj).1
  · exact dirichlet_L_goodPrimeEvenCharacterInverseProductTendsTo_of_one_lt
      L N s hB hs hn

end PositiveDefiniteIntegralLattice
