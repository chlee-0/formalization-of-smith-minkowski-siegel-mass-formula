import SMSFormula.FiniteOrthogonalGroupGoodPrimeEven

/-!
# Good-prime local-factor assembly

This downstream module proves the elementary local-factor and finite-product
statements from the completed odd and even pointwise density theorems.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- At a good prime in odd rank, the product-facing local factor is the odd
unramified Euler factor. -/
lemma massLocalFactorAtPrime_eq_goodPrimeOddEulerFactor
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) (s : ℕ) (hs : 0 < s)
    (hn : n = 2 * s - 1) :
    massLocalFactorAtPrime L p =
      goodPrimeOddEulerFactor p s := by
  rw [massLocalFactorAtPrime_eq_classicalSolutionCountLocalDensity_of_not_mem_bad
      (n := n) L p hp,
    goodPrime_classicalSolutionCountLocalDensity_factor_odd
      L p hp s hs hn]

/-- At a good prime in even rank, the product-facing local factor is the even
Euler factor with its explicit quadratic character. -/
lemma massLocalFactorAtPrime_eq_goodPrimeEvenEulerFactor
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) (s : ℕ) (hs : 0 < s)
    (hn : n = 2 * s) :
    massLocalFactorAtPrime L p =
      goodPrimeEvenEulerFactor L p s := by
  rw [massLocalFactorAtPrime_eq_classicalSolutionCountLocalDensity_of_not_mem_bad
      (n := n) L p hp,
    goodPrime_classicalSolutionCountLocalDensity_factor_even
      L p hp s hs hn]

/-- At a good prime in odd rank, the local inverse mass factor is the inverse
of the odd Euler factor. -/
lemma massLocalInverseFactorAtPrime_eq_goodPrimeOddEulerFactor_inv
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) (s : ℕ) (hs : 0 < s)
    (hn : n = 2 * s - 1) :
    massLocalInverseFactorAtPrime L p =
      (goodPrimeOddEulerFactor p s)⁻¹ := by
  rw [massLocalInverseFactorAtPrime,
    massLocalFactorAtPrime_eq_goodPrimeOddEulerFactor
      (n := n) L p hp s hs hn]

/-- At a good prime in even rank, the local inverse mass factor is the inverse
of the even Euler factor. -/
lemma massLocalInverseFactorAtPrime_eq_goodPrimeEvenEulerFactor_inv
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) (s : ℕ) (hs : 0 < s)
    (hn : n = 2 * s) :
    massLocalInverseFactorAtPrime L p =
      (goodPrimeEvenEulerFactor L p s)⁻¹ := by
  rw [massLocalInverseFactorAtPrime,
    massLocalFactorAtPrime_eq_goodPrimeEvenEulerFactor
      (n := n) L p hp s hs hn]

/-- A finite product of odd-rank good-prime classical inverse factors is the
corresponding finite Euler product. -/
lemma massGoodPrimeClassicalInverseProduct_eq_goodPrimeOddEulerProduct
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p})
    (hS : ∀ p ∈ S, p ∉ massBadPrimeSet L)
    (s : ℕ) (hs : 0 < s) (hn : n = 2 * s - 1) :
    massGoodPrimeClassicalInverseProduct L S =
      S.prod fun p => (goodPrimeOddEulerFactor p s)⁻¹ := by
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [goodPrime_classicalSolutionCountLocalDensity_factor_odd
    L p (hS p hp) s hs hn]

/-- A finite product of even-rank good-prime classical inverse factors is the
corresponding finite character Euler product. -/
lemma massGoodPrimeClassicalInverseProduct_eq_goodPrimeEvenEulerProduct
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p})
    (hS : ∀ p ∈ S, p ∉ massBadPrimeSet L)
    (s : ℕ) (hs : 0 < s) (hn : n = 2 * s) :
    massGoodPrimeClassicalInverseProduct L S =
      S.prod fun p => (goodPrimeEvenEulerFactor L p s)⁻¹ := by
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [goodPrime_classicalSolutionCountLocalDensity_factor_even
    L p (hS p hp) s hs hn]

end PositiveDefiniteIntegralLattice
