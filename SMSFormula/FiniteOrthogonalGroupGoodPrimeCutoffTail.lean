import SMSFormula.FiniteOrthogonalGroupGoodPrimeAssembly

/-!
# Good-prime cutoff-tail assembly

This module proves the odd Euler-core product and the odd/even cutoff-tail
identities from the finite-set decomposition in `Product.lean` and the
good-prime factor evaluation.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The finite odd-rank classical inverse product is the reindexed Euler-core
inverse product. -/
lemma massGoodPrimeClassicalInverseProduct_eq_goodPrimeOddEulerCoreProduct
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p})
    (hS : ∀ p ∈ S, p ∉ massBadPrimeSet L)
    (s : ℕ) (hs : 0 < s) (hn : n = 2 * s - 1) :
    massGoodPrimeClassicalInverseProduct L S =
      goodPrimeOddEulerCoreInverseProduct S s := by
  rw [massGoodPrimeClassicalInverseProduct_eq_goodPrimeOddEulerProduct
    L S hS s hs hn,
    goodPrimeOddEulerProduct_eq_coreInverseProduct]

/-- Odd Euler-factor form of the good-prime cutoff tail. -/
lemma massPartialPrimeInverseProduct_eq_mul_goodPrimeOddEuler_tail_of_le
    (L : PositiveDefiniteIntegralLattice n) {N M : ℕ} (hNM : N ≤ M)
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (s : ℕ) (hs : 0 < s) (hn : n = 2 * s - 1) :
    massPartialPrimeInverseProduct L M =
      massPartialPrimeInverseProduct L N *
        ((rationalPrimesUpTo M \ rationalPrimesUpTo N).prod fun p =>
          (goodPrimeOddEulerFactor p s)⁻¹) := by
  let T := rationalPrimesUpTo M \ rationalPrimesUpTo N
  have hT :
      ∀ p ∈ T, p ∉ massBadPrimeSet L := by
    intro p hpT hpB
    exact (Finset.mem_sdiff.mp hpT).2 (hB hpB)
  calc
    massPartialPrimeInverseProduct L M =
        massPartialPrimeInverseProduct L N *
          massGoodPrimeClassicalInverseProduct L T := by
          simpa [T] using
            massPartialPrimeInverseProduct_eq_mul_goodPrimeClassical_tail_of_le
              (n := n) L hNM hB
    _ = massPartialPrimeInverseProduct L N *
          (T.prod fun p => (goodPrimeOddEulerFactor p s)⁻¹) := by
          rw [massGoodPrimeClassicalInverseProduct_eq_goodPrimeOddEulerProduct
            L T hT s hs hn]

/-- Odd Euler-core form of the same cutoff tail. -/
lemma massPartialPrimeInverseProduct_eq_mul_goodPrimeOddEulerCore_tail_of_le
    (L : PositiveDefiniteIntegralLattice n) {N M : ℕ} (hNM : N ≤ M)
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (s : ℕ) (hs : 0 < s) (hn : n = 2 * s - 1) :
    massPartialPrimeInverseProduct L M =
      massPartialPrimeInverseProduct L N *
        goodPrimeOddEulerCoreInverseProduct
          (rationalPrimesUpTo M \ rationalPrimesUpTo N) s := by
  rw [massPartialPrimeInverseProduct_eq_mul_goodPrimeOddEuler_tail_of_le
    (n := n) L hNM hB s hs hn,
    goodPrimeOddEulerProduct_eq_coreInverseProduct]

/-- Even character-Euler form of the good-prime cutoff tail. -/
lemma massPartialPrimeInverseProduct_eq_mul_goodPrimeEvenEuler_tail_of_le
    (L : PositiveDefiniteIntegralLattice n) {N M : ℕ} (hNM : N ≤ M)
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (s : ℕ) (hs : 0 < s) (hn : n = 2 * s) :
    massPartialPrimeInverseProduct L M =
      massPartialPrimeInverseProduct L N *
        ((rationalPrimesUpTo M \ rationalPrimesUpTo N).prod fun p =>
          (goodPrimeEvenEulerFactor L p s)⁻¹) := by
  let T := rationalPrimesUpTo M \ rationalPrimesUpTo N
  have hT :
      ∀ p ∈ T, p ∉ massBadPrimeSet L := by
    intro p hpT hpB
    exact (Finset.mem_sdiff.mp hpT).2 (hB hpB)
  calc
    massPartialPrimeInverseProduct L M =
        massPartialPrimeInverseProduct L N *
          massGoodPrimeClassicalInverseProduct L T := by
          simpa [T] using
            massPartialPrimeInverseProduct_eq_mul_goodPrimeClassical_tail_of_le
              (n := n) L hNM hB
    _ = massPartialPrimeInverseProduct L N *
          (T.prod fun p => (goodPrimeEvenEulerFactor L p s)⁻¹) := by
          rw [massGoodPrimeClassicalInverseProduct_eq_goodPrimeEvenEulerProduct
            L T hT s hs hn]

end PositiveDefiniteIntegralLattice
