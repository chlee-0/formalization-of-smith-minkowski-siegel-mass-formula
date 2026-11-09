import SMSFormula.FiniteOrthogonalGroupGoodPrimeCutoffTail

/-!
# Transport from good-prime Euler tails to mass-product convergence

This module proves a generic convergence transport for the mass product.
It assumes the relevant Euler-tail convergence statements and changes only
the eventual finite-product equality; no closed zeta or Dirichlet limit is
invoked here.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- An odd Euler-core tail limit transports to the corresponding mass local
inverse-product limit through the cutoff identity. -/
lemma massLocalInverseProductTendsTo_of_goodPrimeOddEulerCoreTail
    (L : PositiveDefiniteIntegralLattice n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s - 1) {P : ℝ}
    (hP : goodPrimeOddEulerCoreInverseProductTendsTo N s P) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L N * P) := by
  unfold massLocalInverseProductTendsTo
  unfold goodPrimeOddEulerCoreInverseProductTendsTo at hP
  have hmul :
      Filter.Tendsto
        (fun M : ℕ =>
          massPartialPrimeInverseProduct L N *
            goodPrimeOddEulerCoreInverseProduct
              (rationalPrimesUpTo M \ rationalPrimesUpTo N) s)
        Filter.atTop
        (nhds (massPartialPrimeInverseProduct L N * P)) :=
    tendsto_const_nhds.mul hP
  refine Filter.Tendsto.congr' ?_ hmul
  show ∀ᶠ M : ℕ in Filter.atTop,
    massPartialPrimeInverseProduct L N *
        goodPrimeOddEulerCoreInverseProduct
          (rationalPrimesUpTo M \ rationalPrimesUpTo N) s =
      massPartialPrimeInverseProduct L M
  rw [Filter.eventually_atTop]
  refine ⟨N, ?_⟩
  intro M hNM
  exact
    (massPartialPrimeInverseProduct_eq_mul_goodPrimeOddEulerCore_tail_of_le
      (n := n) L hNM hB s hs hn).symm

/-- A family of fixed Euler-core factor limits yields the odd mass-product
limit through the primitive transport. -/
lemma massLocalInverseProductTendsTo_of_goodPrimeOddEulerCoreFactors
    (L : PositiveDefiniteIntegralLattice n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s - 1) (P : ℕ → ℝ)
    (hP : ∀ j ∈ Finset.Icc 1 (s - 1),
      goodPrimeEulerCoreInverseProductTendsTo N j (P j)) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L N *
        (Finset.Icc 1 (s - 1)).prod P) :=
  massLocalInverseProductTendsTo_of_goodPrimeOddEulerCoreTail
    (n := n) L hB hs hn
    (goodPrimeOddEulerCoreInverseProductTendsTo_of_core N s P hP)

/-- An even character-Euler tail limit transports to the even mass local
inverse-product limit through the cutoff identity. -/
lemma massLocalInverseProductTendsTo_of_goodPrimeEvenEulerTail
    (L : PositiveDefiniteIntegralLattice n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s) {P : ℝ}
    (hP : goodPrimeEvenEulerInverseProductTendsTo L N s P) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L N * P) := by
  unfold massLocalInverseProductTendsTo
  unfold goodPrimeEvenEulerInverseProductTendsTo at hP
  have hmul :
      Filter.Tendsto
        (fun M : ℕ =>
          massPartialPrimeInverseProduct L N *
            ((rationalPrimesUpTo M \ rationalPrimesUpTo N).prod fun p =>
              (goodPrimeEvenEulerFactor L p s)⁻¹))
        Filter.atTop
        (nhds (massPartialPrimeInverseProduct L N * P)) :=
    tendsto_const_nhds.mul hP
  refine Filter.Tendsto.congr' ?_ hmul
  show ∀ᶠ M : ℕ in Filter.atTop,
    massPartialPrimeInverseProduct L N *
        ((rationalPrimesUpTo M \ rationalPrimesUpTo N).prod fun p =>
          (goodPrimeEvenEulerFactor L p s)⁻¹) =
      massPartialPrimeInverseProduct L M
  rw [Filter.eventually_atTop]
  refine ⟨N, ?_⟩
  intro M hNM
  exact
    (massPartialPrimeInverseProduct_eq_mul_goodPrimeEvenEuler_tail_of_le
      (n := n) L hNM hB s hs hn).symm

/-- Separate even core and character limits combine, through the even convergence
transport, into convergence of the local inverse product. -/
lemma massLocalInverseProductTendsTo_of_goodPrimeEvenCoreAndCharacterTail
    (L : PositiveDefiniteIntegralLattice n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s) {Pcore Pχ : ℝ}
    (hcore : goodPrimeOddEulerCoreInverseProductTendsTo N s Pcore)
    (hχ : goodPrimeEvenCharacterInverseProductTendsTo L N s Pχ) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L N * (Pcore * Pχ)) :=
  massLocalInverseProductTendsTo_of_goodPrimeEvenEulerTail
    (n := n) L hB hs hn
    (goodPrimeEvenEulerInverseProductTendsTo_of_core_and_character
      L hcore hχ)

end PositiveDefiniteIntegralLattice
