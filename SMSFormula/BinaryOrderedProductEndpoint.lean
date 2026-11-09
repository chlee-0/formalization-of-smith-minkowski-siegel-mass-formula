import SMSFormula.FiniteOrthogonalGroupGoodPrimeClosedLimit
import SMSFormula.StandardAxiomsGuard

/-!
# Positive ordered local product in rank two

The endpoint uses the existing increasing-prime cutoff convergence and
Mathlib's nonvanishing of a nontrivial Dirichlet L-function at one.
This module does not identify the limit with the actual binary genus mass.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The existing real rank-two tail is the real embedding of its complex limit. -/
lemma binaryCharacterEndpointTail_ofReal
    (K : PositiveDefiniteIntegralLattice 2) (N : ℕ)
    (hB : massBadPrimeSet K ⊆ rationalPrimesUpTo N) :
    ((goodPrimeEvenCharacterDirichletEndpointTailFactor K N : ℝ) : ℂ) =
      goodPrimeEvenCharacterDirichletEndpointComplexTailFactor K N := by
  have hreal := dirichlet_L_goodPrimeEvenCharacterEndpointInverseProductTendsTo
    K N hB (by norm_num)
  unfold goodPrimeEvenCharacterInverseProductTendsTo at hreal
  have hemb := (Complex.continuous_ofReal.tendsto _).comp hreal
  have hcomplex := dirichlet_L_goodPrimeEvenCharacterEndpointComplexTail_tendsto
    K N (by norm_num) (goodPrimeEvenDirichletCharacter_ne_one K (by norm_num))
  have hemb' : Filter.Tendsto
      (fun M : ℕ => ((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
        (1 - goodPrimeEvenDirichletCharacter K 1 p *
          (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)
      Filter.atTop
      (nhds ((goodPrimeEvenCharacterDirichletEndpointTailFactor K N : ℝ) : ℂ)) := by
    refine Filter.Tendsto.congr' ?_ hemb
    filter_upwards with M
    have hnotBad : ∀ p ∈ rationalPrimesUpTo M \ rationalPrimesUpTo N,
        p ∉ massBadPrimeSet K := by
      intro p hp hpB
      exact (Finset.mem_sdiff.mp hp).2 (hB hpB)
    have hcast := goodPrimeEvenCharacterInverseProduct_ofReal_of_forall_not_mem_bad
      K (rationalPrimesUpTo M \ rationalPrimesUpTo N) 1 hnotBad (by norm_num)
    have hmap :
        ((rationalPrimesUpTo M \ rationalPrimesUpTo N).prod fun p =>
          (1 - goodPrimeEvenDirichletCharacter K 1 p.1 *
            (p.1 : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹) =
          (((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
            (1 - goodPrimeEvenDirichletCharacter K 1 p *
              (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹) := by
      rw [← rationalPrimesUpTo_sdiff_map_val_eq_primesBelow_sdiff N M]
      simp [Finset.prod_map, rationalPrimeValEmbedding]
    exact hcast.trans hmap
  exact tendsto_nhds_unique hemb' hcomplex

/-- Nonvanishing at one prevents the real endpoint tail from being zero. -/
lemma binaryCharacterEndpointTail_ne_zero
    (K : PositiveDefiniteIntegralLattice 2) (N : ℕ)
    (hB : massBadPrimeSet K ⊆ rationalPrimesUpTo N) :
    goodPrimeEvenCharacterDirichletEndpointTailFactor K N ≠ 0 := by
  letI : NeZero (goodPrimeEvenDirichletModulus K 1) :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos K 1)⟩
  have hcomplex : goodPrimeEvenCharacterDirichletEndpointComplexTailFactor K N ≠ 0 := by
    unfold goodPrimeEvenCharacterDirichletEndpointComplexTailFactor
    apply div_ne_zero
    · exact DirichletCharacter.LFunction_apply_one_ne_zero
        (goodPrimeEvenDirichletCharacter_ne_one K (by norm_num))
    · apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      exact dirichlet_L_nontrivial_character_endpoint_eulerFactor_ne_zero
        (goodPrimeEvenDirichletCharacter K 1) p (Nat.prime_of_mem_primesBelow hp)
  intro hz
  have heq := binaryCharacterEndpointTail_ofReal K N hB
  rw [hz, Complex.ofReal_zero] at heq
  exact hcomplex heq.symm

/-- Every actual binary lattice has a positive increasing-prime inverse-product
limit, without a caller convergence certificate. No mass identification is used. -/
theorem exists_pos_massLocalInverseProductTendsTo_rank_two
    (K : PositiveDefiniteIntegralLattice 2) :
    ∃ P : ℝ, 0 < P ∧ massLocalInverseProductTendsTo K P := by
  classical
  let N := (massBadPrimeSet K).sup fun p => p.1
  have hB : massBadPrimeSet K ⊆ rationalPrimesUpTo N := by
    intro p hp
    rw [mem_rationalPrimesUpTo_iff]
    change p.1 ≤ (massBadPrimeSet K).sup (fun q => q.1)
    exact Finset.le_sup hp
  let P := massPartialPrimeInverseProduct K N *
    goodPrimeEvenCharacterDirichletEndpointTailFactor K N
  have hconv : massLocalInverseProductTendsTo K P := by
    simpa [P, goodPrimeEvenCharacterDirichletTailFactor] using
      massLocalInverseProductTendsTo_of_goodPrimeEvenDirichletEulerProduct
        K hB (s := 1) (by norm_num) (by norm_num)
  have hnonneg : 0 ≤ P := by
    exact ge_of_tendsto' hconv (fun M => (massPartialPrimeInverseProduct_pos K M).le)
  have hne : P ≠ 0 := mul_ne_zero
    (massPartialPrimeInverseProduct_pos K N).ne'
    (binaryCharacterEndpointTail_ne_zero K N hB)
  exact ⟨P, lt_of_le_of_ne hnonneg (Ne.symm hne), hconv⟩

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryCharacterEndpointTail_ofReal
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryCharacterEndpointTail_ne_zero
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_pos_massLocalInverseProductTendsTo_rank_two
#print axioms PositiveDefiniteIntegralLattice.binaryCharacterEndpointTail_ofReal
#print axioms PositiveDefiniteIntegralLattice.binaryCharacterEndpointTail_ne_zero
#print axioms PositiveDefiniteIntegralLattice.exists_pos_massLocalInverseProductTendsTo_rank_two
