import SMSFormula.Applications.Unimodular.Gram
import SMSFormula.FiniteOrthogonalGroupGoodPrimeClosedLimit
import SMSFormula.Product

/-!
# Good-prime support for unimodular lattices

For a classically unimodular integral lattice (`pairingDeterminant = 1`), the repository's
Schulze--Pillot bad-prime set has no odd prime support: the polar discriminant
is `2^n`.  Thus all bad primes are contained in the dyadic cutoff
`rationalPrimesUpTo 2`.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The dyadic rational-prime cutoff contains exactly the prime `2`. -/
lemma rationalPrimesUpTo_two :
    rationalPrimesUpTo 2 = {⟨2, Nat.prime_two⟩} := by
  ext p
  constructor
  · intro hp
    rw [mem_rationalPrimesUpTo_iff] at hp
    exact Finset.mem_singleton.mpr <|
      Subtype.ext (le_antisymm hp p.2.two_le)
  · intro hp
    rw [mem_rationalPrimesUpTo_iff]
    have hp' : p = ⟨2, Nat.prime_two⟩ := Finset.mem_singleton.mp hp
    simp [hp']

variable {n : ℕ} {L : PositiveDefiniteIntegralLattice n}

/-- The dyadic cutoff partial inverse product is just the inverse local factor
at `2`; no density evaluation is used. -/
lemma massPartialPrimeInverseProduct_two
    (L : PositiveDefiniteIntegralLattice n) :
    massPartialPrimeInverseProduct L 2 =
      (L.massLocalFactor 2)⁻¹ := by
  rw [massPartialPrimeInverseProduct, rationalPrimesUpTo_two,
    massFinitePrimeInverseProduct]
  simp [massLocalInverseFactorAtPrime, massLocalFactorAtPrime]

/-- At the dyadic cutoff, the finite inverse zeta-core product is the single
removed Euler factor at `2`. -/
lemma goodPrimeEulerCoreInverseProduct_two (j : ℕ) :
    goodPrimeEulerCoreInverseProduct (rationalPrimesUpTo 2) j =
      (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))⁻¹ := by
  simp [goodPrimeEulerCoreInverseProduct, rationalPrimesUpTo_two]

/-- The zeta-core good-prime tail after the dyadic cutoff is the full zeta
value with the Euler factor at `2` removed. -/
lemma goodPrimeEulerCoreZetaTailFactor_two (j : ℕ) :
    goodPrimeEulerCoreZetaTailFactor 2 j =
      (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
        (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))) := by
  simp [goodPrimeEulerCoreZetaTailFactor,
    goodPrimeEulerCoreInverseProduct_two]

/-- Product form of the dyadic zeta-core tail identity over a contiguous range
of core exponents. -/
lemma prod_goodPrimeEulerCoreZetaTailFactor_two (r : ℕ) :
    (Finset.Icc 1 r).prod
        (fun j => goodPrimeEulerCoreZetaTailFactor 2 j) =
      (Finset.Icc 1 r).prod
        (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
          (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) := by
  refine Finset.prod_congr rfl ?_
  intro j _hj
  exact goodPrimeEulerCoreZetaTailFactor_two j

/-- A prime dividing the polar discriminant of a classically unimodular lattice
is dyadic. -/
theorem prime_dvd_polarDeterminant_natAbs_eq_two_of_isUnimodular
    (hL : L.IsUnimodular) (p : {p : ℕ // Nat.Prime p})
    (hp : p.1 ∣ L.polarDeterminant.natAbs) : p.1 = 2 := by
  have hdisc : L.polarDeterminant = (2 : ℤ) ^ n := L.polarDeterminant_eq_two_pow_of_isUnimodular hL
  have hp_pow : p.1 ∣ 2 ^ n := by
    simpa [hdisc] using hp
  have hp_two : p.1 ∣ 2 := p.2.dvd_of_dvd_pow hp_pow
  exact ((Nat.dvd_prime Nat.prime_two).mp hp_two).resolve_left p.2.ne_one

/-- For a classically unimodular lattice, the Schulze--Pillot bad-prime set is
contained in the dyadic rational-prime cutoff. -/
theorem massBadPrimeSet_subset_rationalPrimesUpTo_two_of_isUnimodular
    (hL : L.IsUnimodular) :
    massBadPrimeSet L ⊆ rationalPrimesUpTo 2 := by
  intro p hp
  rw [mem_rationalPrimesUpTo_iff]
  rcases (mem_massBadPrimeSet_iff L p).mp hp with hp_two | hp_disc
  · omega
  · have hp_two' : p.1 = 2 :=
      prime_dvd_polarDeterminant_natAbs_eq_two_of_isUnimodular hL p hp_disc
    omega

/-- Under classical unimodularity the project bad-prime set is exactly the
single dyadic prime. -/
theorem massBadPrimeSet_eq_rationalPrimesUpTo_two_of_isUnimodular
    (hL : L.IsUnimodular) :
    massBadPrimeSet L = rationalPrimesUpTo 2 := by
  refine Finset.Subset.antisymm
    (massBadPrimeSet_subset_rationalPrimesUpTo_two_of_isUnimodular hL) ?_
  intro p hp
  rw [rationalPrimesUpTo_two] at hp
  have hp_two : p = ⟨2, Nat.prime_two⟩ := Finset.mem_singleton.mp hp
  rw [hp_two]
  exact (mem_massBadPrimeSet_iff L ⟨2, Nat.prime_two⟩).mpr (Or.inl rfl)

/-- At the dyadic cutoff, the finite inverse product splits into the fixed
bad-prime prefix and the remaining good-prime classical factors for a
classically unimodular lattice. -/
theorem massPartialPrimeInverseProduct_two_eq_badPrimeSet_mul_goodPrimeClassical
    (hL : L.IsUnimodular) :
    massPartialPrimeInverseProduct L 2 =
      massBadPrimeInverseProduct L *
        massGoodPrimeClassicalInverseProduct L
          (rationalPrimesUpTo 2 \ massBadPrimeSet L) := by
  exact massPartialPrimeInverseProduct_eq_badPrimeSet_mul_goodPrimeClassical
    L 2 (massBadPrimeSet_subset_rationalPrimesUpTo_two_of_isUnimodular hL)

/-- After the dyadic cutoff, every newly adjoined prime is a good prime for a
classically unimodular lattice. -/
theorem massPartialPrimeInverseProduct_eq_two_mul_goodPrimeClassical_tail
    (hL : L.IsUnimodular) {M : ℕ} (hM : 2 ≤ M) :
    massPartialPrimeInverseProduct L M =
      massPartialPrimeInverseProduct L 2 *
        massGoodPrimeClassicalInverseProduct L
          (rationalPrimesUpTo M \ rationalPrimesUpTo 2) := by
  exact massPartialPrimeInverseProduct_eq_mul_goodPrimeClassical_tail_of_le
    L hM (massBadPrimeSet_subset_rationalPrimesUpTo_two_of_isUnimodular hL)

/-- The closed odd-rank zeta Euler product, specialized to the dyadic cutoff
forced by classical unimodularity.  This is still the existing product-limit
route; no local factor at `2` is evaluated. -/
theorem massLocalInverseProductTendsTo_unimodular_odd_zeta
    (hL : L.IsUnimodular) {s : ℕ} (hs : 0 < s) (hn : n = 2 * s - 1) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        (Finset.Icc 1 (s - 1)).prod
          (fun j => goodPrimeEulerCoreZetaTailFactor 2 j)) := by
  exact massLocalInverseProductTendsTo_of_goodPrimeOddZetaEulerProduct
    L (massBadPrimeSet_subset_rationalPrimesUpTo_two_of_isUnimodular hL) hs hn

/-- Odd-rank product-limit convergence in the application parameterization
`n = 2*m + 1`, with the old parameter `s = m + 1`. -/
theorem massLocalInverseProductTendsTo_unimodular_odd_zeta_of_two_mul_add_one
    (hL : L.IsUnimodular) {m : ℕ} (hn : n = 2 * m + 1) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        (Finset.Icc 1 m).prod
          (fun j => goodPrimeEulerCoreZetaTailFactor 2 j)) := by
  have hn' : n = 2 * (m + 1) - 1 := by omega
  simpa [Nat.add_sub_cancel] using
    massLocalInverseProductTendsTo_unimodular_odd_zeta
      (L := L) hL (s := m + 1) (by omega) hn'

/-- Odd-rank product-limit convergence with each zeta-core tail written as
`ζ(2j)` times the removed Euler factor at `2`. -/
theorem massLocalInverseProductTendsTo_unimodular_odd_zeta_removed_two
    (hL : L.IsUnimodular) {s : ℕ} (hs : 0 < s) (hn : n = 2 * s - 1) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        (Finset.Icc 1 (s - 1)).prod
          (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
            (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))))) := by
  simpa [prod_goodPrimeEulerCoreZetaTailFactor_two] using
    massLocalInverseProductTendsTo_unimodular_odd_zeta
      (L := L) hL hs hn

/-- Odd-rank product-limit convergence in the application parameterization,
with the Euler factor at `2` removed from every zeta-core term. -/
theorem massLocalInverseProductTendsTo_unimodular_odd_zeta_removed_two_of_two_mul_add_one
    (hL : L.IsUnimodular) {m : ℕ} (hn : n = 2 * m + 1) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        (Finset.Icc 1 m).prod
          (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
            (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))))) := by
  simpa [prod_goodPrimeEulerCoreZetaTailFactor_two] using
    massLocalInverseProductTendsTo_unimodular_odd_zeta_of_two_mul_add_one
      (L := L) hL hn

/-- In even rank `n = 2*m`, the discriminant used by the good-prime
even-rank character is `(-1)^m * 2^(2*m)` for a classically unimodular
lattice. -/
theorem goodPrimeEvenCharacterDiscriminant_eq_neg_one_pow_mul_two_pow
    (hL : L.IsUnimodular) {m : ℕ} (hn : n = 2 * m) :
    goodPrimeEvenCharacterDiscriminant L m = (-1 : ℤ)^m * (2 : ℤ)^(2 * m) := by
  rw [goodPrimeEvenCharacterDiscriminant,
    L.polarDeterminant_eq_two_pow_of_isUnimodular hL, hn]

/-- At an odd prime, the square `2^(2*m)` contributes trivially to the
unimodular even-rank good-prime character. -/
theorem goodPrimeQuadraticCharacter_eq_jacobiSym_neg_one_pow_of_isUnimodular
    (hL : L.IsUnimodular) (p : {p : ℕ // Nat.Prime p}) (hp2 : p.1 ≠ 2)
    {m : ℕ} (hn : n = 2 * m) :
    goodPrimeQuadraticCharacter L p = jacobiSym ((-1 : ℤ)^m) p.1 := by
  rw [goodPrimeQuadraticCharacter_eq_jacobiSym_even L p m hn,
    goodPrimeEvenCharacterDiscriminant_eq_neg_one_pow_mul_two_pow hL hn,
    jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.pow_left]
  have hp_odd : Odd p.1 := p.2.odd_of_ne_two hp2
  have hgcd : (2 : ℤ).gcd p.1 = 1 := by
    rw [Int.gcd_eq_natAbs]
    norm_num
    exact hp_odd
  have hsq : jacobiSym (2 : ℤ) p.1 ^ 2 = 1 := jacobiSym.sq_one hgcd
  have hpow : jacobiSym (2 : ℤ) p.1 ^ (2 * m) = 1 := by
    rw [show jacobiSym (2 : ℤ) p.1 ^ (2 * m) =
        (jacobiSym (2 : ℤ) p.1 ^ 2) ^ m by rw [pow_mul]]
    rw [hsq, one_pow]
  rw [hpow, mul_one]

/-- If the half-rank `m` is even, the unimodular even-rank good-prime character
is trivial at odd primes. -/
theorem goodPrimeQuadraticCharacter_eq_one_of_isUnimodular_even_halfRank
    (hL : L.IsUnimodular) (p : {p : ℕ // Nat.Prime p}) (hp2 : p.1 ≠ 2)
    {m : ℕ} (hm : Even m) (hn : n = 2 * m) :
    goodPrimeQuadraticCharacter L p = 1 := by
  rw [goodPrimeQuadraticCharacter_eq_jacobiSym_neg_one_pow_of_isUnimodular
    hL p hp2 hn]
  have hpow : (-1 : ℤ)^m = 1 := by
    rcases hm with ⟨k, rfl⟩
    rw [← two_mul]
    rw [show (-1 : ℤ) ^ (2 * k) = ((-1 : ℤ) ^ 2) ^ k by rw [pow_mul]]
    norm_num
  simp [hpow, jacobiSym.one_left]

/-- If the half-rank `m` is odd, the unimodular even-rank good-prime character
is the mod-four character `χ_-4` at odd primes, written as `jacobiSym (-1)`. -/
theorem goodPrimeQuadraticCharacter_eq_jacobiSym_neg_one_of_isUnimodular_odd_halfRank
    (hL : L.IsUnimodular) (p : {p : ℕ // Nat.Prime p}) (hp2 : p.1 ≠ 2)
    {m : ℕ} (hm : Odd m) (hn : n = 2 * m) :
    goodPrimeQuadraticCharacter L p = jacobiSym (-1) p.1 := by
  rw [goodPrimeQuadraticCharacter_eq_jacobiSym_neg_one_pow_of_isUnimodular
    hL p hp2 hn]
  have hpow : (-1 : ℤ)^m = -1 := by
    rcases hm with ⟨k, rfl⟩
    rw [pow_succ]
    rw [show (-1 : ℤ) ^ (2 * k) = ((-1 : ℤ) ^ 2) ^ k by rw [pow_mul]]
    norm_num
  simp [hpow]

/-- Every prime in a tail after the dyadic cutoff is odd. -/
lemma ne_two_of_mem_rationalPrimesUpTo_sdiff_two {M : ℕ}
    {p : {p : ℕ // Nat.Prime p}}
    (hp : p ∈ rationalPrimesUpTo M \ rationalPrimesUpTo 2) : p.1 ≠ 2 := by
  intro hp_two
  exact (Finset.mem_sdiff.mp hp).2 <| by
    rw [mem_rationalPrimesUpTo_iff]
    omega

/-- On any finite set of odd primes, the unimodular even-rank character
product is the trivial character product when the half-rank is even. -/
theorem goodPrimeEvenCharacterInverseProduct_eq_trivial_of_isUnimodular_even_halfRank
    (hL : L.IsUnimodular) (S : Finset {p : ℕ // Nat.Prime p})
    (hS : ∀ p ∈ S, p.1 ≠ 2) {m : ℕ} (hm : Even m) (hn : n = 2 * m) :
    goodPrimeEvenCharacterInverseProduct L S m =
      S.prod fun p => (1 - (p.1 : ℝ) ^ (-(m : ℝ)))⁻¹ := by
  rw [goodPrimeEvenCharacterInverseProduct]
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [goodPrimeQuadraticCharacter_eq_one_of_isUnimodular_even_halfRank
    hL p (hS p hp) hm hn]
  simp

/-- On the dyadic-cutoff tail, the unimodular even-rank character product is
the trivial character product when the half-rank is even. -/
theorem goodPrimeEvenCharacterInverseProduct_tail_eq_trivial_of_isUnimodular_even_halfRank
    (hL : L.IsUnimodular) {M m : ℕ} (hm : Even m) (hn : n = 2 * m) :
    goodPrimeEvenCharacterInverseProduct L
        (rationalPrimesUpTo M \ rationalPrimesUpTo 2) m =
      (rationalPrimesUpTo M \ rationalPrimesUpTo 2).prod
        fun p => (1 - (p.1 : ℝ) ^ (-(m : ℝ)))⁻¹ := by
  exact goodPrimeEvenCharacterInverseProduct_eq_trivial_of_isUnimodular_even_halfRank
    (L := L) hL (rationalPrimesUpTo M \ rationalPrimesUpTo 2)
    (fun p hp => ne_two_of_mem_rationalPrimesUpTo_sdiff_two hp) hm hn

/-- On the dyadic-cutoff tail, an even half-rank unimodular character product is
literally the zeta-core product with exponent `m = 2 * (m / 2)`. -/
theorem goodPrimeEvenCharacterInverseProduct_tail_eq_zetaCore_of_isUnimodular_even_halfRank
    (hL : L.IsUnimodular) {M m : ℕ} (hm : Even m) (hn : n = 2 * m) :
    goodPrimeEvenCharacterInverseProduct L
        (rationalPrimesUpTo M \ rationalPrimesUpTo 2) m =
      goodPrimeEulerCoreInverseProduct
        (rationalPrimesUpTo M \ rationalPrimesUpTo 2) (m / 2) := by
  rw [goodPrimeEvenCharacterInverseProduct_tail_eq_trivial_of_isUnimodular_even_halfRank
    (L := L) hL hm hn]
  rw [goodPrimeEulerCoreInverseProduct]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hm_cast : (m : ℝ) = (2 : ℝ) * ((m / 2 : ℕ) : ℝ) := by
    have hm_nat : m = 2 * (m / 2) := by
      rcases hm with ⟨k, hk⟩
      subst m
      omega
    rw [hm_nat]
    norm_num
  rw [hm_cast]


/-- On any finite set of odd primes, the unimodular even-rank character
product is the `χ₋₄` product when the half-rank is odd. -/
theorem goodPrimeEvenCharacterInverseProduct_eq_chiMinusFour_of_isUnimodular_odd_halfRank
    (hL : L.IsUnimodular) (S : Finset {p : ℕ // Nat.Prime p})
    (hS : ∀ p ∈ S, p.1 ≠ 2) {m : ℕ} (hm : Odd m) (hn : n = 2 * m) :
    goodPrimeEvenCharacterInverseProduct L S m =
      S.prod fun p =>
        (1 - (jacobiSym (-1) p.1 : ℝ) * (p.1 : ℝ) ^ (-(m : ℝ)))⁻¹ := by
  rw [goodPrimeEvenCharacterInverseProduct]
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [goodPrimeQuadraticCharacter_eq_jacobiSym_neg_one_of_isUnimodular_odd_halfRank
    hL p (hS p hp) hm hn]

/-- On the dyadic-cutoff tail, the unimodular even-rank character product is
the `χ₋₄` product when the half-rank is odd. -/
theorem goodPrimeEvenCharacterInverseProduct_tail_eq_chiMinusFour_of_isUnimodular_odd_halfRank
    (hL : L.IsUnimodular) {M m : ℕ} (hm : Odd m) (hn : n = 2 * m) :
    goodPrimeEvenCharacterInverseProduct L
        (rationalPrimesUpTo M \ rationalPrimesUpTo 2) m =
      (rationalPrimesUpTo M \ rationalPrimesUpTo 2).prod fun p =>
        (1 - (jacobiSym (-1) p.1 : ℝ) * (p.1 : ℝ) ^ (-(m : ℝ)))⁻¹ := by
  exact goodPrimeEvenCharacterInverseProduct_eq_chiMinusFour_of_isUnimodular_odd_halfRank
    (L := L) hL (rationalPrimesUpTo M \ rationalPrimesUpTo 2)
    (fun p hp => ne_two_of_mem_rationalPrimesUpTo_sdiff_two hp) hm hn

/-- The lattice-free finite Euler product for the primitive mod-four character
`χ₋₄`, written in the same real inverse-factor shape as the Schulze--Pillot
even-rank good-prime product. -/
def chiMinusFourGoodPrimeInverseProduct (S : Finset {p : ℕ // Nat.Prime p}) (m : ℕ) : ℝ :=
  ∏ p ∈ S, (1 - (jacobiSym (-1) p.1 : ℝ) * (p.1 : ℝ) ^ (-(m : ℝ)))⁻¹

/-- The cutoff-tail convergence predicate for the lattice-free `χ₋₄` Euler
product.  Proving this with the closed Bernoulli/L-value is the remaining
nontrivial Dirichlet-tail special-value task. -/
def chiMinusFourGoodPrimeInverseProductTendsTo (N m : ℕ) (Pχ : ℝ) : Prop :=
  Filter.Tendsto
    (fun M : ℕ =>
      chiMinusFourGoodPrimeInverseProduct (rationalPrimesUpTo M \ rationalPrimesUpTo N) m)
    Filter.atTop
    (nhds Pχ)

/-- In odd half-rank, the unimodular non-endpoint Dirichlet tail is any limit
of the lattice-free `χ₋₄` cutoff Euler product.  This separates the
analytic special-value proof from lattice data. -/
theorem goodPrimeEvenDirichletTailFactorOfCharacter_eq_of_chiMinusFourTendsTo_isUnimodular_odd_halfRank
    (hL : L.IsUnimodular) {m : ℕ} (hm_one : 1 < m) (hm_odd : Odd m) (hn : n = 2 * m)
    {Pχ : ℝ} (hχ4 : chiMinusFourGoodPrimeInverseProductTendsTo 2 m Pχ) :
    goodPrimeEvenDirichletTailFactorOfCharacter L 2 m = Pχ := by
  have hB := massBadPrimeSet_subset_rationalPrimesUpTo_two_of_isUnimodular
    (L := L) hL
  have hχ := dirichlet_L_goodPrimeEvenCharacterInverseProductTendsTo_of_one_lt
    (L := L) 2 m hB hm_one hn
  unfold goodPrimeEvenCharacterInverseProductTendsTo at hχ
  unfold chiMinusFourGoodPrimeInverseProductTendsTo at hχ4
  have hχ4_as_character :
      Filter.Tendsto
        (fun M : ℕ =>
          goodPrimeEvenCharacterInverseProduct L
            (rationalPrimesUpTo M \ rationalPrimesUpTo 2) m)
        Filter.atTop
        (nhds Pχ) := by
    refine Filter.Tendsto.congr' ?_ hχ4
    filter_upwards with M
    exact (goodPrimeEvenCharacterInverseProduct_tail_eq_chiMinusFour_of_isUnimodular_odd_halfRank
      (L := L) hL hm_odd hn).symm
  exact tendsto_nhds_unique hχ hχ4_as_character

/-- The all-positive even-rank tail interface has the same lattice-free `χ₋₄`
limit in the odd half-rank non-endpoint range. -/
theorem goodPrimeEvenCharacterDirichletTailFactor_eq_of_chiMinusFourTendsTo_isUnimodular_odd_halfRank
    (hL : L.IsUnimodular) {m : ℕ} (hm_one : 1 < m) (hm_odd : Odd m) (hn : n = 2 * m)
    {Pχ : ℝ} (hχ4 : chiMinusFourGoodPrimeInverseProductTendsTo 2 m Pχ) :
    goodPrimeEvenCharacterDirichletTailFactor L 2 m = Pχ := by
  rw [goodPrimeEvenCharacterDirichletTailFactor, if_neg (Nat.ne_of_gt hm_one)]
  exact goodPrimeEvenDirichletTailFactorOfCharacter_eq_of_chiMinusFourTendsTo_isUnimodular_odd_halfRank
    (L := L) hL hm_one hm_odd hn hχ4

/-- The closed even-rank zeta-core and Dirichlet-character Euler products,
specialized to the dyadic cutoff forced by classical unimodularity. -/
theorem massLocalInverseProductTendsTo_unimodular_even_dirichlet
    (hL : L.IsUnimodular) {s : ℕ} (hs : 0 < s) (hn : n = 2 * s) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        ((Finset.Icc 1 (s - 1)).prod
          (fun j => goodPrimeEulerCoreZetaTailFactor 2 j) *
            goodPrimeEvenCharacterDirichletTailFactor L 2 s)) := by
  exact massLocalInverseProductTendsTo_of_goodPrimeEvenDirichletEulerProduct
    L (massBadPrimeSet_subset_rationalPrimesUpTo_two_of_isUnimodular hL) hs hn

/-- Even-rank product-limit convergence in the application parameterization
`n = 2*m`. -/
theorem massLocalInverseProductTendsTo_unimodular_even_dirichlet_of_two_mul
    (hL : L.IsUnimodular) {m : ℕ} (hm : 0 < m) (hn : n = 2 * m) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        ((Finset.Icc 1 (m - 1)).prod
          (fun j => goodPrimeEulerCoreZetaTailFactor 2 j) *
            goodPrimeEvenCharacterDirichletTailFactor L 2 m)) := by
  exact massLocalInverseProductTendsTo_unimodular_even_dirichlet
    (L := L) hL hm hn

/-- Even-rank product-limit convergence with the zeta-core part expanded by
removing the Euler factor at `2`; the Dirichlet-character tail is unchanged. -/
theorem massLocalInverseProductTendsTo_unimodular_even_dirichlet_removed_two
    (hL : L.IsUnimodular) {s : ℕ} (hs : 0 < s) (hn : n = 2 * s) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        ((Finset.Icc 1 (s - 1)).prod
          (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
            (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) *
            goodPrimeEvenCharacterDirichletTailFactor L 2 s)) := by
  simpa [prod_goodPrimeEulerCoreZetaTailFactor_two] using
    massLocalInverseProductTendsTo_unimodular_even_dirichlet
      (L := L) hL hs hn

/-- Even-rank product-limit convergence in the application parameterization,
with the zeta-core Euler factor at `2` made explicit. -/
theorem massLocalInverseProductTendsTo_unimodular_even_dirichlet_removed_two_of_two_mul
    (hL : L.IsUnimodular) {m : ℕ} (hm : 0 < m) (hn : n = 2 * m) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        ((Finset.Icc 1 (m - 1)).prod
          (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
            (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) *
            goodPrimeEvenCharacterDirichletTailFactor L 2 m)) := by
  simpa [prod_goodPrimeEulerCoreZetaTailFactor_two] using
    massLocalInverseProductTendsTo_unimodular_even_dirichlet_of_two_mul
      (L := L) hL hm hn

/-- Away from the endpoint `s = 1`, the even-rank product limit may be stated
with the explicit non-endpoint Dirichlet-character tail. -/
theorem massLocalInverseProductTendsTo_unimodular_even_dirichlet_one_lt
    (hL : L.IsUnimodular) {s : ℕ} (hs : 1 < s) (hn : n = 2 * s) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        ((Finset.Icc 1 (s - 1)).prod
          (fun j => goodPrimeEulerCoreZetaTailFactor 2 j) *
            goodPrimeEvenDirichletTailFactorOfCharacter L 2 s)) := by
  exact massLocalInverseProductTendsTo_of_goodPrimeEvenDirichletEulerProduct_one_lt
    L (massBadPrimeSet_subset_rationalPrimesUpTo_two_of_isUnimodular hL) hs hn

/-- Non-endpoint even-rank convergence in the application parameterization
`n = 2*m`. -/
theorem massLocalInverseProductTendsTo_unimodular_even_dirichlet_one_lt_of_two_mul
    (hL : L.IsUnimodular) {m : ℕ} (hm : 1 < m) (hn : n = 2 * m) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        ((Finset.Icc 1 (m - 1)).prod
          (fun j => goodPrimeEulerCoreZetaTailFactor 2 j) *
            goodPrimeEvenDirichletTailFactorOfCharacter L 2 m)) := by
  exact massLocalInverseProductTendsTo_unimodular_even_dirichlet_one_lt
    (L := L) hL hm hn

/-- Non-endpoint even-rank convergence with the zeta-core Euler factor at `2`
made explicit. -/
theorem massLocalInverseProductTendsTo_unimodular_even_dirichlet_one_lt_removed_two
    (hL : L.IsUnimodular) {s : ℕ} (hs : 1 < s) (hn : n = 2 * s) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        ((Finset.Icc 1 (s - 1)).prod
          (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
            (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) *
            goodPrimeEvenDirichletTailFactorOfCharacter L 2 s)) := by
  simpa [prod_goodPrimeEulerCoreZetaTailFactor_two] using
    massLocalInverseProductTendsTo_unimodular_even_dirichlet_one_lt
      (L := L) hL hs hn

/-- Non-endpoint even-rank convergence in the application parameterization,
with the zeta-core Euler factor at `2` made explicit. -/
theorem massLocalInverseProductTendsTo_unimodular_even_dirichlet_one_lt_removed_two_of_two_mul
    (hL : L.IsUnimodular) {m : ℕ} (hm : 1 < m) (hn : n = 2 * m) :
    massLocalInverseProductTendsTo L
      (massPartialPrimeInverseProduct L 2 *
        ((Finset.Icc 1 (m - 1)).prod
          (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
            (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) *
            goodPrimeEvenDirichletTailFactorOfCharacter L 2 m)) := by
  simpa [prod_goodPrimeEulerCoreZetaTailFactor_two] using
    massLocalInverseProductTendsTo_unimodular_even_dirichlet_one_lt_of_two_mul
      (L := L) hL hm hn

/-- For even half-rank, the named non-endpoint Dirichlet tail is the zeta-core
tail at exponent `m = 2 * (m / 2)`, with the Euler factor at `2` removed.  This
identifies the trivial-character branch without evaluating any nontrivial
`χ₋₄` tail. -/
theorem goodPrimeEvenDirichletTailFactorOfCharacter_eq_zetaTail_of_isUnimodular_even_halfRank
    (hL : L.IsUnimodular) {m : ℕ} (hm_one : 1 < m) (hm_even : Even m) (hn : n = 2 * m) :
    goodPrimeEvenDirichletTailFactorOfCharacter L 2 m =
      goodPrimeEulerCoreZetaTailFactor 2 (m / 2) := by
  have hB := massBadPrimeSet_subset_rationalPrimesUpTo_two_of_isUnimodular
    (L := L) hL
  have hχ := dirichlet_L_goodPrimeEvenCharacterInverseProductTendsTo_of_one_lt
    (L := L) 2 m hB hm_one hn
  have hhalf_pos : 1 ≤ m / 2 := by
    rcases hm_even with ⟨k, hk⟩
    subst m
    omega
  have hzeta := riemann_zeta_goodPrimeEulerCoreInverseProductTendsTo 2 (m / 2) hhalf_pos
  unfold goodPrimeEvenCharacterInverseProductTendsTo at hχ
  unfold goodPrimeEulerCoreInverseProductTendsTo at hzeta
  have hzeta_as_character :
      Filter.Tendsto
        (fun M : ℕ =>
          goodPrimeEvenCharacterInverseProduct L
            (rationalPrimesUpTo M \ rationalPrimesUpTo 2) m)
        Filter.atTop
        (nhds (goodPrimeEulerCoreZetaTailFactor 2 (m / 2))) := by
    refine Filter.Tendsto.congr' ?_ hzeta
    filter_upwards with M
    exact (goodPrimeEvenCharacterInverseProduct_tail_eq_zetaCore_of_isUnimodular_even_halfRank
      (L := L) hL hm_even hn).symm
  exact tendsto_nhds_unique hχ hzeta_as_character

/-- The all-positive even-rank tail interface agrees with the same zeta-core
value in the even half-rank non-endpoint range. -/
theorem goodPrimeEvenCharacterDirichletTailFactor_eq_zetaTail_of_isUnimodular_even_halfRank
    (hL : L.IsUnimodular) {m : ℕ} (hm_one : 1 < m) (hm_even : Even m) (hn : n = 2 * m) :
    goodPrimeEvenCharacterDirichletTailFactor L 2 m =
      goodPrimeEulerCoreZetaTailFactor 2 (m / 2) := by
  rw [goodPrimeEvenCharacterDirichletTailFactor, if_neg (Nat.ne_of_gt hm_one)]
  exact goodPrimeEvenDirichletTailFactorOfCharacter_eq_zetaTail_of_isUnimodular_even_halfRank
    (L := L) hL hm_one hm_even hn


end PositiveDefiniteIntegralLattice

end
