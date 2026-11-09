import SMSFormula.FiniteOrthogonalGroupGoodPrimeOdd

/-!
# Even-rank good-prime orthogonal orders

This downstream module converts the product-facing Jacobi value into the
literal square-class data required by the completed arbitrary-form even order
theorems.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-! ### Character target and elementary square-class transport -/

/-- The reduced determinant identifies the product-facing integer character
target with the literal finite-field target. -/
lemma goodPrime_even_characterTarget_eq
    (s : ℕ) (L : PositiveDefiniteIntegralLattice (2 * s))
    (p : {p : ℕ // Nat.Prime p}) :
    ((-1 : ZMod p.1) ^ s) * (goodPrimeGramMatrix L p).det =
      ((((-1 : ℤ) ^ s) * L.polarDeterminant : ℤ) : ZMod p.1) := by
  rw [goodPrimeGramMatrix_det_eq_polarDeterminant]
  norm_num

/-- Jacobi value one supplies an actual square root of the finite-field
character target. -/
lemma exists_sq_eq_goodPrime_even_characterTarget_of_character_eq_one
    (s : ℕ) (L : PositiveDefiniteIntegralLattice (2 * s))
    (p : {p : ℕ // Nat.Prime p})
    (hchi : goodPrimeQuadraticCharacter L p = 1) :
    ∃ t : ZMod p.1,
      t ^ 2 = ((-1 : ZMod p.1) ^ s) * (goodPrimeGramMatrix L p).det := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hj : jacobiSym (((-1 : ℤ) ^ s) * L.polarDeterminant) p.1 = 1 := by
    simpa [goodPrimeQuadraticCharacter,
      show 2 * s / 2 = s by omega] using hchi
  obtain ⟨t, ht⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  refine ⟨t, ?_⟩
  rw [goodPrime_even_characterTarget_eq]
  simpa [pow_two] using ht.symm

/-- Jacobi value negative one supplies literal nonsquareness of the
finite-field character target. -/
lemma forall_sq_ne_goodPrime_even_characterTarget_of_character_eq_neg_one
    (s : ℕ) (L : PositiveDefiniteIntegralLattice (2 * s))
    (p : {p : ℕ // Nat.Prime p})
    (hchi : goodPrimeQuadraticCharacter L p = -1) :
    ∀ t : ZMod p.1,
      t ^ 2 ≠ ((-1 : ZMod p.1) ^ s) * (goodPrimeGramMatrix L p).det := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hj : jacobiSym (((-1 : ℤ) ^ s) * L.polarDeterminant) p.1 = -1 := by
    simpa [goodPrimeQuadraticCharacter,
      show 2 * s / 2 = s by omega] using hchi
  have hnonsq :
      ¬ IsSquare (((((-1 : ℤ) ^ s) * L.polarDeterminant : ℤ) : ZMod p.1)) :=
    ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp hj
  intro t ht
  apply hnonsq
  refine ⟨t, ?_⟩
  rw [← goodPrime_even_characterTarget_eq s L p]
  simpa [pow_two] using ht.symm

/-- Odd powers of negative one give the negative target. -/
lemma neg_one_pow_mul_eq_neg_of_odd
    {K : Type*} [Ring K] {s : ℕ} (hs : Odd s) (c : K) :
    (-1 : K) ^ s * c = -c := by
  obtain ⟨r, rfl⟩ := hs
  simp [pow_add]

/-- Even powers of negative one leave the target unchanged. -/
lemma neg_one_pow_mul_eq_of_even
    {K : Type*} [Ring K] {s : ℕ} (hs : Even s) (c : K) :
    (-1 : K) ^ s * c = c := by
  obtain ⟨r, rfl⟩ := hs
  have hsq : (-1 : K) ^ r * (-1 : K) ^ r = 1 := by
    rw [← pow_add, show r + r = 2 * r by omega, pow_mul]
    simp
  rw [pow_add, hsq, one_mul]

/-- If negative one is square, square status is unchanged by negation. -/
lemma exists_sq_eq_neg_iff_of_neg_one_square
    {K : Type*} [Field K] (u : K) (hu : u ^ 2 = -1) (c : K) :
    (∃ t : K, t ^ 2 = -c) ↔ ∃ t : K, t ^ 2 = c := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨u * t, ?_⟩
    rw [mul_pow, hu, ht]
    ring
  · rintro ⟨t, ht⟩
    refine ⟨u * t, ?_⟩
    rw [mul_pow, hu, ht]
    ring

/-- If negative one is square, nonsquare status is likewise unchanged by
negation. -/
lemma forall_sq_ne_neg_iff_of_neg_one_square
    {K : Type*} [Field K] (u : K) (hu : u ^ 2 = -1) (c : K) :
    (∀ t : K, t ^ 2 ≠ -c) ↔ ∀ t : K, t ^ 2 ≠ c := by
  simpa only [not_exists] using
    not_congr (exists_sq_eq_neg_iff_of_neg_one_square u hu c)

/-- If negative one is nonsquare and `c` is a nonzero square, then `-c` is
nonsquare. -/
lemma forall_sq_ne_neg_of_neg_one_nonsquare_of_sq
    {K : Type*} [Field K]
    (hminus : ∀ x : K, x ^ 2 ≠ -1)
    (c : K) (hc : c ≠ 0) (t : K) (ht : t ^ 2 = c) :
    ∀ x : K, x ^ 2 ≠ -c := by
  intro x hx
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hc
    simpa [ht0] using ht.symm
  apply hminus (x / t)
  field_simp [ht0]
  rw [hx, ht]

/-! ### Closed good-prime group orders selected by the character -/

/-- Character value one selects the split closed order in every positive even
rank. -/
theorem natCard_goodPrimeFiniteGramOrthogonalGroup_even_of_character_eq_one
    (s : ℕ) (hspos : 0 < s) (L : PositiveDefiniteIntegralLattice (2 * s))
    (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L)
    (hchi : goodPrimeQuadraticCharacter L p = 1) :
    Nat.card (goodPrimeFiniteGramOrthogonalGroup L p) =
      splitEvenIdentityOrthogonalOrderExpression p.1 s := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hchar : ringChar (ZMod p.1) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact not_mem_massBadPrimeSet_ne_two L hp
  have hq : 2 ≤ Nat.card (ZMod p.1) := by
    rw [Nat.card_zmod]
    exact p.2.two_le
  have hsymm := goodPrimeGramMatrix_isSymm L p
  have hdet := goodPrimeGramMatrix_det_ne_zero L p hp
  obtain ⟨t, ht⟩ :=
    exists_sq_eq_goodPrime_even_characterTarget_of_character_eq_one s L p hchi
  change Nat.card (finiteGramOrthogonalGroup (goodPrimeGramMatrix L p)) = _
  by_cases hsodd : Odd s
  · rw [neg_one_pow_mul_eq_neg_of_odd hsodd] at ht
    by_cases hnegone : ∃ u : ZMod p.1, u ^ 2 = -1
    · obtain ⟨u, hu⟩ := hnegone
      simpa only [Nat.card_zmod] using
        natCard_evenFiniteGramOrthogonalGroup_eq_split_of_neg_one_square
          hchar hq u hu s hspos (goodPrimeGramMatrix L p) hsymm hdet t ht
    · have hminus : ∀ u : ZMod p.1, u ^ 2 ≠ -1 := by
        intro u hu
        exact hnegone ⟨u, hu⟩
      simpa only [Nat.card_zmod] using
        natCard_evenFiniteGramOrthogonalGroup_eq_split_of_neg_one_nonsquare_of_odd
          hchar hq hminus s hsodd (goodPrimeGramMatrix L p) hsymm hdet t ht
  · have hseven : Even s := Nat.not_odd_iff_even.mp hsodd
    rw [neg_one_pow_mul_eq_of_even hseven] at ht
    by_cases hnegone : ∃ u : ZMod p.1, u ^ 2 = -1
    · obtain ⟨u, hu⟩ := hnegone
      obtain ⟨tneg, htneg⟩ :=
        (exists_sq_eq_neg_iff_of_neg_one_square u hu
          (goodPrimeGramMatrix L p).det).2 ⟨t, ht⟩
      simpa only [Nat.card_zmod] using
        natCard_evenFiniteGramOrthogonalGroup_eq_split_of_neg_one_square
          hchar hq u hu s hspos (goodPrimeGramMatrix L p) hsymm hdet
          tneg htneg
    · have hminus : ∀ u : ZMod p.1, u ^ 2 ≠ -1 := by
        intro u hu
        exact hnegone ⟨u, hu⟩
      have hnegdet : ∀ x : ZMod p.1,
          x ^ 2 ≠ -(goodPrimeGramMatrix L p).det :=
        forall_sq_ne_neg_of_neg_one_nonsquare_of_sq
          hminus (goodPrimeGramMatrix L p).det hdet t ht
      simpa only [Nat.card_zmod] using
        natCard_evenFiniteGramOrthogonalGroup_eq_split_of_neg_one_nonsquare_of_even
          hchar hq hminus s hspos hseven (goodPrimeGramMatrix L p)
          hsymm hdet hnegdet

/-- Character value negative one selects the nonsplit closed order in every
positive even rank. -/
theorem natCard_goodPrimeFiniteGramOrthogonalGroup_even_of_character_eq_neg_one
    (s : ℕ) (hspos : 0 < s) (L : PositiveDefiniteIntegralLattice (2 * s))
    (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L)
    (hchi : goodPrimeQuadraticCharacter L p = -1) :
    Nat.card (goodPrimeFiniteGramOrthogonalGroup L p) =
      nonsplitEvenIdentityOrthogonalOrderExpression p.1 s := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hchar : ringChar (ZMod p.1) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact not_mem_massBadPrimeSet_ne_two L hp
  have hq : 2 ≤ Nat.card (ZMod p.1) := by
    rw [Nat.card_zmod]
    exact p.2.two_le
  have hsymm := goodPrimeGramMatrix_isSymm L p
  have hdet := goodPrimeGramMatrix_det_ne_zero L p hp
  have htarget : ∀ t : ZMod p.1,
      t ^ 2 ≠ ((-1 : ZMod p.1) ^ s) * (goodPrimeGramMatrix L p).det :=
    forall_sq_ne_goodPrime_even_characterTarget_of_character_eq_neg_one
      s L p hchi
  change Nat.card (finiteGramOrthogonalGroup (goodPrimeGramMatrix L p)) = _
  by_cases hsodd : Odd s
  · rw [neg_one_pow_mul_eq_neg_of_odd hsodd] at htarget
    by_cases hnegone : ∃ u : ZMod p.1, u ^ 2 = -1
    · obtain ⟨u, hu⟩ := hnegone
      simpa only [Nat.card_zmod] using
        natCard_evenFiniteGramOrthogonalGroup_eq_nonsplit_of_neg_one_square
          hchar hq u hu s hspos (goodPrimeGramMatrix L p) hsymm hdet htarget
    · have hminus : ∀ u : ZMod p.1, u ^ 2 ≠ -1 := by
        intro u hu
        exact hnegone ⟨u, hu⟩
      simpa only [Nat.card_zmod] using
        natCard_evenFiniteGramOrthogonalGroup_eq_nonsplit_of_neg_one_nonsquare_of_odd
          hchar hq hminus s hsodd (goodPrimeGramMatrix L p)
          hsymm hdet htarget
  · have hseven : Even s := Nat.not_odd_iff_even.mp hsodd
    rw [neg_one_pow_mul_eq_of_even hseven] at htarget
    by_cases hnegone : ∃ u : ZMod p.1, u ^ 2 = -1
    · obtain ⟨u, hu⟩ := hnegone
      have hnegdet : ∀ x : ZMod p.1,
          x ^ 2 ≠ -(goodPrimeGramMatrix L p).det :=
        (forall_sq_ne_neg_iff_of_neg_one_square u hu
          (goodPrimeGramMatrix L p).det).2 htarget
      simpa only [Nat.card_zmod] using
        natCard_evenFiniteGramOrthogonalGroup_eq_nonsplit_of_neg_one_square
          hchar hq u hu s hspos (goodPrimeGramMatrix L p)
          hsymm hdet hnegdet
    · have hminus : ∀ u : ZMod p.1, u ^ 2 ≠ -1 := by
        intro u hu
        exact hnegone ⟨u, hu⟩
      obtain ⟨tneg, htneg⟩ :=
        exists_sq_eq_neg_mul_of_neg_one_nonsquare_of_nonsquare
          (goodPrimeGramMatrix L p).det hdet htarget hminus
      simpa only [Nat.card_zmod] using
        natCard_evenFiniteGramOrthogonalGroup_eq_nonsplit_of_neg_one_nonsquare_of_even
          hchar hq hminus s hspos hseven (goodPrimeGramMatrix L p)
          hsymm hdet tneg htneg

/-! ### Closed even-order normalization algebra -/

/-- The split linear factor, after extracting its power of `p`, is the
corresponding real Euler factor. -/
lemma cast_pow_sub_one_div_pow_eq_one_sub_rpow_neg
    (p : {p : ℕ // Nat.Prime p}) (s : ℕ) :
    (((p.1 ^ s - 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ s) =
      1 - (p.1 : ℝ) ^ (-(s : ℝ)) := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hp_nonneg : (0 : ℝ) ≤ p.1 := by positivity
  have hp_pow_one : 1 ≤ p.1 ^ s :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ p.2.ne_zero)
  have hrpow :
      (p.1 : ℝ) ^ (-(s : ℝ)) = ((p.1 : ℝ) ^ s)⁻¹ := by
    rw [Real.rpow_neg hp_nonneg, Real.rpow_natCast]
  rw [hrpow, Nat.cast_sub hp_pow_one]
  norm_num [Nat.cast_pow]
  field_simp [hp0]

/-- The nonsplit linear factor has the analogous plus-sign normalization. -/
lemma cast_pow_add_one_div_pow_eq_one_add_rpow_neg
    (p : {p : ℕ // Nat.Prime p}) (s : ℕ) :
    (((p.1 ^ s + 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ s) =
      1 + (p.1 : ℝ) ^ (-(s : ℝ)) := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hp_nonneg : (0 : ℝ) ≤ p.1 := by positivity
  have hrpow :
      (p.1 : ℝ) ^ (-(s : ℝ)) = ((p.1 : ℝ) ^ s)⁻¹ := by
    rw [Real.rpow_neg hp_nonneg, Real.rpow_natCast]
  rw [hrpow]
  norm_num [Nat.cast_add, Nat.cast_pow]
  field_simp [hp0]

/-- The cast split even order, divided by the good-prime normalization power,
is twice the split linear factor times the Euler core. -/
theorem cast_splitEvenOrthogonalOrderExpression_div_pow_eq
    (p : {p : ℕ // Nat.Prime p}) (s : ℕ) (hs : 0 < s) :
    (splitEvenIdentityOrthogonalOrderExpression p.1 s : ℝ) /
        (p.1 : ℝ) ^ (s * (2 * s - 1)) =
      2 * (1 - (p.1 : ℝ) ^ (-(s : ℝ))) *
        goodPrimeEulerCore p s := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one.mpr hs
  rw [← cast_finiteOrthogonalOrderEulerProduct_div_pow_eq_goodPrimeEulerCore
    p r]
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hp_pow_one : 1 ≤ p.1 ^ (r + 1) :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ p.2.ne_zero)
  have hN :
      (r + 1) * (2 * (r + 1) - 1) =
        (r + 1) * r + (r + 1) + r * (r + 1) := by
    have htwo : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
    rw [htwo]
    ring
  unfold splitEvenIdentityOrthogonalOrderExpression
  simp only [Nat.add_sub_cancel]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub hp_pow_one]
  rw [← cast_pow_sub_one_div_pow_eq_one_sub_rpow_neg p (r + 1)]
  rw [Nat.cast_sub hp_pow_one]
  rw [hN, pow_add, pow_add]
  field_simp [hp0]
  ring

/-- The cast nonsplit even order has the same Euler core and the plus-sign
linear factor. -/
theorem cast_nonsplitEvenOrthogonalOrderExpression_div_pow_eq
    (p : {p : ℕ // Nat.Prime p}) (s : ℕ) (hs : 0 < s) :
    (nonsplitEvenIdentityOrthogonalOrderExpression p.1 s : ℝ) /
        (p.1 : ℝ) ^ (s * (2 * s - 1)) =
      2 * (1 + (p.1 : ℝ) ^ (-(s : ℝ))) *
        goodPrimeEulerCore p s := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one.mpr hs
  rw [← cast_finiteOrthogonalOrderEulerProduct_div_pow_eq_goodPrimeEulerCore
    p r]
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hN :
      (r + 1) * (2 * (r + 1) - 1) =
        (r + 1) * r + (r + 1) + r * (r + 1) := by
    have htwo : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
    rw [htwo]
    ring
  unfold nonsplitEvenIdentityOrthogonalOrderExpression
  simp only [Nat.add_sub_cancel]
  rw [← cast_pow_add_one_div_pow_eq_one_add_rpow_neg p (r + 1)]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
  rw [hN, pow_add, pow_add]
  field_simp [hp0]
  ring

/-- After the factor `1/2` in the classical density convention, the split
closed order contributes exactly its linear factor times the Euler core. -/
theorem cast_half_normalized_splitEvenOrthogonalOrderExpression_eq
    (p : {p : ℕ // Nat.Prime p}) (s : ℕ) (hs : 0 < s) :
    (((1 / 2 : ℚ) *
        ((p.1 : ℚ) ^ ((2 * s) * ((2 * s) - 1) / 2))⁻¹ *
        (splitEvenIdentityOrthogonalOrderExpression p.1 s : ℚ) : ℚ) : ℝ) =
      (1 - (p.1 : ℝ) ^ (-(s : ℝ))) *
        goodPrimeEulerCore p s := by
  have hN :
      (2 * s) * (2 * s - 1) / 2 = s * (2 * s - 1) := by
    calc
      (2 * s) * (2 * s - 1) / 2 =
          (s * (2 * s - 1)) * 2 / 2 := by
            congr 1
            ring
      _ = s * (2 * s - 1) := by
        rw [Nat.mul_comm (s * (2 * s - 1)) 2]
        exact Nat.mul_div_right (s * (2 * s - 1)) (show 0 < 2 by omega)
  calc
    (((1 / 2 : ℚ) *
        ((p.1 : ℚ) ^ ((2 * s) * ((2 * s) - 1) / 2))⁻¹ *
        (splitEvenIdentityOrthogonalOrderExpression p.1 s : ℚ) : ℚ) : ℝ) =
        (1 / 2 : ℝ) *
          ((splitEvenIdentityOrthogonalOrderExpression p.1 s : ℝ) /
            (p.1 : ℝ) ^ (s * (2 * s - 1))) := by
              rw [hN]
              norm_num [Nat.cast_pow, div_eq_mul_inv]
              ring
    _ = (1 - (p.1 : ℝ) ^ (-(s : ℝ))) *
          goodPrimeEulerCore p s := by
            rw [cast_splitEvenOrthogonalOrderExpression_div_pow_eq p s hs]
            ring

/-- The nonsplit order contributes the plus-sign linear factor under the same
classical normalization. -/
theorem cast_half_normalized_nonsplitEvenOrthogonalOrderExpression_eq
    (p : {p : ℕ // Nat.Prime p}) (s : ℕ) (hs : 0 < s) :
    (((1 / 2 : ℚ) *
        ((p.1 : ℚ) ^ ((2 * s) * ((2 * s) - 1) / 2))⁻¹ *
        (nonsplitEvenIdentityOrthogonalOrderExpression p.1 s : ℚ) : ℚ) : ℝ) =
      (1 + (p.1 : ℝ) ^ (-(s : ℝ))) *
        goodPrimeEulerCore p s := by
  have hN :
      (2 * s) * (2 * s - 1) / 2 = s * (2 * s - 1) := by
    calc
      (2 * s) * (2 * s - 1) / 2 =
          (s * (2 * s - 1)) * 2 / 2 := by
            congr 1
            ring
      _ = s * (2 * s - 1) := by
        rw [Nat.mul_comm (s * (2 * s - 1)) 2]
        exact Nat.mul_div_right (s * (2 * s - 1)) (show 0 < 2 by omega)
  calc
    (((1 / 2 : ℚ) *
        ((p.1 : ℚ) ^ ((2 * s) * ((2 * s) - 1) / 2))⁻¹ *
        (nonsplitEvenIdentityOrthogonalOrderExpression p.1 s : ℚ) : ℚ) : ℝ) =
        (1 / 2 : ℝ) *
          ((nonsplitEvenIdentityOrthogonalOrderExpression p.1 s : ℝ) /
            (p.1 : ℝ) ^ (s * (2 * s - 1))) := by
              rw [hN]
              norm_num [Nat.cast_pow, div_eq_mul_inv]
              ring
    _ = (1 + (p.1 : ℝ) ^ (-(s : ℝ))) *
          goodPrimeEulerCore p s := by
            rw [cast_nonsplitEvenOrthogonalOrderExpression_div_pow_eq p s hs]
            ring

/-! ### The even good-prime factor -/

/-- In literal dimension `2s`, the normalized good-prime classical density is
the even Schulze--Pillot Euler factor. -/
theorem goodPrime_classicalSolutionCountLocalDensity_factor_even_closed
    (s : ℕ) (hs : 0 < s) (L : PositiveDefiniteIntegralLattice (2 * s))
    (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    (((1 / 2 : ℚ) * classicalSolutionCountLocalDensityAtPrime L p : ℚ) : ℝ) =
      goodPrimeEvenEulerFactor L p s := by
  have hsq : goodPrimeQuadraticCharacter L p ^ 2 = 1 :=
    goodPrimeQuadraticCharacter_sq_of_not_mem_bad_even
      L s hp rfl
  have hfactor :
      (goodPrimeQuadraticCharacter L p - 1) *
        (goodPrimeQuadraticCharacter L p + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hchi | hchi
  · have hchi' : goodPrimeQuadraticCharacter L p = 1 := by
      omega
    rw [classicalSolutionCountLocalDensityAtPrime_eq_orthogonalGroup_normalizedCard_of_goodPrime
      L p hp,
      natCard_goodPrimeFiniteGramOrthogonalGroup_even_of_character_eq_one
        s hs L p hp hchi']
    simpa [goodPrimeEvenEulerFactor, hchi', mul_comm, mul_left_comm,
      mul_assoc] using
      cast_half_normalized_splitEvenOrthogonalOrderExpression_eq p s hs
  · have hchi' : goodPrimeQuadraticCharacter L p = -1 := by
      omega
    rw [classicalSolutionCountLocalDensityAtPrime_eq_orthogonalGroup_normalizedCard_of_goodPrime
      L p hp,
      natCard_goodPrimeFiniteGramOrthogonalGroup_even_of_character_eq_neg_one
        s hs L p hp hchi']
    simpa [goodPrimeEvenEulerFactor, hchi', mul_comm, mul_left_comm,
      mul_assoc] using
      cast_half_normalized_nonsplitEvenOrthogonalOrderExpression_eq p s hs

/-- The even good-prime density factor in arbitrary rank, with a rank-equality
interface. -/
theorem goodPrime_classicalSolutionCountLocalDensity_factor_even
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) (s : ℕ) (hs : 0 < s)
    (hn : n = 2 * s) :
    (((1 / 2 : ℚ) * classicalSolutionCountLocalDensityAtPrime L p : ℚ) : ℝ) =
      goodPrimeEvenEulerFactor L p s := by
  subst n
  exact
    goodPrime_classicalSolutionCountLocalDensity_factor_even_closed
      s hs L p hp

end PositiveDefiniteIntegralLattice
