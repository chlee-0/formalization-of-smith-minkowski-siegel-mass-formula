import Mathlib

/-!
# Rational constants for unimodular mass applications

This module defines the finite rational expressions that occur on the right
side of the classical Type I and Type II unimodular mass formulas.  These
definitions are deliberately independent of `PositiveDefiniteIntegralLattice.ordinaryGenusMass`;
`totalTypeIClassMass_eq_typeIConstant` and
`totalTypeIIClassMass_eq_typeIIConstant` prove that the total class masses
equal these constants.
-/

noncomputable section

namespace UnimodularMass

/-- The finite product `P_r = ∏_{j=1}^r |B_{2j}|/(4j)`. -/
def bernoulliCore (r : ℕ) : ℚ :=
  ∏ j ∈ Finset.range r,
    |bernoulli (2 * (j + 1))| / (4 * (j + 1) : ℚ)

/-- The Bernoulli polynomial with the repository's signed convention
`B_1 = -1/2`, evaluated at a rational point. -/
def bernoulliPolynomial (m : ℕ) (x : ℚ) : ℚ :=
  ∑ a ∈ Finset.range (m + 1),
    (Nat.choose m a : ℚ) * bernoulli a * x ^ (m - a)

/-- The primitive mod-four generalized Bernoulli number
`B_{m,χ₋₄} = 4^(m-1) (B_m(1/4) - B_m(3/4))`.

The mathematical application only uses positive `m`; the value at `0` is set
to `0` so the definition remains total over `ℕ`.
-/
def chiMinusFourBernoulli (m : ℕ) : ℚ :=
  if m = 0 then 0
  else (4 : ℚ) ^ (m - 1) *
    (bernoulliPolynomial m (1 / 4) - bernoulliPolynomial m (3 / 4))

/-- The sign in the odd-rank Type I formula. -/
def typeIOddRankSign (n : ℕ) : ℚ :=
  if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1

/-- The sign in the even-rank Type I Bernoulli-number branches. -/
def typeIEvenRankSign (n : ℕ) : ℚ :=
  if n % 8 = 0 then 1 else -1

/-- Classical finite rational constant for Type I unimodular lattices.

This is only the arithmetic right-hand side.  It is not a definition of any
genus mass.
-/
def typeIConstant (n : ℕ) : ℚ :=
  if n = 0 then 0
  else if n = 1 then 1 / 2
  else
    let m := n / 2
    if n % 2 = 1 then
      ((2 : ℚ) ^ m + typeIOddRankSign n) / 2 * bernoulliCore m
    else if m % 2 = 1 then
      |chiMinusFourBernoulli m| / (4 * m : ℚ) * bernoulliCore (m - 1)
    else
      ((2 : ℚ) ^ m - 1) * ((2 : ℚ) ^ (m - 1) + typeIEvenRankSign n) /
          (4 * m : ℚ) *
        |bernoulli m| * bernoulliCore (m - 1)

/-- Classical finite rational constant for Type II unimodular lattices.

Positive ranks outside `8 ∣ n` are assigned the value `0`; proving that this is
the total mass requires a separate nonexistence theorem.
-/
def typeIIConstant (n : ℕ) : ℚ :=
  if n = 0 then 1
  else if n % 8 = 0 then
    let m := n / 2
    |bernoulli m| / (2 * m : ℚ) * bernoulliCore (m - 1)
  else 0

@[simp] theorem bernoulliCore_zero : bernoulliCore 0 = 1 := by
  simp [bernoulliCore]

/-- Product over a one-based interval after adjoining the next endpoint. -/
lemma prod_Icc_one_succ (r : ℕ) (f : ℕ → ℚ) :
    (Finset.Icc 1 (r + 1)).prod f = (Finset.Icc 1 r).prod f * f (r + 1) := by
  by_cases hr : r = 0
  · subst r
    simp
  · have hnot : r + 1 ∉ Finset.Icc 1 r := by
      simp
    have hIcc : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
      ext j
      simp
      constructor
      · intro hj
        by_cases htop : j = r + 1
        · exact Or.inl htop
        · right
          omega
      · intro hj
        rcases hj with hj | hj <;> omega
    rw [hIcc, Finset.prod_insert hnot]
    ring

/-- The Bernoulli core product written in the one-based indexing used by the
zeta-core special-value factors. -/
lemma bernoulliCore_eq_Icc (r : ℕ) :
    bernoulliCore r =
      (Finset.Icc 1 r).prod (fun j => |bernoulli (2 * j)| / (4 * j : ℚ)) := by
  induction r with
  | zero => simp [bernoulliCore]
  | succ r ih =>
      rw [bernoulliCore, Finset.prod_range_succ]
      rw [show (∏ x ∈ Finset.range r,
        |bernoulli (2 * (x + 1))| / (4 * (x + 1) : ℚ)) = bernoulliCore r by rfl]
      rw [ih]
      rw [prod_Icc_one_succ]
      norm_num [Nat.cast_add, Nat.cast_one]

/-- Real-valued form of `bernoulliCore_eq_Icc`, for matching the real analytic
product side before the final rational cast. -/
lemma bernoulliCore_real_eq_Icc (r : ℕ) :
    (bernoulliCore r : ℝ) =
      (Finset.Icc 1 r).prod
        (fun j => ((|bernoulli (2 * j)| / (4 * j : ℚ) : ℚ) : ℝ)) := by
  rw [bernoulliCore_eq_Icc]
  norm_num

/-- Conditional bridge from the signed Bernoulli factors produced by the zeta
special-value formula to the absolute Bernoulli factors in `bernoulliCore`.
The pointwise sign statement is intentionally left as an explicit hypothesis. -/
lemma signedBernoulliCore_eq_bernoulliCore_of_forall_abs (r : ℕ)
    (hB : ∀ j ∈ Finset.Icc 1 r,
      ((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j) = |bernoulli (2 * j)|) :
    (Finset.Icc 1 r).prod
        (fun j => (((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j)) / (4 * j : ℚ)) =
      bernoulliCore r := by
  rw [bernoulliCore_eq_Icc]
  refine Finset.prod_congr rfl ?_
  intro j hj
  rw [hB j hj]

/-- Real-valued conditional bridge from signed Bernoulli factors to the real
cast of `bernoulliCore`. -/
lemma signedBernoulliCore_real_eq_bernoulliCore_of_forall_abs (r : ℕ)
    (hB : ∀ j ∈ Finset.Icc 1 r,
      ((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j) = |bernoulli (2 * j)|) :
    (Finset.Icc 1 r).prod
        (fun j => (((((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j)) /
          (4 * j : ℚ) : ℚ) : ℝ)) =
      (bernoulliCore r : ℝ) := by
  rw [bernoulliCore_real_eq_Icc]
  refine Finset.prod_congr rfl ?_
  intro j hj
  rw [hB j hj]

@[simp] theorem chiMinusFourBernoulli_zero : chiMinusFourBernoulli 0 = 0 := by
  simp [chiMinusFourBernoulli]

@[simp] theorem typeIConstant_zero : typeIConstant 0 = 0 := by
  simp [typeIConstant]

@[simp] theorem typeIIConstant_zero : typeIIConstant 0 = 1 := by
  simp [typeIIConstant]

theorem bernoulli_signed_convention :
    bernoulli 1 = (-1 / 2 : ℚ) := by
  norm_num [bernoulli]

/-- The first mod-four generalized Bernoulli number in the repository's
signed convention.  This is the constant-side input for the rank-two Type I
endpoint. -/
theorem chiMinusFourBernoulli_one :
    chiMinusFourBernoulli 1 = (-1 / 2 : ℚ) := by
  norm_num [chiMinusFourBernoulli, bernoulliPolynomial, Finset.sum_range_succ,
    Nat.choose, bernoulli, bernoulli'_zero, bernoulli'_one]

theorem typeIConstant_one : typeIConstant 1 = 1 / 2 := by
  norm_num [typeIConstant]

theorem typeIIConstant_one : typeIIConstant 1 = 0 := by
  norm_num [typeIIConstant]

/-- Type I rank-two endpoint constant, matching the expected `I₂` ordinary
mass `1 / |O(I₂)| = 1 / 8`. -/
theorem typeIConstant_two : typeIConstant 2 = 1 / 8 := by
  norm_num [typeIConstant, chiMinusFourBernoulli_one]

theorem typeIIConstant_two : typeIIConstant 2 = 0 := by
  norm_num [typeIIConstant]

/-- Stable odd-rank branch of the Type I constant, in the application
parameterization `n = 2*m+1` with rank at least three. -/
lemma typeIConstant_two_mul_add_one (m : ℕ) (hm : 1 ≤ m) :
    typeIConstant (2 * m + 1) =
      ((2 : ℚ) ^ m + typeIOddRankSign (2 * m + 1)) / 2 * bernoulliCore m := by
  have hm0 : m ≠ 0 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  simp [typeIConstant, hm0, hdiv, hmod]

/-- Even-rank Type I branch with odd half-rank, the generalized-Bernoulli
branch. -/
lemma typeIConstant_even_odd_halfRank (m : ℕ) (hodd : m % 2 = 1) :
    typeIConstant (2 * m) =
      |chiMinusFourBernoulli m| / (4 * m : ℚ) * bernoulliCore (m - 1) := by
  have hne0 : 2 * m ≠ 0 := by omega
  have hne1 : 2 * m ≠ 1 := by omega
  have hdiv : (2 * m) / 2 = m := by omega
  have hmod : (2 * m) % 2 = 0 := by omega
  simp [typeIConstant, hne0, hne1, hdiv, hmod, hodd]

/-- Even-rank Type I branch with positive even half-rank. -/
lemma typeIConstant_even_even_halfRank (m : ℕ) (hm : 0 < m) (heven : m % 2 = 0) :
    typeIConstant (2 * m) =
      ((2 : ℚ) ^ m - 1) * ((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m)) /
          (4 * m : ℚ) *
        |bernoulli m| * bernoulliCore (m - 1) := by
  have hne0 : 2 * m ≠ 0 := by omega
  have hne1 : 2 * m ≠ 1 := by omega
  have hdiv : (2 * m) / 2 = m := by omega
  have hmod : (2 * m) % 2 = 0 := by omega
  simp [typeIConstant, hne0, hne1, hdiv, hmod, heven]

/-- Stable odd-rank Type I branch, stated directly in the final theorem's
rank parameter `n`. -/
lemma typeIConstant_oddRank_of_rank {n : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    typeIConstant n =
      ((2 : ℚ) ^ (n / 2) + typeIOddRankSign n) / 2 * bernoulliCore (n / 2) := by
  have hrepr : n = 2 * (n / 2) + 1 := by omega
  have hhalf : 1 ≤ n / 2 := by omega
  have hdiv : (2 * (n / 2) + 1) / 2 = n / 2 := by omega
  rw [hrepr]
  simpa [hdiv] using typeIConstant_two_mul_add_one (n / 2) hhalf

/-- A rank congruent to `1` modulo `8` is odd. -/
lemma mod_two_eq_one_of_mod_eight_eq_one {n : ℕ} (h : n % 8 = 1) :
    n % 2 = 1 := by
  omega

/-- A rank congruent to `3` modulo `8` is odd. -/
lemma mod_two_eq_one_of_mod_eight_eq_three {n : ℕ} (h : n % 8 = 3) :
    n % 2 = 1 := by
  omega

/-- A rank congruent to `5` modulo `8` is odd. -/
lemma mod_two_eq_one_of_mod_eight_eq_five {n : ℕ} (h : n % 8 = 5) :
    n % 2 = 1 := by
  omega

/-- A rank congruent to `7` modulo `8` is odd. -/
lemma mod_two_eq_one_of_mod_eight_eq_seven {n : ℕ} (h : n % 8 = 7) :
    n % 2 = 1 := by
  omega

/-- The odd Type I sign is positive in ranks `1 mod 8`. -/
lemma typeIOddRankSign_eq_one_of_mod_eight_eq_one {n : ℕ} (h : n % 8 = 1) :
    typeIOddRankSign n = 1 := by
  simp [typeIOddRankSign, h]

/-- The odd Type I sign is negative in ranks `3 mod 8`. -/
lemma typeIOddRankSign_eq_neg_one_of_mod_eight_eq_three {n : ℕ} (h : n % 8 = 3) :
    typeIOddRankSign n = -1 := by
  simp [typeIOddRankSign, h]

/-- The odd Type I sign is negative in ranks `5 mod 8`. -/
lemma typeIOddRankSign_eq_neg_one_of_mod_eight_eq_five {n : ℕ} (h : n % 8 = 5) :
    typeIOddRankSign n = -1 := by
  simp [typeIOddRankSign, h]

/-- The odd Type I sign is positive in ranks `7 mod 8`. -/
lemma typeIOddRankSign_eq_one_of_mod_eight_eq_seven {n : ℕ} (h : n % 8 = 7) :
    typeIOddRankSign n = 1 := by
  simp [typeIOddRankSign, h]

/-- Odd-rank Type I branch in ranks `1 mod 8`, with the sign simplified. -/
lemma typeIConstant_odd_mod_eight_one_of_rank {n : ℕ} (hn : 3 ≤ n) (hmod : n % 8 = 1) :
    typeIConstant n =
      ((2 : ℚ) ^ (n / 2) + 1) / 2 * bernoulliCore (n / 2) := by
  rw [typeIConstant_oddRank_of_rank hn (mod_two_eq_one_of_mod_eight_eq_one hmod)]
  rw [typeIOddRankSign_eq_one_of_mod_eight_eq_one hmod]

/-- Odd-rank Type I branch in ranks `3 mod 8`, with the sign simplified. -/
lemma typeIConstant_odd_mod_eight_three_of_rank {n : ℕ} (hn : 3 ≤ n) (hmod : n % 8 = 3) :
    typeIConstant n =
      ((2 : ℚ) ^ (n / 2) - 1) / 2 * bernoulliCore (n / 2) := by
  rw [typeIConstant_oddRank_of_rank hn (mod_two_eq_one_of_mod_eight_eq_three hmod)]
  rw [typeIOddRankSign_eq_neg_one_of_mod_eight_eq_three hmod]
  ring

/-- Odd-rank Type I branch in ranks `5 mod 8`, with the sign simplified. -/
lemma typeIConstant_odd_mod_eight_five_of_rank {n : ℕ} (hn : 3 ≤ n) (hmod : n % 8 = 5) :
    typeIConstant n =
      ((2 : ℚ) ^ (n / 2) - 1) / 2 * bernoulliCore (n / 2) := by
  rw [typeIConstant_oddRank_of_rank hn (mod_two_eq_one_of_mod_eight_eq_five hmod)]
  rw [typeIOddRankSign_eq_neg_one_of_mod_eight_eq_five hmod]
  ring

/-- Odd-rank Type I branch in ranks `7 mod 8`, with the sign simplified. -/
lemma typeIConstant_odd_mod_eight_seven_of_rank {n : ℕ} (hn : 3 ≤ n) (hmod : n % 8 = 7) :
    typeIConstant n =
      ((2 : ℚ) ^ (n / 2) + 1) / 2 * bernoulliCore (n / 2) := by
  rw [typeIConstant_oddRank_of_rank hn (mod_two_eq_one_of_mod_eight_eq_seven hmod)]
  rw [typeIOddRankSign_eq_one_of_mod_eight_eq_seven hmod]

/-- Even-rank Type I generalized-Bernoulli branch, stated directly in the
final theorem's rank parameter `n`.  This is the `n ≡ 2 mod 4` branch. -/
lemma typeIConstant_even_odd_halfRank_of_rank {n : ℕ}
    (heven : n % 2 = 0) (hoddHalf : (n / 2) % 2 = 1) :
    typeIConstant n =
      |chiMinusFourBernoulli (n / 2)| / (4 * ((n / 2 : ℕ) : ℚ)) *
        bernoulliCore (n / 2 - 1) := by
  have hrepr : n = 2 * (n / 2) := by omega
  have hdiv : (2 * (n / 2)) / 2 = n / 2 := by omega
  rw [hrepr]
  simpa [hdiv] using typeIConstant_even_odd_halfRank (m := n / 2) hoddHalf

/-- Even-rank Type I ordinary-Bernoulli branch, stated directly in the final
theorem's rank parameter `n`.  This is the positive `n ≡ 0 mod 4` branch. -/
lemma typeIConstant_even_even_halfRank_of_rank {n : ℕ}
    (hn : 0 < n) (heven : n % 2 = 0) (hevenHalf : (n / 2) % 2 = 0) :
    typeIConstant n =
      ((2 : ℚ) ^ (n / 2) - 1) *
          ((2 : ℚ) ^ (n / 2 - 1) + typeIEvenRankSign n) /
          (4 * ((n / 2 : ℕ) : ℚ)) *
        |bernoulli (n / 2)| * bernoulliCore (n / 2 - 1) := by
  have hrepr : n = 2 * (n / 2) := by omega
  have hdiv : (2 * (n / 2)) / 2 = n / 2 := by omega
  have hhalf_pos : 0 < n / 2 := by omega
  rw [hrepr]
  simpa [hdiv] using
    typeIConstant_even_even_halfRank (m := n / 2) hhalf_pos hevenHalf

/-- A rank congruent to `2` modulo `4` is even. -/
lemma mod_two_eq_zero_of_mod_four_eq_two {n : ℕ} (h : n % 4 = 2) :
    n % 2 = 0 := by
  omega

/-- If `n ≡ 2 mod 4`, then the half-rank is odd. -/
lemma halfRank_mod_two_eq_one_of_mod_four_eq_two {n : ℕ} (h : n % 4 = 2) :
    (n / 2) % 2 = 1 := by
  omega

/-- A rank divisible by `4` is even. -/
lemma mod_two_eq_zero_of_mod_four_eq_zero {n : ℕ} (h : n % 4 = 0) :
    n % 2 = 0 := by
  omega

/-- If `n ≡ 0 mod 4`, then the half-rank is even. -/
lemma halfRank_mod_two_eq_zero_of_mod_four_eq_zero {n : ℕ} (h : n % 4 = 0) :
    (n / 2) % 2 = 0 := by
  omega

/-- A rank divisible by `8` is divisible by `4`. -/
lemma mod_four_eq_zero_of_mod_eight_eq_zero {n : ℕ} (h : n % 8 = 0) :
    n % 4 = 0 := by
  omega

/-- A rank congruent to `4` modulo `8` is divisible by `4`. -/
lemma mod_four_eq_zero_of_mod_eight_eq_four {n : ℕ} (h : n % 8 = 4) :
    n % 4 = 0 := by
  omega

/-- The even Type I sign is positive in ranks `0 mod 8`. -/
lemma typeIEvenRankSign_eq_one_of_mod_eight_eq_zero {n : ℕ} (h : n % 8 = 0) :
    typeIEvenRankSign n = 1 := by
  simp [typeIEvenRankSign, h]

/-- The even Type I sign is negative in ranks `4 mod 8`. -/
lemma typeIEvenRankSign_eq_neg_one_of_mod_eight_eq_four {n : ℕ} (h : n % 8 = 4) :
    typeIEvenRankSign n = -1 := by
  simp [typeIEvenRankSign, h]

/-- The elementary odd-rank Type I sign denominator is positive in the
application range.  This lets downstream mass identities cancel the
cross-multiplied sign factor without case-splitting on `n mod 8`. -/
lemma typeIOddRankSignDen_pos (r : ℕ) (hr : 1 ≤ r) :
    0 < (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ) := by
  have hsign : typeIOddRankSign (2 * r + 1) = 1 ∨
      typeIOddRankSign (2 * r + 1) = -1 := by
    unfold typeIOddRankSign
    split_ifs <;> simp
  rcases hsign with hsign | hsign
  · rw [hsign]
    positivity
  · rw [hsign]
    norm_num [Rat.cast_pow]
    have hpow : (1 : ℝ) < 2 ^ r :=
      one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega : r ≠ 0)
    linarith

/-- The elementary even-rank Type I sign denominator is positive in the
non-endpoint even-half-rank range. -/
lemma typeIEvenRankSignDen_pos (m : ℕ) (hm : 1 < m) :
    0 < (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) := by
  have hsign : typeIEvenRankSign (2 * m) = 1 ∨
      typeIEvenRankSign (2 * m) = -1 := by
    unfold typeIEvenRankSign
    split_ifs <;> simp
  rcases hsign with hsign | hsign
  · rw [hsign]
    positivity
  · rw [hsign]
    norm_num [Rat.cast_pow]
    have hpow : (1 : ℝ) < 2 ^ (m - 1) :=
      one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega : m - 1 ≠ 0)
    linarith

/-- Even-rank Type I generalized-Bernoulli branch, stated with the final
`n ≡ 2 mod 4` hypothesis. -/
lemma typeIConstant_even_mod_four_two_of_rank {n : ℕ} (hmod : n % 4 = 2) :
    typeIConstant n =
      |chiMinusFourBernoulli (n / 2)| / (4 * ((n / 2 : ℕ) : ℚ)) *
        bernoulliCore (n / 2 - 1) := by
  exact typeIConstant_even_odd_halfRank_of_rank
    (mod_two_eq_zero_of_mod_four_eq_two hmod)
    (halfRank_mod_two_eq_one_of_mod_four_eq_two hmod)

/-- Even-rank Type I ordinary-Bernoulli branch, stated with the final positive
`n ≡ 0 mod 4` hypothesis. -/
lemma typeIConstant_even_mod_four_zero_of_rank {n : ℕ} (hn : 0 < n) (hmod : n % 4 = 0) :
    typeIConstant n =
      ((2 : ℚ) ^ (n / 2) - 1) *
          ((2 : ℚ) ^ (n / 2 - 1) + typeIEvenRankSign n) /
          (4 * ((n / 2 : ℕ) : ℚ)) *
        |bernoulli (n / 2)| * bernoulliCore (n / 2 - 1) := by
  exact typeIConstant_even_even_halfRank_of_rank hn
    (mod_two_eq_zero_of_mod_four_eq_zero hmod)
    (halfRank_mod_two_eq_zero_of_mod_four_eq_zero hmod)

/-- Type I ordinary-Bernoulli branch in ranks `0 mod 8`, with the sign
simplified. -/
lemma typeIConstant_even_mod_eight_zero_of_rank {n : ℕ} (hn : 0 < n) (hmod : n % 8 = 0) :
    typeIConstant n =
      ((2 : ℚ) ^ (n / 2) - 1) * ((2 : ℚ) ^ (n / 2 - 1) + 1) /
          (4 * ((n / 2 : ℕ) : ℚ)) *
        |bernoulli (n / 2)| * bernoulliCore (n / 2 - 1) := by
  rw [typeIConstant_even_mod_four_zero_of_rank hn
    (mod_four_eq_zero_of_mod_eight_eq_zero hmod)]
  rw [typeIEvenRankSign_eq_one_of_mod_eight_eq_zero hmod]

/-- Type I ordinary-Bernoulli branch in ranks `4 mod 8`, with the sign
simplified. -/
lemma typeIConstant_even_mod_eight_four_of_rank {n : ℕ} (hn : 0 < n) (hmod : n % 8 = 4) :
    typeIConstant n =
      ((2 : ℚ) ^ (n / 2) - 1) * ((2 : ℚ) ^ (n / 2 - 1) - 1) /
          (4 * ((n / 2 : ℕ) : ℚ)) *
        |bernoulli (n / 2)| * bernoulliCore (n / 2 - 1) := by
  rw [typeIConstant_even_mod_four_zero_of_rank hn
    (mod_four_eq_zero_of_mod_eight_eq_four hmod)]
  rw [typeIEvenRankSign_eq_neg_one_of_mod_eight_eq_four hmod]
  ring

/-- Real-valued stable odd-rank Type I branch, matching the analytic product side. -/
lemma typeIConstant_two_mul_add_one_real (m : ℕ) (hm : 1 ≤ m) :
    (typeIConstant (2 * m + 1) : ℝ) =
      (((2 : ℚ) ^ m + typeIOddRankSign (2 * m + 1)) / 2 : ℚ) *
        (bernoulliCore m : ℝ) := by
  have h := typeIConstant_two_mul_add_one m hm
  norm_num [h]

/-- Real-valued even-rank Type I generalized-Bernoulli branch. -/
lemma typeIConstant_even_odd_halfRank_real (m : ℕ) (hodd : m % 2 = 1) :
    (typeIConstant (2 * m) : ℝ) =
      |(chiMinusFourBernoulli m : ℝ)| / (4 * (m : ℝ)) *
        (bernoulliCore (m - 1) : ℝ) := by
  have h := typeIConstant_even_odd_halfRank m hodd
  norm_num [h]

/-- Real-valued even-rank Type I ordinary-Bernoulli branch. -/
lemma typeIConstant_even_even_halfRank_real
    (m : ℕ) (hm : 0 < m) (heven : m % 2 = 0) :
    (typeIConstant (2 * m) : ℝ) =
      (((2 : ℚ) ^ m - 1) * ((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m)) /
          (4 * m : ℚ) : ℚ) *
        |(bernoulli m : ℝ)| * (bernoulliCore (m - 1) : ℝ) := by
  have h := typeIConstant_even_even_halfRank m hm heven
  norm_num [h]

/-- Real-valued stable odd-rank Type I branch, stated directly in the final
theorem's rank parameter `n`. -/
lemma typeIConstant_oddRank_of_rank_real {n : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    (typeIConstant n : ℝ) =
      (((2 : ℚ) ^ (n / 2) + typeIOddRankSign n) / 2 : ℚ) *
        (bernoulliCore (n / 2) : ℝ) := by
  have h := typeIConstant_oddRank_of_rank hn hodd
  norm_num [h]

/-- Real-valued odd-rank Type I branch in ranks `1 mod 8`, with the sign
simplified. -/
lemma typeIConstant_odd_mod_eight_one_of_rank_real {n : ℕ}
    (hn : 3 ≤ n) (hmod : n % 8 = 1) :
    (typeIConstant n : ℝ) =
      (((2 : ℚ) ^ (n / 2) + 1) / 2 : ℚ) * (bernoulliCore (n / 2) : ℝ) := by
  have h := typeIConstant_odd_mod_eight_one_of_rank hn hmod
  norm_num [h]

/-- Real-valued odd-rank Type I branch in ranks `3 mod 8`, with the sign
simplified. -/
lemma typeIConstant_odd_mod_eight_three_of_rank_real {n : ℕ}
    (hn : 3 ≤ n) (hmod : n % 8 = 3) :
    (typeIConstant n : ℝ) =
      (((2 : ℚ) ^ (n / 2) - 1) / 2 : ℚ) * (bernoulliCore (n / 2) : ℝ) := by
  have h := typeIConstant_odd_mod_eight_three_of_rank hn hmod
  norm_num [h]

/-- Real-valued odd-rank Type I branch in ranks `5 mod 8`, with the sign
simplified. -/
lemma typeIConstant_odd_mod_eight_five_of_rank_real {n : ℕ}
    (hn : 3 ≤ n) (hmod : n % 8 = 5) :
    (typeIConstant n : ℝ) =
      (((2 : ℚ) ^ (n / 2) - 1) / 2 : ℚ) * (bernoulliCore (n / 2) : ℝ) := by
  have h := typeIConstant_odd_mod_eight_five_of_rank hn hmod
  norm_num [h]

/-- Real-valued odd-rank Type I branch in ranks `7 mod 8`, with the sign
simplified. -/
lemma typeIConstant_odd_mod_eight_seven_of_rank_real {n : ℕ}
    (hn : 3 ≤ n) (hmod : n % 8 = 7) :
    (typeIConstant n : ℝ) =
      (((2 : ℚ) ^ (n / 2) + 1) / 2 : ℚ) * (bernoulliCore (n / 2) : ℝ) := by
  have h := typeIConstant_odd_mod_eight_seven_of_rank hn hmod
  norm_num [h]

/-- Real-valued even-rank Type I generalized-Bernoulli branch, stated directly
in the final theorem's rank parameter `n`. -/
lemma typeIConstant_even_odd_halfRank_of_rank_real {n : ℕ}
    (heven : n % 2 = 0) (hoddHalf : (n / 2) % 2 = 1) :
    (typeIConstant n : ℝ) =
      |(chiMinusFourBernoulli (n / 2) : ℝ)| / (4 * ((n / 2 : ℕ) : ℝ)) *
        (bernoulliCore (n / 2 - 1) : ℝ) := by
  have h := typeIConstant_even_odd_halfRank_of_rank heven hoddHalf
  norm_num [h]

/-- Real-valued even-rank Type I ordinary-Bernoulli branch, stated directly in
the final theorem's rank parameter `n`. -/
lemma typeIConstant_even_even_halfRank_of_rank_real {n : ℕ}
    (hn : 0 < n) (heven : n % 2 = 0) (hevenHalf : (n / 2) % 2 = 0) :
    (typeIConstant n : ℝ) =
      (((2 : ℚ) ^ (n / 2) - 1) *
          ((2 : ℚ) ^ (n / 2 - 1) + typeIEvenRankSign n) /
          (4 * ((n / 2 : ℕ) : ℚ)) : ℚ) *
        |(bernoulli (n / 2) : ℝ)| * (bernoulliCore (n / 2 - 1) : ℝ) := by
  have h := typeIConstant_even_even_halfRank_of_rank hn heven hevenHalf
  norm_num [h]

/-- Real-valued Type I generalized-Bernoulli branch, stated with the final
`n ≡ 2 mod 4` hypothesis. -/
lemma typeIConstant_even_mod_four_two_of_rank_real {n : ℕ} (hmod : n % 4 = 2) :
    (typeIConstant n : ℝ) =
      |(chiMinusFourBernoulli (n / 2) : ℝ)| / (4 * ((n / 2 : ℕ) : ℝ)) *
        (bernoulliCore (n / 2 - 1) : ℝ) := by
  have h := typeIConstant_even_mod_four_two_of_rank hmod
  norm_num [h]

/-- Real-valued Type I ordinary-Bernoulli branch, stated with the final positive
`n ≡ 0 mod 4` hypothesis. -/
lemma typeIConstant_even_mod_four_zero_of_rank_real {n : ℕ}
    (hn : 0 < n) (hmod : n % 4 = 0) :
    (typeIConstant n : ℝ) =
      (((2 : ℚ) ^ (n / 2) - 1) *
          ((2 : ℚ) ^ (n / 2 - 1) + typeIEvenRankSign n) /
          (4 * ((n / 2 : ℕ) : ℚ)) : ℚ) *
        |(bernoulli (n / 2) : ℝ)| * (bernoulliCore (n / 2 - 1) : ℝ) := by
  have h := typeIConstant_even_mod_four_zero_of_rank hn hmod
  norm_num [h]

/-- Real-valued Type I ordinary-Bernoulli branch in ranks `0 mod 8`, with the
sign simplified. -/
lemma typeIConstant_even_mod_eight_zero_of_rank_real {n : ℕ}
    (hn : 0 < n) (hmod : n % 8 = 0) :
    (typeIConstant n : ℝ) =
      (((2 : ℚ) ^ (n / 2) - 1) * ((2 : ℚ) ^ (n / 2 - 1) + 1) /
          (4 * ((n / 2 : ℕ) : ℚ)) : ℚ) *
        |(bernoulli (n / 2) : ℝ)| * (bernoulliCore (n / 2 - 1) : ℝ) := by
  have h := typeIConstant_even_mod_eight_zero_of_rank hn hmod
  norm_num [h]

/-- Real-valued Type I ordinary-Bernoulli branch in ranks `4 mod 8`, with the
sign simplified. -/
lemma typeIConstant_even_mod_eight_four_of_rank_real {n : ℕ}
    (hn : 0 < n) (hmod : n % 8 = 4) :
    (typeIConstant n : ℝ) =
      (((2 : ℚ) ^ (n / 2) - 1) * ((2 : ℚ) ^ (n / 2 - 1) - 1) /
          (4 * ((n / 2 : ℕ) : ℚ)) : ℚ) *
        |(bernoulli (n / 2) : ℝ)| * (bernoulliCore (n / 2 - 1) : ℝ) := by
  have h := typeIConstant_even_mod_eight_four_of_rank hn hmod
  norm_num [h]

/-- Positive Type II branch, specialized to ranks `8*k`. -/
lemma typeIIConstant_eight_mul (k : ℕ) (hk : 0 < k) :
    typeIIConstant (8 * k) =
      |bernoulli (4 * k)| / (8 * k : ℚ) * bernoulliCore (4 * k - 1) := by
  have hne0 : 8 * k ≠ 0 := by omega
  have hmod : (8 * k) % 8 = 0 := by omega
  have hdiv : (8 * k) / 2 = 4 * k := by omega
  have hden : (2 * (4 * k) : ℚ) = (8 * k : ℚ) := by ring
  simp [typeIIConstant, hne0, hmod, hdiv, hden]

/-- Real-valued positive Type II branch, specialized to ranks `8*k`. -/
lemma typeIIConstant_eight_mul_real (k : ℕ) (hk : 0 < k) :
    (typeIIConstant (8 * k) : ℝ) =
      |(bernoulli (4 * k) : ℝ)| / (8 * (k : ℝ)) *
        (bernoulliCore (4 * k - 1) : ℝ) := by
  have h := typeIIConstant_eight_mul k hk
  norm_num [h]

/-- A positive natural divisible by `8` is at least `8`.  This is the
rank gate used before applying the rank-at-least-three mass theorem in the
Type II branch. -/
lemma eight_le_of_pos_dvd_eight {n : ℕ} (hn : 0 < n) (h8 : 8 ∣ n) :
    8 ≤ n := by
  rcases h8 with ⟨k, rfl⟩
  have hk : 0 < k := by omega
  omega

/-- A positive natural divisible by `8` is in the rank-at-least-three range. -/
lemma three_le_of_pos_dvd_eight {n : ℕ} (hn : 0 < n) (h8 : 8 ∣ n) :
    3 ≤ n := by
  have h8le := eight_le_of_pos_dvd_eight hn h8
  omega

/-- Positive Type II branch, stated directly with the downstream divisibility
hypothesis `8 ∣ n`. -/
lemma typeIIConstant_eq_of_pos_dvd_eight {n : ℕ} (hn : 0 < n) (h8 : 8 ∣ n) :
    typeIIConstant n =
      |bernoulli (n / 2)| / (2 * ((n / 2 : ℕ) : ℚ)) * bernoulliCore (n / 2 - 1) := by
  have hne0 : n ≠ 0 := by omega
  have hmod : n % 8 = 0 := Nat.mod_eq_zero_of_dvd h8
  simp [typeIIConstant, hne0, hmod]

/-- Positive ranks outside the `8 ∣ n` Type II branch have zero rational
constant.  This is only the arithmetic RHS convention; the geometric
nonexistence/obstruction for Type II lattices is a separate theorem. -/
lemma typeIIConstant_eq_zero_of_pos_mod_ne_zero {n : ℕ} (hn : 0 < n) (hmod : n % 8 ≠ 0) :
    typeIIConstant n = 0 := by
  have hne0 : n ≠ 0 := by omega
  simp [typeIIConstant, hne0, hmod]

/-- Positive ranks outside the `8 ∣ n` Type II branch have zero rational
constant, stated with the downstream non-divisibility hypothesis. -/
lemma typeIIConstant_eq_zero_of_pos_not_dvd_eight {n : ℕ} (hn : 0 < n) (h8 : ¬ 8 ∣ n) :
    typeIIConstant n = 0 := by
  exact typeIIConstant_eq_zero_of_pos_mod_ne_zero hn (mt Nat.dvd_of_mod_eq_zero h8)

/-- Real-valued positive Type II branch, stated directly with the downstream
divisibility hypothesis `8 ∣ n`. -/
lemma typeIIConstant_eq_of_pos_dvd_eight_real {n : ℕ} (hn : 0 < n) (h8 : 8 ∣ n) :
    (typeIIConstant n : ℝ) =
      |(bernoulli (n / 2) : ℝ)| / (2 * ((n / 2 : ℕ) : ℝ)) *
        (bernoulliCore (n / 2 - 1) : ℝ) := by
  have h := typeIIConstant_eq_of_pos_dvd_eight hn h8
  norm_num [h]

/-- Real-valued zero branch for positive Type II ranks outside `8 ∣ n`. -/
lemma typeIIConstant_eq_zero_of_pos_not_dvd_eight_real {n : ℕ}
    (hn : 0 < n) (h8 : ¬ 8 ∣ n) :
    (typeIIConstant n : ℝ) = 0 := by
  have h := typeIIConstant_eq_zero_of_pos_not_dvd_eight hn h8
  norm_num [h]

/-- General Type I/Type II ratio for the rational constants in positive ranks
`8*k`.  This is only an arithmetic check on the independently defined right-hand
sides; it does not identify either constant with a genus mass. -/
lemma typeI_typeII_ratio_eight_mul (k : ℕ) (hk : 0 < k) :
    typeIConstant (8 * k) =
      (((2 : ℚ) ^ (4 * k) - 1) * ((2 : ℚ) ^ (4 * k - 1) + 1) / 2) *
        typeIIConstant (8 * k) := by
  have hmpos : 0 < 4 * k := by omega
  have hmeven : (4 * k) % 2 = 0 := by omega
  have hI := typeIConstant_even_even_halfRank (m := 4 * k) hmpos hmeven
  have hII := typeIIConstant_eight_mul k hk
  have hrank : 2 * (4 * k) = 8 * k := by ring
  have hsign : typeIEvenRankSign (2 * (4 * k)) = 1 := by
    have hmod : (2 * (4 * k)) % 8 = 0 := by omega
    simp [typeIEvenRankSign, hmod]
  calc
    typeIConstant (8 * k) = typeIConstant (2 * (4 * k)) := by rw [hrank]
    _ = ((2 : ℚ) ^ (4 * k) - 1) * ((2 : ℚ) ^ (4 * k - 1) + 1) /
            (4 * (4 * (k : ℚ))) * |bernoulli (4 * k)| * bernoulliCore (4 * k - 1) := by
          rw [hI, hsign]
          norm_num [Nat.cast_mul]
    _ = (((2 : ℚ) ^ (4 * k) - 1) * ((2 : ℚ) ^ (4 * k - 1) + 1) / 2) *
          typeIIConstant (8 * k) := by
          rw [hII]
          have hden : (8 * k : ℚ) ≠ 0 := by positivity
          field_simp [hden]
          ring

theorem bernoulli_two : bernoulli 2 = (1 / 6 : ℚ) := by
  norm_num [bernoulli, bernoulli'_two]

theorem bernoulli_four : bernoulli 4 = (-1 / 30 : ℚ) := by
  norm_num [bernoulli, bernoulli'_four]

theorem bernoulli_six_prime : bernoulli' 6 = (1 / 42 : ℚ) := by
  have h := sum_bernoulli 7
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (show Odd 5 by norm_num) (show 1 < 5 by norm_num)] at h
  linarith

theorem bernoulli_six : bernoulli 6 = (1 / 42 : ℚ) := by
  have hrel := bernoulli'_eq_bernoulli 6
  norm_num at hrel
  rw [← hrel]
  exact bernoulli_six_prime

theorem bernoulli_eight_prime : bernoulli' 8 = (-1 / 30 : ℚ) := by
  have h := sum_bernoulli 9
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli_six_prime,
    bernoulli'_eq_zero_of_odd (show Odd 5 by norm_num) (show 1 < 5 by norm_num),
    bernoulli'_eq_zero_of_odd (show Odd 7 by norm_num) (show 1 < 7 by norm_num)] at h
  linarith

theorem bernoulli_eight : bernoulli 8 = (-1 / 30 : ℚ) := by
  have hrel := bernoulli'_eq_bernoulli 8
  norm_num at hrel
  rw [← hrel]
  exact bernoulli_eight_prime

theorem bernoulli_ten_prime : bernoulli' 10 = (5 / 66 : ℚ) := by
  have h := sum_bernoulli 11
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli, bernoulli'_zero,
    bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four,
    bernoulli_six_prime, bernoulli_eight_prime,
    bernoulli'_eq_zero_of_odd (show Odd 5 by norm_num) (show 1 < 5 by norm_num),
    bernoulli'_eq_zero_of_odd (show Odd 7 by norm_num) (show 1 < 7 by norm_num),
    bernoulli'_eq_zero_of_odd (show Odd 9 by norm_num) (show 1 < 9 by norm_num)] at h
  linarith

theorem bernoulli_ten : bernoulli 10 = (5 / 66 : ℚ) := by
  have hrel := bernoulli'_eq_bernoulli 10
  norm_num at hrel
  rw [← hrel]
  exact bernoulli_ten_prime

theorem bernoulli_twelve_prime : bernoulli' 12 = (-691 / 2730 : ℚ) := by
  have h := sum_bernoulli 13
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli, bernoulli'_zero,
    bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four,
    bernoulli_six_prime, bernoulli_eight_prime, bernoulli_ten_prime,
    bernoulli'_eq_zero_of_odd (show Odd 5 by norm_num) (show 1 < 5 by norm_num),
    bernoulli'_eq_zero_of_odd (show Odd 7 by norm_num) (show 1 < 7 by norm_num),
    bernoulli'_eq_zero_of_odd (show Odd 9 by norm_num) (show 1 < 9 by norm_num),
    bernoulli'_eq_zero_of_odd (show Odd 11 by norm_num) (show 1 < 11 by norm_num)] at h
  linarith

theorem bernoulli_twelve : bernoulli 12 = (-691 / 2730 : ℚ) := by
  have hrel := bernoulli'_eq_bernoulli 12
  norm_num at hrel
  rw [← hrel]
  exact bernoulli_twelve_prime

theorem bernoulli_fourteen_prime : bernoulli' 14 = (7 / 6 : ℚ) := by
  have h := sum_bernoulli 15
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli, bernoulli'_zero,
    bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four,
    bernoulli_six_prime, bernoulli_eight_prime, bernoulli_ten_prime,
    bernoulli_twelve_prime,
    bernoulli'_eq_zero_of_odd (show Odd 5 by norm_num) (show 1 < 5 by norm_num),
    bernoulli'_eq_zero_of_odd (show Odd 7 by norm_num) (show 1 < 7 by norm_num),
    bernoulli'_eq_zero_of_odd (show Odd 9 by norm_num) (show 1 < 9 by norm_num),
    bernoulli'_eq_zero_of_odd (show Odd 11 by norm_num) (show 1 < 11 by norm_num),
    bernoulli'_eq_zero_of_odd (show Odd 13 by norm_num) (show 1 < 13 by norm_num)] at h
  linarith

theorem bernoulli_fourteen : bernoulli 14 = (7 / 6 : ℚ) := by
  have hrel := bernoulli'_eq_bernoulli 14
  norm_num at hrel
  rw [← hrel]
  exact bernoulli_fourteen_prime

theorem chiMinusFourBernoulli_five :
    chiMinusFourBernoulli 5 = (-25 / 2 : ℚ) := by
  norm_num [chiMinusFourBernoulli, bernoulliPolynomial, Finset.sum_range_succ,
    Nat.choose, bernoulli, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (show Odd 5 by norm_num) (show 1 < 5 by norm_num)]

theorem bernoulliCore_three :
    bernoulliCore 3 = 1 / 2903040 := by
  norm_num [bernoulliCore, Finset.prod_range_succ, bernoulli, bernoulli'_two,
    bernoulli'_four, bernoulli_six_prime]

theorem bernoulliCore_four :
    bernoulliCore 4 = 1 / 1393459200 := by
  norm_num [bernoulliCore, Finset.prod_range_succ, bernoulli, bernoulli'_two,
    bernoulli'_four, bernoulli_six_prime, bernoulli_eight_prime]

theorem bernoulliCore_seven :
    bernoulliCore 7 = 691 / 578473294823424000 := by
  norm_num [bernoulliCore, Finset.prod_range_succ, bernoulli, bernoulli'_two,
    bernoulli'_four, bernoulli_six_prime, bernoulli_eight_prime,
    bernoulli_ten_prime, bernoulli_twelve_prime, bernoulli_fourteen_prime]

theorem typeIIConstant_eight :
    typeIIConstant 8 = 1 / 696729600 := by
  norm_num [typeIIConstant, bernoulliCore, Finset.prod_range_succ, bernoulli,
    bernoulli'_two, bernoulli'_four, bernoulli_six_prime]

theorem typeIConstant_eight :
    typeIConstant 8 = 1 / ((2 : ℚ) ^ 8 * (Nat.factorial 8 : ℚ)) := by
  norm_num [typeIConstant, typeIEvenRankSign, bernoulliCore, Finset.prod_range_succ,
    bernoulli, bernoulli'_two, bernoulli'_four, bernoulli_six_prime]

theorem typeIConstant_nine :
    typeIConstant 9 = 17 / 2786918400 := by
  norm_num [typeIConstant, typeIOddRankSign, bernoulliCore, Finset.prod_range_succ,
    bernoulli, bernoulli'_two, bernoulli'_four, bernoulli_six_prime,
    bernoulli_eight_prime]

theorem typeIConstant_ten :
    typeIConstant 10 = 1 / 2229534720 := by
  norm_num [typeIConstant, chiMinusFourBernoulli, bernoulliPolynomial, bernoulliCore,
    Finset.sum_range_succ, Finset.prod_range_succ, Nat.choose, bernoulli,
    bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, bernoulli_six_prime, bernoulli_eight_prime,
    bernoulli'_eq_zero_of_odd (show Odd 5 by norm_num) (show 1 < 5 by norm_num)]

theorem typeIIConstant_sixteen :
    typeIIConstant 16 = 691 / 277667181515243520000 := by
  norm_num [typeIIConstant, bernoulliCore, Finset.prod_range_succ, bernoulli,
    bernoulli'_two, bernoulli'_four, bernoulli_six_prime, bernoulli_eight_prime,
    bernoulli_ten_prime, bernoulli_twelve_prime, bernoulli_fourteen_prime]

theorem typeIConstant_sixteen :
    typeIConstant 16 = 505121 / 12340763622899712000 := by
  norm_num [typeIConstant, typeIEvenRankSign, bernoulliCore, Finset.prod_range_succ,
    bernoulli, bernoulli'_two, bernoulli'_four, bernoulli_six_prime,
    bernoulli_eight_prime, bernoulli_ten_prime, bernoulli_twelve_prime,
    bernoulli_fourteen_prime]

theorem typeI_typeII_ratio_eight :
    typeIConstant 8 / typeIIConstant 8 = 135 / 2 := by
  norm_num [typeIConstant, typeIIConstant, typeIEvenRankSign, bernoulliCore,
    Finset.prod_range_succ, bernoulli, bernoulli'_two, bernoulli'_four,
    bernoulli_six_prime]

end UnimodularMass
