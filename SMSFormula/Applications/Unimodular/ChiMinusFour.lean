import SMSFormula.Applications.Unimodular.Constants
import SMSFormula.Applications.Unimodular.GoodPrimes
import SMSFormula.FiniteOrthogonalGroupGoodPrimeEvenPositivity
import SMSFormula.StandardAxiomsGuard
import Mathlib.NumberTheory.ZetaValues

/-!
# Chi-minus-four special-value interfaces

This file does not evaluate a dyadic density or a genus mass. It specializes
mathlib's Fourier theorem, converts the result to the existing rational
Bernoulli constants, and proves the comparison of the odd-prime Euler product
with the character series in the absolute-convergence range
(`EulerToDirichletSeries_of_one_lt`). The closed values follow both from that
comparison taken as a hypothesis and unconditionally.
-/

noncomputable section

namespace UnimodularMass.ChiMinusFour

/-! ## Existing Bernoulli polynomial convention -/

/-- Identify the repository's finite rational sum with mathlib's polynomial.
Both use the negative convention for the first Bernoulli number. -/
theorem bernoulliPolynomial_eq_eval (m : ℕ) (x : ℚ) :
    UnimodularMass.bernoulliPolynomial m x = (Polynomial.bernoulli m).eval x := by
  simp only [UnimodularMass.bernoulliPolynomial, Polynomial.bernoulli,
    Polynomial.eval_finset_sum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Reflection, transported to the existing rational definition. -/
theorem bernoulliPolynomial_one_sub (m : ℕ) (x : ℚ) :
    UnimodularMass.bernoulliPolynomial m (1 - x) =
      (-1 : ℚ) ^ m * UnimodularMass.bernoulliPolynomial m x := by
  simpa only [bernoulliPolynomial_eq_eval] using
    Polynomial.bernoulli_eval_one_sub m x

/-- The real polynomial used by mathlib's Fourier theorem at rational points. -/
theorem bernoulliFun_rat (m : ℕ) (x : ℚ) :
    bernoulliFun m (x : ℝ) =
      (UnimodularMass.bernoulliPolynomial m x : ℝ) := by
  rw [bernoulliPolynomial_eq_eval, bernoulliFun]
  have hx : (x : ℝ) = (algebraMap ℚ ℝ) x := by simp
  rw [hx, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rfl

private theorem neg_one_pow_even {m : ℕ} (hm : Even m) : (-1 : ℚ) ^ m = 1 := by
  rcases hm with ⟨k, rfl⟩
  rw [← two_mul, pow_mul]
  norm_num

private theorem neg_one_pow_odd {m : ℕ} (hm : Odd m) : (-1 : ℚ) ^ m = -1 := by
  rcases hm with ⟨k, rfl⟩
  rw [pow_succ, pow_mul]
  norm_num

/-- The generalized Bernoulli number vanishes in the wrong parity,
including the separately defined zero endpoint. -/
theorem chiMinusFourBernoulli_even {m : ℕ} (hm : Even m) :
    UnimodularMass.chiMinusFourBernoulli m = 0 := by
  have h34 : UnimodularMass.bernoulliPolynomial m (3 / 4) =
      UnimodularMass.bernoulliPolynomial m (1 / 4) := by
    calc
      _ = UnimodularMass.bernoulliPolynomial m (1 - (1 / 4 : ℚ)) := by norm_num
      _ = (-1 : ℚ) ^ m * UnimodularMass.bernoulliPolynomial m (1 / 4) :=
        bernoulliPolynomial_one_sub m (1 / 4)
      _ = _ := by rw [neg_one_pow_even hm, one_mul]
  by_cases hm0 : m = 0
  · simp [hm0]
  · rw [UnimodularMass.chiMinusFourBernoulli, if_neg hm0, h34]
    ring

/-- The factor of two from reflection is essential in the odd branch. -/
theorem chiMinusFourBernoulli_eq_quarter {m : ℕ} (hm : Odd m) :
    UnimodularMass.chiMinusFourBernoulli m =
      2 * (4 : ℚ) ^ (m - 1) * UnimodularMass.bernoulliPolynomial m (1 / 4) := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, hk⟩
    omega
  have h34 : UnimodularMass.bernoulliPolynomial m (3 / 4) =
      -UnimodularMass.bernoulliPolynomial m (1 / 4) := by
    calc
      _ = UnimodularMass.bernoulliPolynomial m (1 - (1 / 4 : ℚ)) := by norm_num
      _ = (-1 : ℚ) ^ m * UnimodularMass.bernoulliPolynomial m (1 / 4) :=
        bernoulliPolynomial_one_sub m (1 / 4)
      _ = _ := by rw [neg_one_pow_odd hm, neg_one_mul]
  rw [UnimodularMass.chiMinusFourBernoulli, if_neg hm0, h34]
  ring

/-! ## Primitive mod-four coefficients, including the even inputs -/

/-- These are series coefficients, not a new definition of a mass or local factor.
In particular the coefficient at two is zero. -/
def chi4 (n : ℕ) : ℝ :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

@[simp] theorem chi4_zero : chi4 0 = 0 := by norm_num [chi4]
@[simp] theorem chi4_one : chi4 1 = 1 := by norm_num [chi4]
@[simp] theorem chi4_two : chi4 2 = 0 := by norm_num [chi4]
@[simp] theorem chi4_three : chi4 3 = -1 := by norm_num [chi4]

@[simp] theorem chi4_add_four (n : ℕ) : chi4 (n + 4) = chi4 n := by
  simp [chi4]

/-- The primitive character has no nontrivial Euler factor at two.
This lemma says nothing about the value of the extended Jacobi symbol at two. -/
theorem chi4_euler_factor_two (m : ℕ) :
    (1 - chi4 2 * (2 : ℝ) ^ (-(m : ℝ)))⁻¹ = 1 := by
  simp

/-- The primitive mod-four character, packaged as a Mathlib `DirichletCharacter`.
This is a character interface for the existing coefficients `chi4`; it does not
change any mass or local-factor definition. -/
noncomputable def chi4DirichletCharacter : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

@[simp] theorem chi4DirichletCharacter_apply_nat (n : ℕ) :
    chi4DirichletCharacter n = ((chi4 n : ℝ) : ℂ) := by
  rw [chi4DirichletCharacter, MulChar.ringHomComp_apply]
  rw [ZMod.χ₄_nat_mod_four]
  have hlt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 4
  · norm_num [chi4, h]
  · norm_num [chi4, h]
  · simp [chi4, h]
  · simp [chi4, h]

/-- Away from two, the mod-four Dirichlet character agrees with the Jacobi
symbol formulation used by the existing real good-prime product. -/
theorem chi4DirichletCharacter_apply_prime_eq_jacobiSym_neg_one
    (p : {p : ℕ // Nat.Prime p}) (hp2 : p.1 ≠ 2) :
    chi4DirichletCharacter p.1 = ((jacobiSym (-1) p.1 : ℝ) : ℂ) := by
  rw [chi4DirichletCharacter, MulChar.ringHomComp_apply]
  have hp_odd : Odd p.1 := p.2.odd_of_ne_two hp2
  rw [jacobiSym.at_neg_one hp_odd]
  norm_cast

/-- Mathlib's Dirichlet-character Euler product for the primitive mod-four
character, in the same `(M + 1).primesBelow` cutoff notation used elsewhere in
the mass-formula product layer. -/
theorem chi4DirichletCharacter_complexEulerProduct_tendsto_LSeries
    {m : ℕ} (hm : 1 < m) :
    Filter.Tendsto
      (fun M : ℕ => (M + 1).primesBelow.prod fun p =>
        (1 - chi4DirichletCharacter p * (p : ℂ) ^ (-((m : ℕ) : ℂ)))⁻¹)
      Filter.atTop
      (nhds (LSeries (fun n : ℕ => ((chi4 n : ℝ) : ℂ)) ((m : ℕ) : ℂ))) := by
  let χ := chi4DirichletCharacter
  let z : ℂ := ((m : ℕ) : ℂ)
  have hz : 1 < z.re := by
    dsimp [z]
    norm_num
    exact_mod_cast hm
  have h := (DirichletCharacter.LSeries_eulerProduct (χ := χ) hz).comp
    (Filter.tendsto_add_atTop_nat 1)
  simpa [χ, z] using h

/-- Each real `χ₋₄` Euler factor embeds as the corresponding complex
Dirichlet-character Euler factor away from the conductor prime two. -/
theorem chiMinusFourGoodPrimeInverseFactor_ofReal
    (p : {p : ℕ // Nat.Prime p}) (hp2 : p.1 ≠ 2) (m : ℕ) :
    (((1 - (jacobiSym (-1) p.1 : ℝ) * (p.1 : ℝ) ^ (-(m : ℝ)))⁻¹ : ℝ) : ℂ) =
      (1 - chi4DirichletCharacter p.1 * (p.1 : ℂ) ^ (-((m : ℕ) : ℂ)))⁻¹ := by
  rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul]
  rw [chi4DirichletCharacter_apply_prime_eq_jacobiSym_neg_one p hp2]
  congr 2
  rw [Complex.ofReal_cpow]
  · congr 1
    norm_num
  · positivity

/-- Finite products of the repository's real odd-prime `χ₋₄` factors embed as
the complex finite Euler products for `chi4DirichletCharacter`, provided the
finite set excludes the conductor prime two. -/
theorem chiMinusFourGoodPrimeInverseProduct_ofReal
    (S : Finset {p : ℕ // Nat.Prime p}) (m : ℕ) (hS : ∀ p ∈ S, p.1 ≠ 2) :
    ((PositiveDefiniteIntegralLattice.chiMinusFourGoodPrimeInverseProduct S m : ℝ) : ℂ) =
      S.prod fun p =>
        (1 - chi4DirichletCharacter p.1 * (p.1 : ℂ) ^ (-((m : ℕ) : ℂ)))⁻¹ := by
  rw [PositiveDefiniteIntegralLattice.chiMinusFourGoodPrimeInverseProduct, Complex.ofReal_prod]
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact chiMinusFourGoodPrimeInverseFactor_ofReal p (hS p hp) m

/-- The same real-to-complex bridge after rewriting the repository prime subtype
tail as Mathlib's `Nat.primesBelow` tail. -/
theorem chiMinusFourGoodPrimeInverseProduct_tail_eq_complex_re_primesBelow_sdiff
    (M m : ℕ) :
    PositiveDefiniteIntegralLattice.chiMinusFourGoodPrimeInverseProduct
        (PositiveDefiniteIntegralLattice.rationalPrimesUpTo M \ PositiveDefiniteIntegralLattice.rationalPrimesUpTo 2) m =
      (((M + 1).primesBelow \ (2 + 1).primesBelow).prod fun p =>
        (1 - chi4DirichletCharacter p * (p : ℂ) ^ (-((m : ℕ) : ℂ)))⁻¹).re := by
  have hcast := chiMinusFourGoodPrimeInverseProduct_ofReal
    (PositiveDefiniteIntegralLattice.rationalPrimesUpTo M \ PositiveDefiniteIntegralLattice.rationalPrimesUpTo 2) m
    (fun p hp => PositiveDefiniteIntegralLattice.ne_two_of_mem_rationalPrimesUpTo_sdiff_two hp)
  have hmap :
      ((PositiveDefiniteIntegralLattice.rationalPrimesUpTo M \ PositiveDefiniteIntegralLattice.rationalPrimesUpTo 2).prod fun p =>
        (1 - chi4DirichletCharacter p.1 * (p.1 : ℂ) ^ (-((m : ℕ) : ℂ)))⁻¹) =
      (((M + 1).primesBelow \ (2 + 1).primesBelow).prod fun p =>
        (1 - chi4DirichletCharacter p * (p : ℂ) ^ (-((m : ℕ) : ℂ)))⁻¹) := by
    rw [← PositiveDefiniteIntegralLattice.rationalPrimesUpTo_sdiff_map_val_eq_primesBelow_sdiff 2 M]
    simp [Finset.prod_map, PositiveDefiniteIntegralLattice.rationalPrimeValEmbedding]
  have hre := congrArg Complex.re hcast
  rw [Complex.ofReal_re] at hre
  exact hre.trans (congrArg Complex.re hmap)

/-- Removing the dyadic Euler factor from the primitive mod-four character does
not change the complex Euler product: below `3` the only prime is `2`, and its
character value is zero. -/
theorem chi4DirichletCharacter_complexTail_tendsto_LSeries
    {m : ℕ} (hm : 1 < m) :
    Filter.Tendsto
      (fun M : ℕ => ((M + 1).primesBelow \ (2 + 1).primesBelow).prod fun p =>
        (1 - chi4DirichletCharacter p * (p : ℂ) ^ (-((m : ℕ) : ℂ)))⁻¹)
      Filter.atTop
      (nhds (LSeries (fun n : ℕ => ((chi4 n : ℝ) : ℂ)) ((m : ℕ) : ℂ))) := by
  refine Filter.Tendsto.congr' ?_ (chi4DirichletCharacter_complexEulerProduct_tendsto_LSeries hm)
  filter_upwards [Filter.eventually_ge_atTop 2] with M hM
  symm
  have hsubset : (2 + 1).primesBelow ⊆ (M + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ hM), hp.2⟩
  rw [← Finset.prod_sdiff hsubset]
  have hsmall : ((2 + 1).primesBelow.prod fun p =>
        (1 - chi4DirichletCharacter p * (p : ℂ) ^ (-((m : ℕ) : ℂ)))⁻¹) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    have hp' := Nat.mem_primesBelow.mp hp
    have hp2 : p = 2 := by
      have hp_le2 : p ≤ 2 := Nat.lt_succ_iff.mp hp'.1
      have h2le : 2 ≤ p := hp'.2.two_le
      omega
    subst p
    rw [chi4DirichletCharacter_apply_nat]
    simp
  rw [hsmall, mul_one]

/-- The Mathlib `LSeries` attached to `chi4DirichletCharacter` is the complex
embedding of the real primitive-coefficient Dirichlet series used in this file. -/
theorem chi4_LSeries_eq_tsum (m : ℕ) :
    LSeries (fun n : ℕ => ((chi4 n : ℝ) : ℂ)) ((m : ℕ) : ℂ) =
      ((∑' n : ℕ, chi4 n / (n : ℝ) ^ m : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  congr 1
  funext n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · simp [LSeries.term, hn]

private theorem sine_add_four (n : ℕ) :
    Real.sin (Real.pi * ((n + 4 : ℕ) : ℝ) / 2) =
      Real.sin (Real.pi * (n : ℝ) / 2) := by
  have hangle : Real.pi * ((n + 4 : ℕ) : ℝ) / 2 =
      Real.pi * (n : ℝ) / 2 + 2 * Real.pi := by
    push_cast
    ring
  rw [hangle, Real.sin_add_two_pi]

/-- Identify the trigonometric coefficients without a choice of character conductor. -/
theorem sine_eq_chi4 (n : ℕ) :
    Real.sin (Real.pi * (n : ℝ) / 2) = chi4 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 4
      · interval_cases n
        · norm_num [chi4]
        · norm_num [chi4]
        · norm_num [chi4]
        · have hangle : Real.pi * ((3 : ℕ) : ℝ) / 2 = Real.pi / 2 + Real.pi := by
            norm_num
            ring
          rw [hangle, Real.sin_add_pi, Real.sin_pi_div_two]
          norm_num [chi4]
      · have hlt : n - 4 < n := by omega
        have hdecomp : n - 4 + 4 = n := by omega
        calc
          _ = Real.sin (Real.pi * ((n - 4 + 4 : ℕ) : ℝ) / 2) := by rw [hdecomp]
          _ = Real.sin (Real.pi * ((n - 4 : ℕ) : ℝ) / 2) := sine_add_four (n - 4)
          _ = chi4 (n - 4) := ih (n - 4) hlt
          _ = chi4 (n - 4 + 4) := (chi4_add_four (n - 4)).symm
          _ = chi4 n := congrArg chi4 hdecomp

/-! ## Fourier evaluation; the index restriction excludes the rank-two endpoint -/

/-- The signed value obtained directly from Fourier expansion, with exponent `2*k+1`. -/
def signedValue (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k + 1) * Real.pi ^ (2 * k + 1) *
      (UnimodularMass.chiMinusFourBernoulli (2 * k + 1) : ℝ) /
    ((2 : ℝ) ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ))

/-- The desired absolute-Bernoulli value, independent of any lattice. -/
def absoluteValue (m : ℕ) : ℝ :=
  Real.pi ^ m * |(UnimodularMass.chiMinusFourBernoulli m : ℝ)| /
    ((2 : ℝ) ^ m * (m.factorial : ℝ))

/-- Convert mathlib's Fourier normalization to the repository constant. -/
theorem fourierValue_eq_signedValue (k : ℕ) :
    (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k + 1) / 2 /
        ((2 * k + 1).factorial : ℝ) * bernoulliFun (2 * k + 1) (1 / 4) =
      signedValue k := by
  have hCq : UnimodularMass.chiMinusFourBernoulli (2 * k + 1) =
      2 * (4 : ℚ) ^ (2 * k) *
        UnimodularMass.bernoulliPolynomial (2 * k + 1) (1 / 4) := by
    simpa only [Nat.add_sub_cancel] using
      chiMinusFourBernoulli_eq_quarter (show Odd (2 * k + 1) from ⟨k, rfl⟩)
  have hC : (UnimodularMass.chiMinusFourBernoulli (2 * k + 1) : ℝ) =
      2 * (4 : ℝ) ^ (2 * k) *
        (UnimodularMass.bernoulliPolynomial (2 * k + 1) (1 / 4) : ℝ) := by
    exact_mod_cast hCq
  have hfour : (4 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ (2 * k)) ^ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_two]
  have htwo : (2 : ℝ) ^ (2 * k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : ((2 * k + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
  have hquarter : (1 / 4 : ℝ) = ((1 / 4 : ℚ) : ℝ) := by norm_num
  rw [hquarter, bernoulliFun_rat, signedValue, hC, mul_pow, hfour]
  simp only [pow_succ, pow_zero]
  field_simp [htwo, hfac]

/-- The sine-series formula for every odd exponent at least three. -/
theorem hasSum_sine_signed (k : ℕ) (hk : k ≠ 0) :
    HasSum
      (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k + 1) * Real.sin (Real.pi * n / 2))
      (signedValue k) := by
  rw [← fourierValue_eq_signedValue k]
  have h := hasSum_one_div_nat_pow_mul_sin hk
    (x := (1 / 4 : ℝ)) (by constructor <;> norm_num)
  convert h using 1
  funext n
  exact congrArg (fun a : ℝ => 1 / (n : ℝ) ^ (2 * k + 1) * Real.sin a) (by ring)

/-- The corresponding primitive-character Dirichlet series, not an Euler product. -/
theorem hasSum_chi4_signed (k : ℕ) (hk : k ≠ 0) :
    HasSum (fun n : ℕ => chi4 n / (n : ℝ) ^ (2 * k + 1)) (signedValue k) := by
  convert hasSum_sine_signed k hk using 1
  funext n
  rw [sine_eq_chi4]
  ring

/-- Absolute value removes the Fourier sign without assuming a Bernoulli sign theorem. -/
theorem abs_signedValue (k : ℕ) : |signedValue k| = absoluteValue (2 * k + 1) := by
  have hp : |Real.pi| = Real.pi := abs_of_pos Real.pi_pos
  have hf : |((2 * k + 1).factorial : ℝ)| = ((2 * k + 1).factorial : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  simp [signedValue, absoluteValue, abs_div, abs_mul, abs_pow, hp, hf]

theorem abs_tsum_chi4 (k : ℕ) (hk : k ≠ 0) :
    |∑' n : ℕ, chi4 n / (n : ℝ) ^ (2 * k + 1)| = absoluteValue (2 * k + 1) := by
  rw [(hasSum_chi4_signed k hk).tsum_eq, abs_signedValue]

/-! ## The Euler-product comparison -/

/-- The comparison of the real odd-prime Euler product with this explicit
character series. It holds for `1 < m` (`EulerToDirichletSeries_of_one_lt`). -/
def EulerToDirichletSeries (m : ℕ) : Prop :=
  PositiveDefiniteIntegralLattice.chiMinusFourGoodPrimeInverseProductTendsTo 2 m
    (∑' n : ℕ, chi4 n / (n : ℝ) ^ m)

/-- The lattice-free odd-prime Euler product for the primitive mod-four
character converges to the corresponding real Dirichlet series in the
absolute-convergence range: the Euler-product/Dirichlet-series comparison for
the non-endpoint exponents used in the unimodular mass application. -/
theorem EulerToDirichletSeries_of_one_lt {m : ℕ} (hm : 1 < m) :
    EulerToDirichletSeries m := by
  unfold EulerToDirichletSeries PositiveDefiniteIntegralLattice.chiMinusFourGoodPrimeInverseProductTendsTo
  have hcomplex := chi4DirichletCharacter_complexTail_tendsto_LSeries hm
  have hreal :
      Filter.Tendsto
        (fun M : ℕ => (((M + 1).primesBelow \ (2 + 1).primesBelow).prod fun p =>
          (1 - chi4DirichletCharacter p * (p : ℂ) ^ (-((m : ℕ) : ℂ)))⁻¹).re)
        Filter.atTop
        (nhds ((LSeries (fun n : ℕ => ((chi4 n : ℝ) : ℂ)) ((m : ℕ) : ℂ)).re)) := by
    exact Complex.continuous_re.tendsto _ |>.comp hcomplex
  have htarget :
      (LSeries (fun n : ℕ => ((chi4 n : ℝ) : ℂ)) ((m : ℕ) : ℂ)).re =
        ∑' n : ℕ, chi4 n / (n : ℝ) ^ m := by
    rw [chi4_LSeries_eq_tsum]
    simp
  rw [htarget] at hreal
  refine Filter.Tendsto.congr' ?_ hreal
  filter_upwards with M
  exact (chiMinusFourGoodPrimeInverseProduct_tail_eq_complex_re_primesBelow_sdiff M m).symm

/-- The Euler/series comparison gives the signed closed value. -/
theorem eulerProductTendsTo_signed (k : ℕ) (hk : k ≠ 0)
    (hEuler : EulerToDirichletSeries (2 * k + 1)) :
    PositiveDefiniteIntegralLattice.chiMinusFourGoodPrimeInverseProductTendsTo 2 (2 * k + 1)
      (signedValue k) := by
  change PositiveDefiniteIntegralLattice.chiMinusFourGoodPrimeInverseProductTendsTo 2 (2 * k + 1)
    (∑' n : ℕ, chi4 n / (n : ℝ) ^ (2 * k + 1)) at hEuler
  rwa [(hasSum_chi4_signed k hk).tsum_eq] at hEuler

/-- The signed `χ₋₄` Euler-product value in the non-endpoint odd-exponent
range, now using the proved Euler-product/Dirichlet-series comparison. -/
theorem eulerProductTendsTo_signed_unconditional (k : ℕ) (hk : k ≠ 0) :
    PositiveDefiniteIntegralLattice.chiMinusFourGoodPrimeInverseProductTendsTo 2 (2 * k + 1)
      (signedValue k) := by
  exact eulerProductTendsTo_signed k hk
    (EulerToDirichletSeries_of_one_lt (by omega : 1 < 2 * k + 1))

/-- Conditional application to the existing lattice tail. Positivity is reused
from the proved good-prime layer, so no new Bernoulli-sign assumption is needed.
The only new analytic hypothesis is the explicitly named Euler/series comparison. -/
theorem lattice_tail_eq_absoluteValue
    {n k : ℕ} (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular)
    (hk : k ≠ 0) (hn : n = 2 * (2 * k + 1))
    (hEuler : EulerToDirichletSeries (2 * k + 1)) :
    PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletTailFactorOfCharacter
        L 2 (2 * k + 1) = absoluteValue (2 * k + 1) := by
  have hm : 1 < 2 * k + 1 := by omega
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have htail :=
    PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletTailFactorOfCharacter_eq_of_chiMinusFourTendsTo_isUnimodular_odd_halfRank
      (L := L) hL hm hodd hn (eulerProductTendsTo_signed k hk hEuler)
  have hpos := PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletTailFactorOfCharacter_pos
    L 2 (2 * k + 1) hm hn
  calc
    _ = |PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletTailFactorOfCharacter
        L 2 (2 * k + 1)| := (abs_of_pos hpos).symm
    _ = |signedValue k| := congrArg abs htail
    _ = absoluteValue (2 * k + 1) := abs_signedValue k

/-- Unconditional application to the existing lattice tail in the same range as
`lattice_tail_eq_absoluteValue`, using the proved `χ₋₄` Euler-product
comparison. -/
theorem lattice_tail_eq_absoluteValue_unconditional
    {n k : ℕ} (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular)
    (hk : k ≠ 0) (hn : n = 2 * (2 * k + 1)) :
    PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletTailFactorOfCharacter
        L 2 (2 * k + 1) = absoluteValue (2 * k + 1) := by
  exact lattice_tail_eq_absoluteValue L hL hk hn
    (EulerToDirichletSeries_of_one_lt (by omega : 1 < 2 * k + 1))

/-- The useful cancellation shape for the residual inverse pi-power. -/
theorem inv_pi_pow_mul_absoluteValue (m : ℕ) :
    (Real.pi ^ m)⁻¹ * absoluteValue m =
      |(UnimodularMass.chiMinusFourBernoulli m : ℝ)| /
        ((2 : ℝ) ^ m * (m.factorial : ℝ)) := by
  unfold absoluteValue
  calc
    _ = ((Real.pi ^ m)⁻¹ * Real.pi ^ m) *
        (|(UnimodularMass.chiMinusFourBernoulli m : ℝ)| /
          ((2 : ℝ) ^ m * (m.factorial : ℝ))) := by ring
    _ = _ := by
      rw [inv_mul_cancel₀ (pow_ne_zero _ Real.pi_ne_zero), one_mul]

/-- The residual real-power π factor from the even-rank zeta/archimedean layer
cancels against the χ₋₄ absolute value for every natural exponent. -/
theorem rpow_pi_neg_mul_absoluteValue (m : ℕ) :
    Real.rpow Real.pi (-(m : ℝ)) * absoluteValue m =
      |(UnimodularMass.chiMinusFourBernoulli m : ℝ)| /
        ((2 : ℝ) ^ m * (m.factorial : ℝ)) := by
  have hpow : Real.rpow Real.pi (-(m : ℝ)) = (Real.pi ^ m)⁻¹ := by
    rw [← Real.rpow_natCast Real.pi m]
    exact Real.rpow_neg Real.pi_pos.le (m : ℝ)
  rw [hpow]
  exact inv_pi_pow_mul_absoluteValue m

/-- In the odd half-rank branch, the residual `π^{-m}` factor cancels against
the proved χ₋₄ lattice tail, leaving only the rational Bernoulli/factorial
quantity. -/
theorem lattice_tail_pi_cancel_unconditional
    {n k : ℕ} (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular)
    (hk : k ≠ 0) (hn : n = 2 * (2 * k + 1)) :
    Real.rpow Real.pi (-((2 * k + 1 : ℕ) : ℝ)) *
        PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletTailFactorOfCharacter
          L 2 (2 * k + 1) =
      |(UnimodularMass.chiMinusFourBernoulli (2 * k + 1) : ℝ)| /
        ((2 : ℝ) ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ)) := by
  rw [lattice_tail_eq_absoluteValue_unconditional L hL hk hn]
  exact rpow_pi_neg_mul_absoluteValue (2 * k + 1)

/-- The χ₋₄ absolute value of the character Dirichlet-tail factor in the non-endpoint
odd half-rank branch. -/
theorem lattice_character_tail_eq_absoluteValue_unconditional
    {n k : ℕ} (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular)
    (hk : k ≠ 0) (hn : n = 2 * (2 * k + 1)) :
    PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
        L 2 (2 * k + 1) = absoluteValue (2 * k + 1) := by
  rw [PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor,
    if_neg (Nat.ne_of_gt (by omega : 1 < 2 * k + 1))]
  exact lattice_tail_eq_absoluteValue_unconditional L hL hk hn

/-- The odd half-rank χ₋₄ π cancellation for the character Dirichlet-tail factor. -/
theorem lattice_character_tail_pi_cancel_unconditional
    {n k : ℕ} (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular)
    (hk : k ≠ 0) (hn : n = 2 * (2 * k + 1)) :
    Real.rpow Real.pi (-((2 * k + 1 : ℕ) : ℝ)) *
        PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
          L 2 (2 * k + 1) =
      |(UnimodularMass.chiMinusFourBernoulli (2 * k + 1) : ℝ)| /
        ((2 : ℝ) ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ)) := by
  rw [lattice_character_tail_eq_absoluteValue_unconditional L hL hk hn]
  exact rpow_pi_neg_mul_absoluteValue (2 * k + 1)

end UnimodularMass.ChiMinusFour

end
