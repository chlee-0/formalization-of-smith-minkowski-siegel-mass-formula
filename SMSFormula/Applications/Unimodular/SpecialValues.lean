import SMSFormula.Applications.Unimodular.Constants
import SMSFormula.Applications.Unimodular.ChiMinusFour
import SMSFormula.Applications.Unimodular.GoodPrimes

/-!
# Special-value rewrites for unimodular mass products

This module records the zeta special-value rewrite in the exact real product
shape used by the unimodular good-prime tail.  It only rewrites the full zeta
factor in the dyadic-cutoff product; it does not evaluate the native dyadic
local factor, the Dirichlet-character tail, or the final Bernoulli mass
constant.
-/

noncomputable section

namespace UnimodularMass

/-- Real form of Mathlib's even zeta-value theorem, in the coercion shape used
by the Schulze--Pillot product side. -/
lemma riemannZeta_two_mul_nat_re_eq_bernoulli_pi (j : ℕ) (hj : j ≠ 0) :
    (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re =
      ((-1 : ℝ) ^ (j + 1)) * (2 : ℝ) ^ (2 * j - 1) *
        Real.pi ^ (2 * j) * (bernoulli (2 * j) : ℝ) /
        ((Nat.factorial (2 * j) : ℕ) : ℝ) := by
  have hζ := riemannZeta_two_mul_nat (k := j) hj
  have hζ_real :
      riemannZeta (((2 * j : ℕ) : ℝ) : ℂ) =
        ((((-1 : ℝ) ^ (j + 1)) * (2 : ℝ) ^ (2 * j - 1) *
          Real.pi ^ (2 * j) * (bernoulli (2 * j) : ℝ) /
          ((Nat.factorial (2 * j) : ℕ) : ℝ) : ℝ) : ℂ) := by
    simpa [Nat.cast_mul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow]
      using hζ
  rw [hζ_real]
  exact Complex.ofReal_re _

/-- The signed even Bernoulli factor appearing in the zeta special-value formula
is positive. -/
lemma signedBernoulli_even_real_pos (j : ℕ) (hj : j ≠ 0) :
    0 < ((-1 : ℝ) ^ (j + 1)) * (bernoulli (2 * j) : ℝ) := by
  have harg : (1 : ℝ) < ((2 * j : ℕ) : ℝ) := by
    have hjge : (1 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hj) : 1 ≤ j)
    norm_num [Nat.cast_mul]
    nlinarith
  have hz_complex := riemannZeta_pos_of_one_lt harg
  have hz_re : 0 < (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re := by
    exact (Complex.lt_def.mp hz_complex).1
  rw [riemannZeta_two_mul_nat_re_eq_bernoulli_pi j hj] at hz_re
  let A : ℝ := ((-1 : ℝ) ^ (j + 1)) * (bernoulli (2 * j) : ℝ)
  let P : ℝ := (2 : ℝ) ^ (2 * j - 1) * Real.pi ^ (2 * j) /
    ((Nat.factorial (2 * j) : ℕ) : ℝ)
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hz_AP : 0 < A * P := by
    dsimp [A, P]
    convert hz_re using 1
    ring
  exact (mul_pos_iff_of_pos_right hPpos).mp hz_AP

/-- Rational form of the signed even Bernoulli positivity. -/
lemma signedBernoulli_even_pos (j : ℕ) (hj : j ≠ 0) :
    0 < ((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j) := by
  rw [← Rat.cast_pos (K := ℝ)]
  norm_num [Rat.cast_pow]
  exact signedBernoulli_even_real_pos j hj

/-- The signed even Bernoulli factor is the absolute Bernoulli factor. -/
lemma signedBernoulli_even_eq_abs (j : ℕ) (hj : j ≠ 0) :
    ((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j) = |bernoulli (2 * j)| := by
  have hpos := signedBernoulli_even_pos j hj
  have hsign : |(((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j))| =
      ((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j) := abs_of_pos hpos
  have hunit_abs : |((-1 : ℚ) ^ (j + 1))| = 1 := by
    simp
  calc
    ((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j)
        = |(((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j))| := by rw [hsign]
    _ = |((-1 : ℚ) ^ (j + 1))| * |bernoulli (2 * j)| := by rw [abs_mul]
    _ = |bernoulli (2 * j)| := by rw [hunit_abs, one_mul]

/-- Unconditional bridge from the signed Bernoulli factors produced by the zeta
special-value formula to the absolute Bernoulli factors in `bernoulliCore`. -/
lemma signedBernoulliCore_eq_bernoulliCore (r : ℕ) :
    (Finset.Icc 1 r).prod
        (fun j => (((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j)) / (4 * j : ℚ)) =
      bernoulliCore r := by
  exact signedBernoulliCore_eq_bernoulliCore_of_forall_abs r (fun j hj =>
    signedBernoulli_even_eq_abs j (by
      have hj' := (Finset.mem_Icc.mp hj).1
      omega))

/-- Real-valued identity relating the signed Bernoulli factors produced
by the zeta special-value formula to `bernoulliCore`. -/
lemma signedBernoulliCore_real_eq_bernoulliCore (r : ℕ) :
    (Finset.Icc 1 r).prod
        (fun j => (((((-1 : ℚ) ^ (j + 1)) * bernoulli (2 * j)) /
          (4 * j : ℚ) : ℚ) : ℝ)) =
      (bernoulliCore r : ℝ) := by
  exact signedBernoulliCore_real_eq_bernoulliCore_of_forall_abs r (fun j hj =>
    signedBernoulli_even_eq_abs j (by
      have hj' := (Finset.mem_Icc.mp hj).1
      omega))

/-- The dyadic-cutoff zeta-core factor after substituting the even zeta-value
formula.  The removed Euler factor at `2` remains explicit. -/
lemma zetaCoreRemovedTwo_eq_bernoulli_pi (j : ℕ) (hj : j ≠ 0) :
    (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
        (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))) =
      (((-1 : ℝ) ^ (j + 1)) * (2 : ℝ) ^ (2 * j - 1) *
        Real.pi ^ (2 * j) * (bernoulli (2 * j) : ℝ) /
        ((Nat.factorial (2 * j) : ℕ) : ℝ)) *
        (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))) := by
  rw [riemannZeta_two_mul_nat_re_eq_bernoulli_pi j hj]

/-- Product form of the even zeta-value substitution over the zeta-core part of
an odd or even unimodular good-prime tail. -/
lemma prod_zetaCoreRemovedTwo_eq_bernoulli_pi (r : ℕ) :
    (Finset.Icc 1 r).prod
        (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
          (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) =
      (Finset.Icc 1 r).prod
        (fun j => (((-1 : ℝ) ^ (j + 1)) * (2 : ℝ) ^ (2 * j - 1) *
          Real.pi ^ (2 * j) * (bernoulli (2 * j) : ℝ) /
          ((Nat.factorial (2 * j) : ℕ) : ℝ)) *
          (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) := by
  refine Finset.prod_congr rfl ?_
  intro j hj
  exact zetaCoreRemovedTwo_eq_bernoulli_pi j (by
    have hj' := (Finset.mem_Icc.mp hj).1
    omega)

/-- Algebraic simplification of the explicit Euler factor at `2` after the
zeta special value is substituted. -/
lemma two_pow_mul_removed_two_factor (j : ℕ) (hj : j ≠ 0) :
    (2 : ℝ) ^ (2 * j - 1) * (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))) =
      ((2 : ℝ) ^ (2 * j) - 1) / 2 := by
  have hcast : ((2 : ℝ) * (j : ℝ)) = ((2 * j : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hpow : (2 : ℝ) ^ (2 * j) = (2 : ℝ) ^ (2 * j - 1) * 2 := by
    have hsucc : 2 * j = (2 * j - 1) + 1 := by omega
    calc
      (2 : ℝ) ^ (2 * j) = (2 : ℝ) ^ ((2 * j - 1) + 1) := by rw [← hsucc]
      _ = (2 : ℝ) ^ (2 * j - 1) * 2 := by rw [pow_succ]
  rw [hpow]
  have hpow_ne : (2 : ℝ) ^ (2 * j - 1) * 2 ≠ 0 := by positivity
  field_simp [hpow_ne]

/-- The dyadic-cutoff zeta-core factor after both the even zeta special value
and the removed Euler factor at `2` have been simplified. -/
lemma zetaCoreRemovedTwo_eq_bernoulli_pi_dyadicFactor (j : ℕ) (hj : j ≠ 0) :
    (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
        (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))) =
      ((-1 : ℝ) ^ (j + 1)) * (((2 : ℝ) ^ (2 * j) - 1) / 2) *
        Real.pi ^ (2 * j) * (bernoulli (2 * j) : ℝ) /
        ((Nat.factorial (2 * j) : ℕ) : ℝ) := by
  rw [zetaCoreRemovedTwo_eq_bernoulli_pi j hj]
  let A : ℝ := (-1 : ℝ) ^ (j + 1)
  let B : ℝ := (2 : ℝ) ^ (2 * j - 1)
  let C : ℝ := Real.pi ^ (2 * j)
  let D : ℝ := (bernoulli (2 * j) : ℝ)
  let E : ℝ := ((Nat.factorial (2 * j) : ℕ) : ℝ)
  let R : ℝ := 1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))
  change A * B * C * D / E * R = A * (((2 : ℝ) ^ (2 * j) - 1) / 2) * C * D / E
  rw [show A * B * C * D / E * R = A * (B * R) * C * D / E by ring]
  rw [show B * R = ((2 : ℝ) ^ (2 * j) - 1) / 2 by
    dsimp [B, R]
    exact two_pow_mul_removed_two_factor j hj]

/-- One zeta-core factor rewritten as a `bernoulliCore` factor times the
remaining explicit dyadic, π and factorial contribution. -/
lemma zetaCoreRemovedTwo_eq_bernoulliCoreFactor (j : ℕ) (hj : j ≠ 0) :
    ((-1 : ℝ) ^ (j + 1)) * (((2 : ℝ) ^ (2 * j) - 1) / 2) *
        Real.pi ^ (2 * j) * (bernoulli (2 * j) : ℝ) /
        ((Nat.factorial (2 * j) : ℕ) : ℝ) =
      ((|bernoulli (2 * j)| / (4 * j : ℚ) : ℚ) : ℝ) *
        ((((2 : ℝ) ^ (2 * j) - 1) / 2) * Real.pi ^ (2 * j) *
          ((4 * j : ℚ) : ℝ) /
          ((Nat.factorial (2 * j) : ℕ) : ℝ)) := by
  have hBq := signedBernoulli_even_eq_abs j hj
  have hB : ((-1 : ℝ) ^ (j + 1)) * (bernoulli (2 * j) : ℝ) =
      ((|bernoulli (2 * j)| : ℚ) : ℝ) := by
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) hBq
    simpa [Rat.cast_mul, Rat.cast_pow, Rat.cast_abs] using hcast
  have h4j : ((4 * j : ℚ) : ℝ) ≠ 0 := by
    have hjpos : (0 : ℚ) < (j : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hj
    positivity
  have hfac : (((Nat.factorial (2 * j) : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [show ((-1 : ℝ) ^ (j + 1)) * (((2 : ℝ) ^ (2 * j) - 1) / 2) *
        Real.pi ^ (2 * j) * (bernoulli (2 * j) : ℝ) /
        ((Nat.factorial (2 * j) : ℕ) : ℝ) =
      (((-1 : ℝ) ^ (j + 1)) * (bernoulli (2 * j) : ℝ)) *
        ((((2 : ℝ) ^ (2 * j) - 1) / 2) * Real.pi ^ (2 * j)) /
        ((Nat.factorial (2 * j) : ℕ) : ℝ) by ring]
  rw [hB]
  norm_num [Rat.cast_div]
  field_simp [h4j, hfac]

/-- Product form after substituting the zeta special value and simplifying the
removed Euler factor at `2` to `(2^(2j)-1)/2`. -/
lemma prod_zetaCoreRemovedTwo_eq_bernoulli_pi_dyadicFactor (r : ℕ) :
    (Finset.Icc 1 r).prod
        (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
          (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) =
      (Finset.Icc 1 r).prod
        (fun j => ((-1 : ℝ) ^ (j + 1)) * (((2 : ℝ) ^ (2 * j) - 1) / 2) *
          Real.pi ^ (2 * j) * (bernoulli (2 * j) : ℝ) /
          ((Nat.factorial (2 * j) : ℕ) : ℝ)) := by
  refine Finset.prod_congr rfl ?_
  intro j hj
  exact zetaCoreRemovedTwo_eq_bernoulli_pi_dyadicFactor j (by
    have hj' := (Finset.mem_Icc.mp hj).1
    omega)

/-- Product form in which the Bernoulli part of the zeta-core product is the
rational `bernoulliCore`; the remaining factor is explicit. -/
lemma prod_zetaCoreRemovedTwo_eq_bernoulliCore_mul_remainder (r : ℕ) :
    (Finset.Icc 1 r).prod
        (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
          (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) =
      (bernoulliCore r : ℝ) *
        (Finset.Icc 1 r).prod
          (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) * Real.pi ^ (2 * j) *
            ((4 * j : ℚ) : ℝ) /
            ((Nat.factorial (2 * j) : ℕ) : ℝ))) := by
  rw [prod_zetaCoreRemovedTwo_eq_bernoulli_pi_dyadicFactor]
  calc
    (Finset.Icc 1 r).prod
        (fun j => ((-1 : ℝ) ^ (j + 1)) * (((2 : ℝ) ^ (2 * j) - 1) / 2) *
          Real.pi ^ (2 * j) * (bernoulli (2 * j) : ℝ) /
          ((Nat.factorial (2 * j) : ℕ) : ℝ))
        = (Finset.Icc 1 r).prod
          (fun j => ((|bernoulli (2 * j)| / (4 * j : ℚ) : ℚ) : ℝ) *
            ((((2 : ℝ) ^ (2 * j) - 1) / 2) * Real.pi ^ (2 * j) *
              ((4 * j : ℚ) : ℝ) /
              ((Nat.factorial (2 * j) : ℕ) : ℝ))) := by
            refine Finset.prod_congr rfl ?_
            intro j hj
            exact zetaCoreRemovedTwo_eq_bernoulliCoreFactor j (by
              have hj' := (Finset.mem_Icc.mp hj).1
              omega)
    _ = (Finset.Icc 1 r).prod
          (fun j => ((|bernoulli (2 * j)| / (4 * j : ℚ) : ℚ) : ℝ)) *
        (Finset.Icc 1 r).prod
          (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) * Real.pi ^ (2 * j) *
            ((4 * j : ℚ) : ℝ) /
            ((Nat.factorial (2 * j) : ℕ) : ℝ))) := by
            rw [Finset.prod_mul_distrib]
    _ = (bernoulliCore r : ℝ) *
        (Finset.Icc 1 r).prod
          (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) * Real.pi ^ (2 * j) *
            ((4 * j : ℚ) : ℝ) /
            ((Nat.factorial (2 * j) : ℕ) : ℝ))) := by
            rw [← bernoulliCore_real_eq_Icc]

/-- Sum of the exponents `2j` over the one-based zeta-core range. -/
lemma sum_Icc_one_two_mul (r : ℕ) :
    (Finset.Icc 1 r).sum (fun j => 2 * j) = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ r + 1)]
      rw [ih]
      ring

/-- Product of the π powers occurring in the zeta-core range. -/
lemma prod_Icc_one_real_pi_pow_two_mul (r : ℕ) :
    (Finset.Icc 1 r).prod (fun j => Real.pi ^ (2 * j)) =
      Real.pi ^ (r * (r + 1)) := by
  rw [Finset.prod_pow_eq_pow_sum]
  rw [sum_Icc_one_two_mul]

/-- The remaining explicit zeta-core factor splits into one total π power and a
π-free product. -/
lemma prod_zetaCoreRemainder_eq_pi_pow_mul_rational (r : ℕ) :
    (Finset.Icc 1 r).prod
          (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) * Real.pi ^ (2 * j) *
            ((4 * j : ℚ) : ℝ) /
            ((Nat.factorial (2 * j) : ℕ) : ℝ))) =
      Real.pi ^ (r * (r + 1)) *
        (Finset.Icc 1 r).prod
          (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) *
            ((4 * j : ℚ) : ℝ) /
            ((Nat.factorial (2 * j) : ℕ) : ℝ))) := by
  calc
    (Finset.Icc 1 r).prod
          (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) * Real.pi ^ (2 * j) *
            ((4 * j : ℚ) : ℝ) /
            ((Nat.factorial (2 * j) : ℕ) : ℝ)))
        = (Finset.Icc 1 r).prod
          (fun j => Real.pi ^ (2 * j) *
            ((((2 : ℝ) ^ (2 * j) - 1) / 2) *
              ((4 * j : ℚ) : ℝ) /
              ((Nat.factorial (2 * j) : ℕ) : ℝ))) := by
            refine Finset.prod_congr rfl ?_
            intro j hj
            ring
    _ = (Finset.Icc 1 r).prod (fun j => Real.pi ^ (2 * j)) *
        (Finset.Icc 1 r).prod
          (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) *
            ((4 * j : ℚ) : ℝ) /
            ((Nat.factorial (2 * j) : ℕ) : ℝ))) := by
            rw [Finset.prod_mul_distrib]
    _ = Real.pi ^ (r * (r + 1)) *
        (Finset.Icc 1 r).prod
          (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) *
            ((4 * j : ℚ) : ℝ) /
            ((Nat.factorial (2 * j) : ℕ) : ℝ))) := by
            rw [prod_Icc_one_real_pi_pow_two_mul]

/-- Zeta-core product after extracting both `bernoulliCore` and the total π
power. -/
lemma prod_zetaCoreRemovedTwo_eq_bernoulliCore_mul_pi_pow_remainder (r : ℕ) :
    (Finset.Icc 1 r).prod
        (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
          (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) =
      (bernoulliCore r : ℝ) * Real.pi ^ (r * (r + 1)) *
        (Finset.Icc 1 r).prod
          (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) *
            ((4 * j : ℚ) : ℝ) /
            ((Nat.factorial (2 * j) : ℕ) : ℝ))) := by
  rw [prod_zetaCoreRemovedTwo_eq_bernoulliCore_mul_remainder]
  rw [prod_zetaCoreRemainder_eq_pi_pow_mul_rational]
  ring

/-- Gamma at a positive integer, restated with the application namespace for
later cancellation with the zeta-value factorials. -/
lemma realGamma_nat_add_one_eq_factorial (j : ℕ) :
    Real.Gamma ((j : ℝ) + 1) = (Nat.factorial j : ℝ) := by
  exact Real.Gamma_nat_eq_factorial j

/-- Gamma at a half-integer in the finite-product shape used for the
archimedean factor. -/
lemma realGamma_nat_add_one_half_eq_factorial (j : ℕ) :
    Real.Gamma ((j : ℝ) + 1 / 2) =
      (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi /
        ((4 : ℝ) ^ j * (Nat.factorial j : ℝ)) := by
  induction j with
  | zero =>
      norm_num
      rw [Real.Gamma_one_half_eq]
  | succ j ih =>
      have harg_ne : (j : ℝ) + 1 / 2 ≠ 0 := by positivity
      have harg : (((j + 1 : ℕ) : ℝ) + 1 / 2) = ((j : ℝ) + 1 / 2) + 1 := by
        norm_num [Nat.cast_add]
        ring
      rw [harg, Real.Gamma_add_one harg_ne, ih]
      have hfac2_nat : Nat.factorial (2 * (j + 1)) =
          (2 * j + 2) * (2 * j + 1) * Nat.factorial (2 * j) := by
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega]
        rw [Nat.factorial_succ]
        rw [show 2 * j + 1 = (2 * j) + 1 by omega]
        rw [Nat.factorial_succ]
        ring
      have hfac2 : (Nat.factorial (2 * (j + 1)) : ℝ) =
          ((2 * j + 2 : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ) *
            (Nat.factorial (2 * j) : ℝ) := by
        exact_mod_cast hfac2_nat
      have hfac1 : (Nat.factorial (j + 1) : ℝ) =
          ((j + 1 : ℕ) : ℝ) * (Nat.factorial j : ℝ) := by
        rw [Nat.factorial_succ]
        norm_num
      rw [hfac2, hfac1]
      have hden : (4 : ℝ) ^ j * (Nat.factorial j : ℝ) ≠ 0 := by positivity
      have hden' :
          (4 : ℝ) ^ (j + 1) * (((j + 1 : ℕ) : ℝ) * (Nat.factorial j : ℝ)) ≠ 0 := by
        positivity
      field_simp [hden, hden']
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring

/-- The even-indexed terms in `archimedeanMassFactor` are the
half-integer Gamma values. -/
lemma realGamma_two_mul_add_one_div_two_eq_factorial (j : ℕ) :
    Real.Gamma ((((2 * j + 1 : ℕ) : ℝ) / 2)) =
      (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi /
        ((4 : ℝ) ^ j * (Nat.factorial j : ℝ)) := by
  have harg : (((2 * j + 1 : ℕ) : ℝ) / 2) = (j : ℝ) + 1 / 2 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  rw [harg, realGamma_nat_add_one_half_eq_factorial]

/-- The odd-indexed terms in `archimedeanMassFactor` are the integer
Gamma values. -/
lemma realGamma_two_mul_add_two_div_two_eq_factorial (j : ℕ) :
    Real.Gamma ((((2 * j + 2 : ℕ) : ℝ) / 2)) = (Nat.factorial j : ℝ) := by
  have harg : (((2 * j + 2 : ℕ) : ℝ) / 2) = (j : ℝ) + 1 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  rw [harg, realGamma_nat_add_one_eq_factorial]

/-- A paired half-integer/integer Gamma factor, indexed in the order occurring
in the Schulze--Pillot archimedean product. -/
lemma realGamma_pair_eq_factorial (j : ℕ) :
    Real.Gamma ((((2 * j + 1 : ℕ) : ℝ) / 2)) *
        Real.Gamma ((((2 * j + 2 : ℕ) : ℝ) / 2)) =
      (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi / (4 : ℝ) ^ j := by
  rw [realGamma_two_mul_add_one_div_two_eq_factorial,
    realGamma_two_mul_add_two_div_two_eq_factorial]
  have hfac : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hpow : (4 : ℝ) ^ j ≠ 0 := by positivity
  field_simp [hfac, hpow]

/-- Product form of the paired Gamma simplification.  This is the local
archimedean-product building block before splitting the actual range into
even and odd indices. -/
lemma prod_range_realGamma_pair_eq_factorial (r : ℕ) :
    (Finset.range r).prod (fun j =>
      Real.Gamma ((((2 * j + 1 : ℕ) : ℝ) / 2)) *
        Real.Gamma ((((2 * j + 2 : ℕ) : ℝ) / 2))) =
      (Finset.range r).prod (fun j =>
        (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi / (4 : ℝ) ^ j) := by
  refine Finset.prod_congr rfl ?_
  intro j hj
  exact realGamma_pair_eq_factorial j

/-- Split the `archimedeanMassFactor` Gamma range in even rank into
paired half-integer/integer Gamma factors. -/
lemma prod_range_even_gamma_pair (r : ℕ) :
    (Finset.range (2 * r)).prod (fun j =>
        Real.Gamma ((((j + 1 : ℕ) : ℝ) / 2))) =
      (Finset.range r).prod (fun j =>
        Real.Gamma ((((2 * j + 1 : ℕ) : ℝ) / 2)) *
          Real.Gamma ((((2 * j + 2 : ℕ) : ℝ) / 2))) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega]
      rw [Finset.prod_range_succ]
      rw [Finset.prod_range_succ]
      rw [show (Finset.range (r + 1)).prod (fun j =>
          Real.Gamma ((((2 * j + 1 : ℕ) : ℝ) / 2)) *
            Real.Gamma ((((2 * j + 2 : ℕ) : ℝ) / 2))) =
          (Finset.range r).prod (fun j =>
            Real.Gamma ((((2 * j + 1 : ℕ) : ℝ) / 2)) *
              Real.Gamma ((((2 * j + 2 : ℕ) : ℝ) / 2))) *
            (Real.Gamma ((((2 * r + 1 : ℕ) : ℝ) / 2)) *
              Real.Gamma ((((2 * r + 2 : ℕ) : ℝ) / 2))) by
        rw [Finset.prod_range_succ]]
      rw [ih]
      ring

/-- The complete Gamma range in even rank, rewritten by factorials. -/
lemma prod_range_even_gamma_eq_factorial (r : ℕ) :
    (Finset.range (2 * r)).prod (fun j =>
        Real.Gamma ((((j + 1 : ℕ) : ℝ) / 2))) =
      (Finset.range r).prod (fun j =>
        (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi / (4 : ℝ) ^ j) := by
  rw [prod_range_even_gamma_pair]
  exact prod_range_realGamma_pair_eq_factorial r

/-- The complete Gamma range in odd rank, rewritten by factorials. -/
lemma prod_range_odd_gamma_eq_factorial (r : ℕ) :
    (Finset.range (2 * r + 1)).prod (fun j =>
        Real.Gamma ((((j + 1 : ℕ) : ℝ) / 2))) =
      (Finset.range r).prod (fun j =>
        (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi / (4 : ℝ) ^ j) *
        ((Nat.factorial (2 * r) : ℝ) * Real.sqrt Real.pi /
          ((4 : ℝ) ^ r * (Nat.factorial r : ℝ))) := by
  rw [Finset.prod_range_succ]
  rw [prod_range_even_gamma_eq_factorial]
  have harg : (((2 * r + 1 : ℕ) : ℝ) / 2) = (r : ℝ) + 1 / 2 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  rw [harg, realGamma_nat_add_one_half_eq_factorial]

/-- Even-rank Schulze--Pillot archimedean factor after rewriting its Gamma
product by factorials.  The remaining π power is intentionally left visible for
later cancellation against the zeta-core π power. -/
lemma archimedeanMassFactor_even_eq_factorial_product (r : ℕ) :
    PositiveDefiniteIntegralLattice.archimedeanMassFactor (2 * r) =
      2 * Real.rpow Real.pi
        (-(((2 * r : ℕ) : ℝ) * (((2 * r : ℕ) : ℝ) + 1) / 4)) *
        (Finset.range r).prod (fun j =>
          (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi / (4 : ℝ) ^ j) := by
  unfold PositiveDefiniteIntegralLattice.archimedeanMassFactor
  rw [prod_range_even_gamma_eq_factorial]

/-- Odd-rank Schulze--Pillot archimedean factor after rewriting its Gamma
product by factorials.  The remaining π power is intentionally left visible for
later cancellation against the zeta-core π power. -/
lemma archimedeanMassFactor_odd_eq_factorial_product (r : ℕ) :
    PositiveDefiniteIntegralLattice.archimedeanMassFactor (2 * r + 1) =
      2 * Real.rpow Real.pi
        (-(((2 * r + 1 : ℕ) : ℝ) * (((2 * r + 1 : ℕ) : ℝ) + 1) / 4)) *
        ((Finset.range r).prod (fun j =>
          (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi / (4 : ℝ) ^ j) *
          ((Nat.factorial (2 * r) : ℝ) * Real.sqrt Real.pi /
            ((4 : ℝ) ^ r * (Nat.factorial r : ℝ)))) := by
  unfold PositiveDefiniteIntegralLattice.archimedeanMassFactor
  rw [prod_range_odd_gamma_eq_factorial]

/-- Product of the `4^j` denominators in the archimedean Gamma range. -/
lemma prod_range_four_pow_eq (r : ℕ) :
    (Finset.range r).prod (fun j => (4 : ℝ) ^ j) =
      (4 : ℝ) ^ (r * (r - 1) / 2) := by
  rw [Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_range_id]

/-- Extract the common `√π` and `4` powers from the paired Gamma factorial
product. -/
lemma prod_range_gamma_factorial_extract_sqrt_pi (r : ℕ) :
    (Finset.range r).prod (fun j =>
        (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi / (4 : ℝ) ^ j) =
      (Real.sqrt Real.pi) ^ r *
        (Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
          (4 : ℝ) ^ (r * (r - 1) / 2) := by
  calc
    (Finset.range r).prod (fun j =>
        (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi / (4 : ℝ) ^ j)
      = (Finset.range r).prod (fun j =>
          Real.sqrt Real.pi * (Nat.factorial (2 * j) : ℝ) / (4 : ℝ) ^ j) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          ring
    _ = ((Finset.range r).prod (fun j =>
          Real.sqrt Real.pi * (Nat.factorial (2 * j) : ℝ))) /
        ((Finset.range r).prod (fun j => (4 : ℝ) ^ j)) := by
          rw [Finset.prod_div_distrib]
    _ = ((Finset.range r).prod (fun j => Real.sqrt Real.pi) *
        (Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ))) /
        ((Finset.range r).prod (fun j => (4 : ℝ) ^ j)) := by
          rw [Finset.prod_mul_distrib]
    _ = (Real.sqrt Real.pi) ^ r *
        (Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
          (4 : ℝ) ^ (r * (r - 1) / 2) := by
          rw [Finset.prod_const, Finset.card_range, prod_range_four_pow_eq]

/-- Even-rank archimedean factor with the common `√π` and `4` powers extracted. -/
lemma archimedeanMassFactor_even_eq_extracted (r : ℕ) :
    PositiveDefiniteIntegralLattice.archimedeanMassFactor (2 * r) =
      2 * Real.rpow Real.pi
        (-(((2 * r : ℕ) : ℝ) * (((2 * r : ℕ) : ℝ) + 1) / 4)) *
        ((Real.sqrt Real.pi) ^ r *
          (Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
            (4 : ℝ) ^ (r * (r - 1) / 2)) := by
  rw [archimedeanMassFactor_even_eq_factorial_product]
  rw [prod_range_gamma_factorial_extract_sqrt_pi]

/-- Odd-rank archimedean factor with the common `√π` and `4` powers extracted
from the paired part; the final half-integer factor remains explicit. -/
lemma archimedeanMassFactor_odd_eq_extracted (r : ℕ) :
    PositiveDefiniteIntegralLattice.archimedeanMassFactor (2 * r + 1) =
      2 * Real.rpow Real.pi
        (-(((2 * r + 1 : ℕ) : ℝ) * (((2 * r + 1 : ℕ) : ℝ) + 1) / 4)) *
        (((Real.sqrt Real.pi) ^ r *
          (Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
            (4 : ℝ) ^ (r * (r - 1) / 2)) *
          ((Nat.factorial (2 * r) : ℝ) * Real.sqrt Real.pi /
            ((4 : ℝ) ^ r * (Nat.factorial r : ℝ)))) := by
  rw [archimedeanMassFactor_odd_eq_factorial_product]
  rw [prod_range_gamma_factorial_extract_sqrt_pi]

/-- The visible `√π` factor as a real power. -/
lemma sqrt_pi_eq_rpow_half :
    Real.sqrt Real.pi = Real.rpow Real.pi (1 / 2 : ℝ) := by
  exact Real.sqrt_eq_rpow Real.pi

/-- Powers of the visible `√π` factor as real powers of `π`.  This form is
used for cancellation against the `Real.rpow Real.pi` archimedean factor. -/
lemma sqrt_pi_pow_eq_rpow_half (r : ℕ) :
    (Real.sqrt Real.pi) ^ r = Real.rpow Real.pi ((r : ℝ) / 2) := by
  rw [sqrt_pi_eq_rpow_half]
  rw [← Real.rpow_natCast (Real.rpow Real.pi (1 / 2 : ℝ)) r]
  calc
    Real.rpow (Real.rpow Real.pi (1 / 2 : ℝ)) (r : ℝ)
        = Real.rpow Real.pi ((1 / 2 : ℝ) * (r : ℝ)) := by
          exact (Real.rpow_mul Real.pi_pos.le (1 / 2 : ℝ) (r : ℝ)).symm
    _ = Real.rpow Real.pi ((r : ℝ) / 2) := by
          congr 1
          ring

/-- Even powers of `√π` are integral powers of `π`. -/
lemma sqrt_pi_pow_two_mul (r : ℕ) :
    (Real.sqrt Real.pi) ^ (2 * r) = Real.pi ^ r := by
  rw [sqrt_pi_pow_eq_rpow_half]
  rw [← Real.rpow_natCast Real.pi r]
  congr 1
  norm_num

/-- Odd powers of `√π` are an integral power of `π` times one final `√π`. -/
lemma sqrt_pi_pow_two_mul_add_one (r : ℕ) :
    (Real.sqrt Real.pi) ^ (2 * r + 1) = Real.pi ^ r * Real.sqrt Real.pi := by
  rw [pow_succ']
  rw [sqrt_pi_pow_two_mul]
  ring

/-- Extract the paired Gamma product with the `√π` power rewritten as a real
power of `π`. -/
lemma prod_range_gamma_factorial_extract_pi_rpow (r : ℕ) :
    (Finset.range r).prod (fun j =>
        (Nat.factorial (2 * j) : ℝ) * Real.sqrt Real.pi / (4 : ℝ) ^ j) =
      Real.rpow Real.pi ((r : ℝ) / 2) *
        (Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
          (4 : ℝ) ^ (r * (r - 1) / 2) := by
  rw [prod_range_gamma_factorial_extract_sqrt_pi]
  rw [sqrt_pi_pow_eq_rpow_half]

/-- Even-rank archimedean factor with the extracted `√π` power rewritten as a
real power of `π`. -/
lemma archimedeanMassFactor_even_eq_pi_rpow_extracted (r : ℕ) :
    PositiveDefiniteIntegralLattice.archimedeanMassFactor (2 * r) =
      2 * Real.rpow Real.pi
        (-(((2 * r : ℕ) : ℝ) * (((2 * r : ℕ) : ℝ) + 1) / 4)) *
        (Real.rpow Real.pi ((r : ℝ) / 2) *
          (Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
            (4 : ℝ) ^ (r * (r - 1) / 2)) := by
  rw [archimedeanMassFactor_even_eq_extracted]
  rw [sqrt_pi_pow_eq_rpow_half]

/-- Odd-rank archimedean factor with both visible `√π` factors rewritten as real
powers of `π`. -/
lemma archimedeanMassFactor_odd_eq_pi_rpow_extracted (r : ℕ) :
    PositiveDefiniteIntegralLattice.archimedeanMassFactor (2 * r + 1) =
      2 * Real.rpow Real.pi
        (-(((2 * r + 1 : ℕ) : ℝ) * (((2 * r + 1 : ℕ) : ℝ) + 1) / 4)) *
        ((Real.rpow Real.pi ((r : ℝ) / 2) *
          (Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
            (4 : ℝ) ^ (r * (r - 1) / 2)) *
          ((Nat.factorial (2 * r) : ℝ) * Real.rpow Real.pi (1 / 2 : ℝ) /
            ((4 : ℝ) ^ r * (Nat.factorial r : ℝ)))) := by
  rw [archimedeanMassFactor_odd_eq_extracted]
  rw [sqrt_pi_pow_eq_rpow_half, sqrt_pi_eq_rpow_half]

/-- In odd rank, the π powers from the archimedean factor and the zeta-core
special values cancel exactly. -/
lemma oddRank_archimedean_zetaCore_pi_cancel (r : ℕ) :
    Real.rpow Real.pi
        (-(((2 * r + 1 : ℕ) : ℝ) * (((2 * r + 1 : ℕ) : ℝ) + 1) / 4)) *
      (Real.rpow Real.pi ((r : ℝ) / 2) * Real.rpow Real.pi (1 / 2 : ℝ)) *
      Real.pi ^ (r * (r + 1)) = 1 := by
  let a : ℝ := -(((2 * r + 1 : ℕ) : ℝ) * (((2 * r + 1 : ℕ) : ℝ) + 1) / 4)
  let b : ℝ := (r : ℝ) / 2
  let c : ℝ := (1 / 2 : ℝ)
  let d : ℝ := (r * (r + 1) : ℕ)
  have hbc : Real.rpow Real.pi b * Real.rpow Real.pi c =
      Real.rpow Real.pi (b + c) := (Real.rpow_add Real.pi_pos b c).symm
  have habc : Real.rpow Real.pi a * Real.rpow Real.pi (b + c) =
      Real.rpow Real.pi (a + (b + c)) := (Real.rpow_add Real.pi_pos a (b + c)).symm
  have hall : Real.rpow Real.pi (a + (b + c)) * Real.rpow Real.pi d =
      Real.rpow Real.pi (a + (b + c) + d) :=
        (Real.rpow_add Real.pi_pos (a + (b + c)) d).symm
  rw [← Real.rpow_natCast Real.pi (r * (r + 1))]
  change Real.rpow Real.pi a * (Real.rpow Real.pi b * Real.rpow Real.pi c) *
    Real.rpow Real.pi d = 1
  rw [hbc, habc, hall]
  have hexp : a + (b + c) + d = 0 := by
    dsimp [a, b, c, d]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  rw [hexp]
  exact Real.rpow_zero Real.pi


/-- Product of the even factorials up to the top endpoint, converted from the
zero-based Gamma range to the one-based zeta-core range. -/
lemma prod_range_factorial_two_mul_mul_top_eq_prod_Icc (r : ℕ) :
    ((Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ))) *
        (Nat.factorial (2 * r) : ℝ) =
      (Finset.Icc 1 r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.prod_range_succ]
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1)]
      rw [← ih]

/-- Product of the even factorials in the even-rank Gamma range, converted to
the zeta-core range `1 ≤ j ≤ r-1`. -/
lemma prod_range_factorial_two_mul_eq_prod_Icc_pred (r : ℕ) :
    (Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) =
      (Finset.Icc 1 (r - 1)).prod (fun j => (Nat.factorial (2 * j) : ℝ)) := by
  cases r with
  | zero => simp
  | succ r =>
      rw [Finset.prod_range_succ]
      simpa using prod_range_factorial_two_mul_mul_top_eq_prod_Icc r

/-- The factorials in the zeta-core denominators cancel against the odd-rank
archimedean Gamma factorial range.  This algebraic lemma is stated
for an arbitrary numerator `A`; later applications instantiate `A` with the
explicit dyadic zeta-core numerator. -/
lemma prod_Icc_div_factorial_two_mul_mul_range_factorial_top (r : ℕ) (A : ℕ → ℝ) :
    ((Finset.Icc 1 r).prod
        (fun j => A j / (Nat.factorial (2 * j) : ℝ))) *
      ((Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) *
        (Nat.factorial (2 * r) : ℝ)) =
      (Finset.Icc 1 r).prod A := by
  have hfac := prod_range_factorial_two_mul_mul_top_eq_prod_Icc r
  rw [Finset.prod_div_distrib]
  rw [hfac]
  have hden : (Finset.Icc 1 r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) ≠ 0 := by
    positivity
  field_simp [hden]

/-- The factorials in the zeta-core denominators cancel against the even-rank
archimedean Gamma factorial range, with zeta-core range `1 ≤ j ≤ r-1`. -/
lemma prod_Icc_pred_div_factorial_two_mul_mul_range_factorial (r : ℕ) (A : ℕ → ℝ) :
    ((Finset.Icc 1 (r - 1)).prod
        (fun j => A j / (Nat.factorial (2 * j) : ℝ))) *
      ((Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ))) =
      (Finset.Icc 1 (r - 1)).prod A := by
  have hfac := prod_range_factorial_two_mul_eq_prod_Icc_pred r
  rw [Finset.prod_div_distrib]
  rw [hfac]
  have hden : (Finset.Icc 1 (r - 1)).prod (fun j => (Nat.factorial (2 * j) : ℝ)) ≠ 0 := by
    positivity
  field_simp [hden]

/-- Odd-rank zeta-core rational remainder multiplied by the extracted
archimedean factorial part.  The π powers are handled separately by
`oddRank_archimedean_zetaCore_pi_cancel`. -/
lemma oddRank_zetaCoreRemainder_mul_archimedeanFactorialPart (r : ℕ) :
    ((Finset.Icc 1 r).prod
        (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) *
          ((4 * j : ℚ) : ℝ) / (Nat.factorial (2 * j) : ℝ))) *
      (((Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
          (4 : ℝ) ^ (r * (r - 1) / 2)) *
        ((Nat.factorial (2 * r) : ℝ) /
          ((4 : ℝ) ^ r * (Nat.factorial r : ℝ))))) =
      (((Finset.Icc 1 r).prod
        (fun j => (((2 : ℝ) ^ (2 * j) - 1) / 2) * ((4 * j : ℚ) : ℝ))) /
        ((4 : ℝ) ^ (r * (r - 1) / 2 + r) * (Nat.factorial r : ℝ))) := by
  let A : ℕ → ℝ := fun j => (((2 : ℝ) ^ (2 * j) - 1) / 2) * ((4 * j : ℚ) : ℝ)
  have hcancel := prod_Icc_div_factorial_two_mul_mul_range_factorial_top r A
  have h4a : (4 : ℝ) ^ (r * (r - 1) / 2) ≠ 0 := by positivity
  have h4r : (4 : ℝ) ^ r ≠ 0 := by positivity
  have hfacr : (Nat.factorial r : ℝ) ≠ 0 := by positivity
  have hden : (4 : ℝ) ^ (r * (r - 1) / 2 + r) * (Nat.factorial r : ℝ) ≠ 0 := by
    positivity
  dsimp [A] at hcancel ⊢
  rw [← hcancel]
  field_simp [h4a, h4r, hfacr, hden]
  ring_nf

/-- Even-rank zeta-core rational remainder multiplied by the extracted
archimedean factorial part.  The residual `π^{-r}` is handled separately by
`evenRank_archimedean_zetaCore_pi_leftover`. -/
lemma evenRank_zetaCoreRemainder_mul_archimedeanFactorialPart (r : ℕ) :
    ((Finset.Icc 1 (r - 1)).prod
        (fun j => (((((2 : ℝ) ^ (2 * j) - 1) / 2) *
          ((4 * j : ℚ) : ℝ)) / (Nat.factorial (2 * j) : ℝ))) *
      ((Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
        (4 : ℝ) ^ (r * (r - 1) / 2))) =
      (((Finset.Icc 1 (r - 1)).prod
        (fun j => (((2 : ℝ) ^ (2 * j) - 1) / 2) * ((4 * j : ℚ) : ℝ))) /
        (4 : ℝ) ^ (r * (r - 1) / 2)) := by
  let A : ℕ → ℝ := fun j => (((2 : ℝ) ^ (2 * j) - 1) / 2) * ((4 * j : ℚ) : ℝ)
  have hcancel := prod_Icc_pred_div_factorial_two_mul_mul_range_factorial r A
  have h4 : (4 : ℝ) ^ (r * (r - 1) / 2) ≠ 0 := by positivity
  dsimp [A] at hcancel ⊢
  rw [← hcancel]
  field_simp [h4]


/-- The finite dyadic numerator left by the zeta-core special values factors
into the product of `(2^(2j)-1)` and the elementary product `∏ 2j = 2^r r!`. -/
lemma prod_Icc_zetaCoreDyadicNumerator_eq_two_pow_factorial_mul (r : ℕ) :
    (Finset.Icc 1 r).prod
        (fun j => (((2 : ℝ) ^ (2 * j) - 1) / 2) * ((4 * j : ℚ) : ℝ)) =
      (2 : ℝ) ^ r * (Nat.factorial r : ℝ) *
        (Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1) := by
  calc
    (Finset.Icc 1 r).prod
        (fun j => (((2 : ℝ) ^ (2 * j) - 1) / 2) * ((4 * j : ℚ) : ℝ))
        = (Finset.Icc 1 r).prod
            (fun j => ((2 : ℝ) ^ (2 * j) - 1) * ((2 : ℝ) * (j : ℝ))) := by
            refine Finset.prod_congr rfl ?_
            intro j hj
            norm_num [Rat.cast_mul]
            ring
    _ = (Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1) *
        (Finset.Icc 1 r).prod (fun j => (2 : ℝ) * (j : ℝ)) := by
            rw [Finset.prod_mul_distrib]
    _ = (Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1) *
        ((2 : ℝ) ^ r * (Nat.factorial r : ℝ)) := by
            rw [show (Finset.Icc 1 r).prod (fun j => (2 : ℝ) * (j : ℝ)) =
                (2 : ℝ) ^ r * (Nat.factorial r : ℝ) by
              induction r with
              | zero => simp
              | succ r ih =>
                  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1)]
                  rw [ih]
                  rw [Nat.factorial_succ]
                  norm_num [Nat.cast_add]
                  ring]
    _ = (2 : ℝ) ^ r * (Nat.factorial r : ℝ) *
        (Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1) := by ring

/-- The same dyadic numerator factorization on the even-rank zeta-core range
`1 ≤ j ≤ r-1`. -/
lemma prod_Icc_pred_zetaCoreDyadicNumerator_eq_two_pow_factorial_mul (r : ℕ) :
    (Finset.Icc 1 (r - 1)).prod
        (fun j => (((2 : ℝ) ^ (2 * j) - 1) / 2) * ((4 * j : ℚ) : ℝ)) =
      (2 : ℝ) ^ (r - 1) * (Nat.factorial (r - 1) : ℝ) *
        (Finset.Icc 1 (r - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1) := by
  exact prod_Icc_zetaCoreDyadicNumerator_eq_two_pow_factorial_mul (r - 1)

/-- Odd-rank factorial-cancelled zeta-core/archimedean rational remainder,
with the elementary `∏ 2j` product also simplified.  The leading factor `2`
from the native archimedean factor is included. -/
lemma oddRank_zetaCoreRemainder_mul_archimedeanFactorialPart_simplified (r : ℕ) :
    2 * (((Finset.Icc 1 r).prod
        (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) *
          ((4 * j : ℚ) : ℝ) / (Nat.factorial (2 * j) : ℝ))) *
      (((Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
          (4 : ℝ) ^ (r * (r - 1) / 2)) *
        ((Nat.factorial (2 * r) : ℝ) /
          ((4 : ℝ) ^ r * (Nat.factorial r : ℝ)))))) =
      (2 * (2 : ℝ) ^ r / (4 : ℝ) ^ (r * (r - 1) / 2 + r)) *
        (Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1) := by
  rw [oddRank_zetaCoreRemainder_mul_archimedeanFactorialPart]
  rw [prod_Icc_zetaCoreDyadicNumerator_eq_two_pow_factorial_mul]
  have h4 : (4 : ℝ) ^ (r * (r - 1) / 2 + r) ≠ 0 := by positivity
  have hfac : (Nat.factorial r : ℝ) ≠ 0 := by positivity
  field_simp [h4, hfac]

/-- Even-rank factorial-cancelled zeta-core/archimedean rational remainder,
with the elementary `∏ 2j` product also simplified.  The leading factor `2`
from the native archimedean factor is included. -/
lemma evenRank_zetaCoreRemainder_mul_archimedeanFactorialPart_simplified (r : ℕ) :
    2 * (((Finset.Icc 1 (r - 1)).prod
        (fun j => (((((2 : ℝ) ^ (2 * j) - 1) / 2) *
          ((4 * j : ℚ) : ℝ)) / (Nat.factorial (2 * j) : ℝ))) *
      ((Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
        (4 : ℝ) ^ (r * (r - 1) / 2)))) =
      (2 * (2 : ℝ) ^ (r - 1) * (Nat.factorial (r - 1) : ℝ) /
          (4 : ℝ) ^ (r * (r - 1) / 2)) *
        (Finset.Icc 1 (r - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1) := by
  rw [evenRank_zetaCoreRemainder_mul_archimedeanFactorialPart]
  rw [prod_Icc_pred_zetaCoreDyadicNumerator_eq_two_pow_factorial_mul]
  have h4 : (4 : ℝ) ^ (r * (r - 1) / 2) ≠ 0 := by positivity
  field_simp [h4]

/-- In even rank, the archimedean π powers and the zeta-core π powers leave
the single residual `π^{-r}` factor which must later be canceled by the
Dirichlet-character special value. -/
lemma evenRank_archimedean_zetaCore_pi_leftover (r : ℕ) (hr : 1 ≤ r) :
    Real.rpow Real.pi
        (-(((2 * r : ℕ) : ℝ) * (((2 * r : ℕ) : ℝ) + 1) / 4)) *
      Real.rpow Real.pi ((r : ℝ) / 2) *
      Real.pi ^ ((r - 1) * r) = Real.rpow Real.pi (-(r : ℝ)) := by
  let a : ℝ := -(((2 * r : ℕ) : ℝ) * (((2 * r : ℕ) : ℝ) + 1) / 4)
  let b : ℝ := (r : ℝ) / 2
  let d : ℝ := ((r - 1) * r : ℕ)
  have hsub_nat : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hsub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    have hcast : (((r - 1) + 1 : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast hsub_nat
    norm_num [Nat.cast_add] at hcast
    linarith
  have hab : Real.rpow Real.pi a * Real.rpow Real.pi b =
      Real.rpow Real.pi (a + b) := (Real.rpow_add Real.pi_pos a b).symm
  have hall : Real.rpow Real.pi (a + b) * Real.rpow Real.pi d =
      Real.rpow Real.pi (a + b + d) := (Real.rpow_add Real.pi_pos (a + b) d).symm
  rw [← Real.rpow_natCast Real.pi ((r - 1) * r)]
  change Real.rpow Real.pi a * Real.rpow Real.pi b * Real.rpow Real.pi d =
    Real.rpow Real.pi (-(r : ℝ))
  rw [hab, hall]
  congr 1
  dsimp [a, b, d]
  norm_num [Nat.cast_mul]
  rw [hsub]
  ring

/-- The extra trivial-character Dirichlet tail in even half-rank carries exactly
the π power needed to cancel the residual `π^{-r}` left by the even-rank
zeta-core/archimedean product. -/
lemma evenRank_trivialDirichletTail_pi_cancel (r : ℕ) (hr_even : Even r) :
    Real.rpow Real.pi (-(r : ℝ)) * Real.pi ^ (2 * (r / 2)) = 1 := by
  have hpow : Real.pi ^ (2 * (r / 2)) =
      Real.rpow Real.pi (((2 * (r / 2) : ℕ) : ℝ)) := by
    exact (Real.rpow_natCast Real.pi (2 * (r / 2))).symm
  rw [hpow]
  have hmul : Real.rpow Real.pi (-(r : ℝ)) *
      Real.rpow Real.pi (((2 * (r / 2) : ℕ) : ℝ)) =
        Real.rpow Real.pi (-(r : ℝ) + ((2 * (r / 2) : ℕ) : ℝ)) :=
    (Real.rpow_add Real.pi_pos (-(r : ℝ)) (((2 * (r / 2) : ℕ) : ℝ))).symm
  rw [hmul]
  have hexp : -(r : ℝ) + ((2 * (r / 2) : ℕ) : ℝ) = 0 := by
    have hr_nat : r = 2 * (r / 2) := by
      rcases hr_even with ⟨k, hk⟩
      subst r
      omega
    rw [← hr_nat]
    norm_num
  rw [hexp]
  exact Real.rpow_zero Real.pi

/-- Extracted odd-rank π product from the zeta-core and archimedean factors. -/
def oddRankExtractedPiProduct (r : ℕ) : ℝ :=
  Real.rpow Real.pi
      (-(((2 * r + 1 : ℕ) : ℝ) * (((2 * r + 1 : ℕ) : ℝ) + 1) / 4)) *
    (Real.rpow Real.pi ((r : ℝ) / 2) * Real.rpow Real.pi (1 / 2 : ℝ)) *
    Real.pi ^ (r * (r + 1))

/-- Extracted odd-rank rational product after Bernoulli, zeta and Gamma rewrites,
before the final elementary dyadic numerator simplification. -/
def oddRankExtractedRationalProduct (r : ℕ) : ℝ :=
  2 * (((Finset.Icc 1 r).prod
    (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) *
      ((4 * j : ℚ) : ℝ) / (Nat.factorial (2 * j) : ℝ))) *
    (((Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
      (4 : ℝ) ^ (r * (r - 1) / 2)) *
    ((Nat.factorial (2 * r) : ℝ) /
      ((4 : ℝ) ^ r * (Nat.factorial r : ℝ))))))

/-- Simplified odd-rank elementary dyadic numerator remainder. -/
def oddRankDyadicNumeratorRemainder (r : ℕ) : ℝ :=
  (2 * (2 : ℝ) ^ r / (4 : ℝ) ^ (r * (r - 1) / 2 + r)) *
    (Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)

/-- Extracted even-rank π product from the zeta-core and archimedean factors. -/
def evenRankExtractedPiProduct (r : ℕ) : ℝ :=
  Real.rpow Real.pi
      (-(((2 * r : ℕ) : ℝ) * (((2 * r : ℕ) : ℝ) + 1) / 4)) *
    Real.rpow Real.pi ((r : ℝ) / 2) *
    Real.pi ^ ((r - 1) * r)

/-- In the even half-rank branch, adjoining the trivial-character zeta tail
cancels all π powers in the extracted even-rank product. -/
lemma evenRankExtractedPiProduct_mul_trivialDirichletTail_pi_cancel
    (r : ℕ) (hr : 1 ≤ r) (hr_even : Even r) :
    evenRankExtractedPiProduct r * Real.pi ^ (2 * (r / 2)) = 1 := by
  unfold evenRankExtractedPiProduct
  rw [evenRank_archimedean_zetaCore_pi_leftover r hr]
  exact evenRank_trivialDirichletTail_pi_cancel r hr_even

/-- Extracted even-rank rational product after Bernoulli, zeta and Gamma
rewrites, before the final elementary dyadic numerator simplification. -/
def evenRankExtractedRationalProduct (r : ℕ) : ℝ :=
  2 * (((Finset.Icc 1 (r - 1)).prod
    (fun j => ((((2 : ℝ) ^ (2 * j) - 1) / 2) *
      ((4 * j : ℚ) : ℝ) / (Nat.factorial (2 * j) : ℝ))) *
    ((Finset.range r).prod (fun j => (Nat.factorial (2 * j) : ℝ)) /
      (4 : ℝ) ^ (r * (r - 1) / 2))))

/-- Simplified even-rank elementary dyadic numerator remainder, with the
residual `π^{-r}` factor kept separately. -/
def evenRankDyadicNumeratorRemainder (r : ℕ) : ℝ :=
  (2 * (2 : ℝ) ^ (r - 1) * (Nat.factorial (r - 1) : ℝ) /
      (4 : ℝ) ^ (r * (r - 1) / 2)) *
    (Finset.Icc 1 (r - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)

/-- Odd-rank extracted zeta-core/archimedean product after the Bernoulli, π,
Gamma-factorial, and elementary dyadic-numerator simplifications.  This is the
combined algebraic cancellation layer after the actual zeta and Gamma factors
have been rewritten by the preceding lemmas; it still does not evaluate the
native dyadic local factor. -/
lemma oddRank_extracted_zetaCore_archimedean_remainder_simplified (r : ℕ) :
    oddRankExtractedPiProduct r * oddRankExtractedRationalProduct r =
      oddRankDyadicNumeratorRemainder r := by
  unfold oddRankExtractedPiProduct oddRankExtractedRationalProduct
    oddRankDyadicNumeratorRemainder
  rw [oddRank_archimedean_zetaCore_pi_cancel]
  simpa using oddRank_zetaCoreRemainder_mul_archimedeanFactorialPart_simplified r

/-- Even-rank extracted zeta-core/archimedean product after the Bernoulli, π,
Gamma-factorial, and elementary dyadic-numerator simplifications.  The residual
`π^{-r}` factor is left visible for the later Dirichlet-character special-value
cancellation. -/
lemma evenRank_extracted_zetaCore_archimedean_remainder_simplified
    (r : ℕ) (hr : 1 ≤ r) :
    evenRankExtractedPiProduct r * evenRankExtractedRationalProduct r =
      Real.rpow Real.pi (-(r : ℝ)) * evenRankDyadicNumeratorRemainder r := by
  unfold evenRankExtractedPiProduct evenRankExtractedRationalProduct
    evenRankDyadicNumeratorRemainder
  rw [evenRank_archimedean_zetaCore_pi_leftover r hr]
  rw [evenRank_zetaCoreRemainder_mul_archimedeanFactorialPart_simplified]

/-- In the non-endpoint odd half-rank branch, the extracted even-rank
zeta/archimedean product and the proved `χ₋₄` character tail combine to a
π-free Bernoulli/factorial expression.  This is the combined special-value
bridge before the remaining elementary dyadic numerator simplification to the
Type I constant. -/
lemma evenRank_extracted_mul_characterTail_oddHalf_rational
    {n k : ℕ} (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular)
    (hk : k ≠ 0) (hn : n = 2 * (2 * k + 1)) :
    evenRankExtractedPiProduct (2 * k + 1) *
        evenRankExtractedRationalProduct (2 * k + 1) *
          PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
            L 2 (2 * k + 1) =
      evenRankDyadicNumeratorRemainder (2 * k + 1) *
        (|(chiMinusFourBernoulli (2 * k + 1) : ℝ)| /
          ((2 : ℝ) ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ))) := by
  have hspecial := evenRank_extracted_zetaCore_archimedean_remainder_simplified
    (r := 2 * k + 1) (by omega : 1 ≤ 2 * k + 1)
  have htail := ChiMinusFour.lattice_character_tail_pi_cancel_unconditional
    (L := L) hL hk hn
  calc
    evenRankExtractedPiProduct (2 * k + 1) *
        evenRankExtractedRationalProduct (2 * k + 1) *
          PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
            L 2 (2 * k + 1)
        = (Real.rpow Real.pi (-(((2 * k + 1 : ℕ) : ℝ))) *
              evenRankDyadicNumeratorRemainder (2 * k + 1)) *
            PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
              L 2 (2 * k + 1) := by
            rw [hspecial]
    _ = evenRankDyadicNumeratorRemainder (2 * k + 1) *
          (Real.rpow Real.pi (-(((2 * k + 1 : ℕ) : ℝ))) *
            PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
              L 2 (2 * k + 1)) := by
            ring
    _ = evenRankDyadicNumeratorRemainder (2 * k + 1) *
        (|(chiMinusFourBernoulli (2 * k + 1) : ℝ)| /
          ((2 : ℝ) ^ (2 * k + 1) * ((2 * k + 1).factorial : ℝ))) := by
            rw [htail]

/-- Elementary cancellation in the π-free odd half-rank `χ₋₄` factor: the
factorial and `2^r` denominator in the Bernoulli special value cancel the
leading part of `evenRankDyadicNumeratorRemainder`. -/
lemma evenRankDyadicNumeratorRemainder_mul_chiMinusFourFactor
    (r : ℕ) (hr : 0 < r) :
    evenRankDyadicNumeratorRemainder r *
        (|(chiMinusFourBernoulli r : ℝ)| /
          ((2 : ℝ) ^ r * (r.factorial : ℝ))) =
      (|(chiMinusFourBernoulli r : ℝ)| / (r : ℝ)) *
        ((Finset.Icc 1 (r - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (r * (r - 1) / 2) := by
  unfold evenRankDyadicNumeratorRemainder
  have hpow : 2 * (2 : ℝ) ^ (r - 1) = (2 : ℝ) ^ r := by
    cases r with
    | zero => cases hr
    | succ r =>
        simp [pow_succ]
        ring
  have hfac_nat : Nat.factorial r = r * Nat.factorial (r - 1) := by
    cases r with
    | zero => cases hr
    | succ r =>
        rw [Nat.factorial_succ]
        simp
  have hfac : (r.factorial : ℝ) = (r : ℝ) * ((r - 1).factorial : ℝ) := by
    exact_mod_cast hfac_nat
  have hr_ne : (r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hr)
  have hfac_ne : ((r - 1).factorial : ℝ) ≠ 0 := by positivity
  have hpow_ne : (2 : ℝ) ^ r ≠ 0 := by positivity
  have hfour_ne : (4 : ℝ) ^ (r * (r - 1) / 2) ≠ 0 := by positivity
  rw [hpow, hfac]
  field_simp [hr_ne, hfac_ne, hpow_ne, hfour_ne]

/-- Compact form of the non-endpoint odd half-rank special-value bridge after
the elementary factorial and `2^r` cancellation.  The remaining finite product
is the explicit dyadic numerator factor that will be compared with the dyadic
local density. -/
lemma evenRank_extracted_mul_characterTail_oddHalf_compact
    {n k : ℕ} (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular)
    (hk : k ≠ 0) (hn : n = 2 * (2 * k + 1)) :
    evenRankExtractedPiProduct (2 * k + 1) *
        evenRankExtractedRationalProduct (2 * k + 1) *
          PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
            L 2 (2 * k + 1) =
      (|(chiMinusFourBernoulli (2 * k + 1) : ℝ)| / ((2 * k + 1 : ℕ) : ℝ)) *
        ((Finset.Icc 1 (2 * k + 1 - 1)).prod
          (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2) := by
  rw [evenRank_extracted_mul_characterTail_oddHalf_rational (L := L) hL hk hn]
  exact evenRankDyadicNumeratorRemainder_mul_chiMinusFourFactor
    (2 * k + 1) (by omega)

/-- After reinserting the Bernoulli-core product, the compact odd half-rank
special-value factor is the Type I constant times the remaining explicit dyadic
numerator factor.  This separates the final rational constant from the part
that must be supplied by the dyadic local density. -/
lemma oddHalfCompactFactor_mul_bernoulliCore_eq_typeIConstant
    (m : ℕ) (hm_odd : m % 2 = 1) :
    (bernoulliCore (m - 1) : ℝ) *
        ((|(chiMinusFourBernoulli m : ℝ)| / (m : ℝ)) *
          ((Finset.Icc 1 (m - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (m * (m - 1) / 2)) =
      (4 : ℝ) * (typeIConstant (2 * m) : ℝ) *
        ((Finset.Icc 1 (m - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (m * (m - 1) / 2) := by
  have htype := typeIConstant_even_odd_halfRank_real (m := m) hm_odd
  have hm_pos : 0 < m := by omega
  have hm_ne : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm_pos)
  have hfour_ne : (4 : ℝ) ^ (m * (m - 1) / 2) ≠ 0 := by positivity
  rw [htype]
  field_simp [hm_ne, hfour_ne]

/-- Odd half-rank special-value bridge after reinserting `bernoulliCore`: the
analytic zeta/Gamma/`χ₋₄` tail part has been reduced to the Type I constant
times the explicit dyadic numerator factor.  The dyadic local density remains
separate. -/
lemma evenRank_extracted_mul_characterTail_oddHalf_typeIConstant
    {n k : ℕ} (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular)
    (hk : k ≠ 0) (hn : n = 2 * (2 * k + 1)) :
    (bernoulliCore (2 * k + 1 - 1) : ℝ) *
      (evenRankExtractedPiProduct (2 * k + 1) *
        evenRankExtractedRationalProduct (2 * k + 1) *
          PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
            L 2 (2 * k + 1)) =
      (4 : ℝ) * (typeIConstant (2 * (2 * k + 1)) : ℝ) *
        ((Finset.Icc 1 (2 * k + 1 - 1)).prod
          (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2) := by
  rw [evenRank_extracted_mul_characterTail_oddHalf_compact (L := L) hL hk hn]
  exact oddHalfCompactFactor_mul_bernoulliCore_eq_typeIConstant
    (m := 2 * k + 1) (by omega)

/-- In the non-endpoint even half-rank branch, the extracted even-rank
zeta/archimedean product and the trivial-character Dirichlet tail combine to a
π-free Bernoulli/factorial expression.  This is the ordinary-Bernoulli analogue
of `evenRank_extracted_mul_characterTail_oddHalf_rational`. -/
lemma evenRank_extracted_mul_characterTail_evenHalf_rational
    {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular)
    (hm_one : 1 < m) (hm_even : Even m) (hn : n = 2 * m) :
    evenRankExtractedPiProduct m *
        evenRankExtractedRationalProduct m *
          PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
            L 2 m =
      evenRankDyadicNumeratorRemainder m *
        ((|(bernoulli m : ℝ)| / (4 * ((m : ℝ) / 2))) *
          ((((2 : ℝ) ^ m - 1) / 2) * (4 * ((m : ℝ) / 2)) /
            (Nat.factorial m : ℝ))) := by
  have hspecial := evenRank_extracted_zetaCore_archimedean_remainder_simplified
    (r := m) (by omega : 1 ≤ m)
  have htail :=
    PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor_eq_zetaTail_of_isUnimodular_even_halfRank
      (L := L) hL hm_one hm_even hn
  have hhalf_ne : m / 2 ≠ 0 := by
    rcases hm_even with ⟨k, hk⟩
    subst m
    omega
  have hm2 : 2 * (m / 2) = m := by
    rcases hm_even with ⟨k, hk⟩
    subst m
    omega
  have hm_half_cast : ((m / 2 : ℕ) : ℝ) = (m : ℝ) / 2 := by
    rcases hm_even with ⟨k, hk⟩
    subst m
    have hkdiv : (k + k) / 2 = k := by omega
    norm_num [hkdiv]
  calc
    evenRankExtractedPiProduct m * evenRankExtractedRationalProduct m *
          PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor L 2 m
        = (Real.rpow Real.pi (-(m : ℝ)) * evenRankDyadicNumeratorRemainder m) *
          PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor L 2 m := by
            rw [hspecial]
    _ = evenRankDyadicNumeratorRemainder m *
        (Real.rpow Real.pi (-(m : ℝ)) *
          PositiveDefiniteIntegralLattice.goodPrimeEulerCoreZetaTailFactor 2 (m / 2)) := by
            rw [htail]
            ring
    _ = evenRankDyadicNumeratorRemainder m *
        (Real.rpow Real.pi (-(m : ℝ)) *
          ((|(bernoulli m : ℝ)| / (4 * ((m : ℝ) / 2))) *
            ((((2 : ℝ) ^ m - 1) / 2) * Real.pi ^ m * (4 * ((m : ℝ) / 2)) /
              (Nat.factorial m : ℝ)))) := by
            rw [PositiveDefiniteIntegralLattice.goodPrimeEulerCoreZetaTailFactor_two]
            rw [zetaCoreRemovedTwo_eq_bernoulli_pi_dyadicFactor (j := m / 2) hhalf_ne]
            rw [zetaCoreRemovedTwo_eq_bernoulliCoreFactor (j := m / 2) hhalf_ne]
            simp [hm2, hm_half_cast]
    _ = evenRankDyadicNumeratorRemainder m *
        ((|(bernoulli m : ℝ)| / (4 * ((m : ℝ) / 2))) *
          ((((2 : ℝ) ^ m - 1) / 2) * (4 * ((m : ℝ) / 2)) /
            (Nat.factorial m : ℝ))) := by
            congr 1
            have hpi : Real.rpow Real.pi (-(m : ℝ)) * Real.pi ^ m = 1 := by
              have hpow : Real.pi ^ m = Real.pi ^ (2 * (m / 2)) := by rw [hm2]
              rw [hpow]
              exact evenRank_trivialDirichletTail_pi_cancel m hm_even
            have hfac : (Nat.factorial m : ℝ) ≠ 0 := by positivity
            field_simp [hfac]
            calc
              Real.pi.rpow (-(m : ℝ)) * |(bernoulli m : ℝ)| * ((2 : ℝ) ^ m - 1) *
                    Real.pi ^ m
                  = (Real.rpow Real.pi (-(m : ℝ)) * Real.pi ^ m) *
                      (|(bernoulli m : ℝ)| * ((2 : ℝ) ^ m - 1)) := by ring
              _ = |(bernoulli m : ℝ)| * ((2 : ℝ) ^ m - 1) := by
                    rw [hpi]
                    ring

/-- Elementary cancellation in the π-free even half-rank trivial-character
factor.  The extra zeta value at exponent `m / 2` cancels the factorial and
half-rank denominator, leaving the explicit dyadic numerator factor expected
to pair with the dyadic local density. -/
lemma evenRankDyadicNumeratorRemainder_mul_trivialZetaFactor
    (m : ℕ) (hm : 0 < m) :
    evenRankDyadicNumeratorRemainder m *
        ((|(bernoulli m : ℝ)| / (4 * ((m : ℝ) / 2))) *
          ((((2 : ℝ) ^ m - 1) / 2) * (4 * ((m : ℝ) / 2)) /
            (Nat.factorial m : ℝ))) =
      (((2 : ℝ) ^ (m - 1) * ((2 : ℝ) ^ m - 1) * |(bernoulli m : ℝ)|) /
          (m : ℝ)) *
        ((Finset.Icc 1 (m - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (m * (m - 1) / 2) := by
  unfold evenRankDyadicNumeratorRemainder
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hhalf_ne : (m : ℝ) / 2 ≠ 0 := by positivity
  have hfac_nat : Nat.factorial m = m * Nat.factorial (m - 1) := by
    cases m with
    | zero => cases hm
    | succ m =>
        rw [Nat.factorial_succ]
        simp
  have hfac : (Nat.factorial m : ℝ) = (m : ℝ) * (Nat.factorial (m - 1) : ℝ) := by
    exact_mod_cast hfac_nat
  have hfac_pred_ne : (Nat.factorial (m - 1) : ℝ) ≠ 0 := by positivity
  have hfour_ne : (4 : ℝ) ^ (m * (m - 1) / 2) ≠ 0 := by positivity
  rw [hfac]
  field_simp [hm_ne, hhalf_ne, hfac_pred_ne, hfour_ne]

/-- After reinserting the Bernoulli-core product, the compact even half-rank
ordinary-Bernoulli special-value factor is the Type I constant times the
remaining explicit dyadic numerator factor.  The statement is cross-multiplied
by the elementary Type I sign denominator, avoiding a separate nonvanishing
side condition. -/
lemma evenHalfCompactFactor_mul_bernoulliCore_eq_typeIConstant
    (m : ℕ) (hm : 0 < m) (hm_even : m % 2 = 0) :
    (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) *
      ((bernoulliCore (m - 1) : ℝ) *
        ((((2 : ℝ) ^ (m - 1) * ((2 : ℝ) ^ m - 1) * |(bernoulli m : ℝ)|) /
            (m : ℝ)) *
          ((Finset.Icc 1 (m - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (m * (m - 1) / 2))) =
      (4 : ℝ) * (2 : ℝ) ^ (m - 1) * (typeIConstant (2 * m) : ℝ) *
        ((Finset.Icc 1 (m - 1)).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (m * (m - 1) / 2) := by
  have htype := typeIConstant_even_even_halfRank_real (m := m) hm hm_even
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hfour_ne : (4 : ℝ) ^ (m * (m - 1) / 2) ≠ 0 := by positivity
  rw [htype]
  norm_num [Rat.cast_add, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_div]
  field_simp [hm_ne, hfour_ne]

/-- Even half-rank special-value bridge after reinserting `bernoulliCore`: the
analytic zeta/Gamma/trivial-character tail has been reduced to the Type I
constant, up to the explicit dyadic numerator factor and the elementary
cross-multiplied sign denominator. -/
lemma evenRank_extracted_mul_characterTail_evenHalf_typeIConstant
    {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) (hL : L.IsUnimodular)
    (hm_one : 1 < m) (hm_even : Even m) (hn : n = 2 * m) :
    (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) *
      ((bernoulliCore (m - 1) : ℝ) *
        (evenRankExtractedPiProduct m *
          evenRankExtractedRationalProduct m *
            PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
              L 2 m)) =
      (4 : ℝ) * (2 : ℝ) ^ (m - 1) * (typeIConstant (2 * m) : ℝ) *
        ((Finset.Icc 1 (m - 1)).prod
          (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (m * (m - 1) / 2) := by
  have hm_pos : 0 < m := by omega
  have hm_even_mod : m % 2 = 0 := by
    rcases hm_even with ⟨k, hk⟩
    subst m
    omega
  rw [evenRank_extracted_mul_characterTail_evenHalf_rational (L := L) hL hm_one hm_even hn]
  rw [evenRankDyadicNumeratorRemainder_mul_trivialZetaFactor m hm_pos]
  exact evenHalfCompactFactor_mul_bernoulliCore_eq_typeIConstant m hm_pos hm_even_mod

/-- In odd rank, after reinserting the Bernoulli-core product, the compact
zeta/Gamma special-value factor is the Type I constant times the remaining
explicit dyadic numerator factor.  As in the even half-rank branch, the
statement is cross-multiplied by the elementary sign denominator to avoid a
separate nonvanishing side condition. -/
lemma oddRankCompactFactor_mul_bernoulliCore_eq_typeIConstant
    (r : ℕ) (hr : 1 ≤ r) :
    (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ) *
      ((bernoulliCore r : ℝ) * oddRankDyadicNumeratorRemainder r) =
      (4 : ℝ) * (2 : ℝ) ^ r * (typeIConstant (2 * r + 1) : ℝ) *
        ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (r * (r - 1) / 2 + r) := by
  have htype := typeIConstant_two_mul_add_one_real r hr
  rw [htype]
  unfold oddRankDyadicNumeratorRemainder
  norm_num [Rat.cast_add, Rat.cast_pow, Rat.cast_div]
  have hfour_ne : (4 : ℝ) ^ (r * (r - 1) / 2 + r) ≠ 0 := by positivity
  field_simp [hfour_ne]
  ring

/-- Odd-rank special-value bridge after reinserting `bernoulliCore`: the
analytic zeta/Gamma product has been reduced to the Type I constant, up to the
explicit dyadic numerator factor and the elementary cross-multiplied sign
denominator. -/
lemma oddRank_extracted_zetaCore_archimedean_typeIConstant
    (r : ℕ) (hr : 1 ≤ r) :
    (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ) *
      ((bernoulliCore r : ℝ) *
        (oddRankExtractedPiProduct r * oddRankExtractedRationalProduct r)) =
      (4 : ℝ) * (2 : ℝ) ^ r * (typeIConstant (2 * r + 1) : ℝ) *
        ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ (r * (r - 1) / 2 + r) := by
  rw [oddRank_extracted_zetaCore_archimedean_remainder_simplified]
  exact oddRankCompactFactor_mul_bernoulliCore_eq_typeIConstant r hr

end UnimodularMass

end
