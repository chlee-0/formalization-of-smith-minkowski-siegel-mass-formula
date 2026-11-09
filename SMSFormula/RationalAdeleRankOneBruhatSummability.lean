import SMSFormula.RationalAdeleRankOneBruhatFactorization
import SMSFormula.RationalFiniteAdeleQuadraticGaussDenominatorDecay
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# Summability of the concrete rational rank-one Bruhat family

This file combines the exact real--finite Bruhat factorization with the finite
quadratic Gauss denominator decay.  The reduced numerator and denominator of a
rational parameter define an injective point of `ℤ²`; its max-norm supplies the
literal height.  The real and finite square-root factors are jointly bounded by
the inverse square root of this height, up to the visible positive real-scale,
polar-determinant, and lattice-discriminant constants.

The elementary max-norm `ℤ²` p-series is summable once its exponent is greater
than two.  Restriction along the reduced rational pair therefore proves actual
summability of the Bruhat coefficients in every rank at least five.  No
rational `tsum`, Eisenstein functional, Weil representation, or coefficient
identity is defined here.
-/

noncomputable section

open Matrix MeasureTheory RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The canonical reduced numerator--denominator pair of a rational Bruhat
parameter. -/
def rationalRankOneBruhatPair (t : ℚ) : Fin 2 → ℤ :=
  ![t.num, (t.den : ℤ)]

/-- The max-norm height of the canonical reduced numerator--denominator pair. -/
def rationalRankOneBruhatHeight (t : ℚ) : ℝ :=
  ‖rationalRankOneBruhatPair t‖

/-- Reduced numerator--denominator pairs distinguish rational numbers. -/
theorem rationalRankOneBruhatPair_injective :
    Function.Injective rationalRankOneBruhatPair := by
  intro s t h
  apply Rat.ext
  · simpa [rationalRankOneBruhatPair] using congrFun h 0
  · exact_mod_cast (show (s.den : ℤ) = (t.den : ℤ) by
      simpa [rationalRankOneBruhatPair] using congrFun h 1)

/-- The canonical Bruhat height is the maximum of the absolute numerator and
the positive denominator. -/
theorem rationalRankOneBruhatHeight_eq_max (t : ℚ) :
    rationalRankOneBruhatHeight t =
      max (t.num.natAbs : ℝ) (t.den : ℝ) := by
  rw [rationalRankOneBruhatHeight,
    EisensteinSeries.norm_eq_max_natAbs]
  simp [rationalRankOneBruhatPair]

/-- The rational height p-series is the restriction of the elementary
max-norm p-series on `ℤ²`. -/
theorem summable_rationalRankOneBruhatHeight_rpow
    {k : ℝ} (hk : 2 < k) :
    Summable (fun t : ℚ => rationalRankOneBruhatHeight t ^ (-k)) := by
  simpa [rationalRankOneBruhatHeight, Function.comp_def] using
    (EisensteinSeries.summable_one_div_norm_rpow hk).comp_injective
      rationalRankOneBruhatPair_injective

/-- The positive real scale and the canonical rational height are controlled
jointly by the denominator times the exact archimedean norm. -/
theorem min_scale_mul_rationalRankOneBruhatHeight_le_den_mul_complex_norm
    {a : ℝ} (ha : 0 < a) (t : ℚ) :
    min a 1 * rationalRankOneBruhatHeight t ≤
      (t.den : ℝ) * ‖(a : ℂ) - (t : ℂ) * Complex.I‖ := by
  have hnorma : a ≤ ‖(a : ℂ) - (t : ℂ) * Complex.I‖ := by
    have h :=
      Complex.abs_re_le_norm ((a : ℂ) - (t : ℂ) * Complex.I)
    simpa [abs_of_pos ha] using h
  have hnormt : |(t : ℝ)| ≤
      ‖(a : ℂ) - (t : ℂ) * Complex.I‖ := by
    have h :=
      Complex.abs_im_le_norm ((a : ℂ) - (t : ℂ) * Complex.I)
    simpa using h
  have hnum : (t.num.natAbs : ℝ) =
      (t.den : ℝ) * |(t : ℝ)| := by
    rw [Rat.cast_def, abs_div]
    rw [abs_of_pos (show (0 : ℝ) < t.den by exact_mod_cast t.den_pos)]
    rw [Nat.cast_natAbs, Int.cast_abs]
    field_simp
  rw [rationalRankOneBruhatHeight_eq_max]
  by_cases h : t.num.natAbs ≤ t.den
  · rw [max_eq_right (by exact_mod_cast h)]
    calc
      min a 1 * (t.den : ℝ) ≤ a * (t.den : ℝ) := by
        gcongr
        exact min_le_left _ _
      _ ≤ ‖(a : ℂ) - (t : ℂ) * Complex.I‖ * (t.den : ℝ) := by
        gcongr
      _ = (t.den : ℝ) *
          ‖(a : ℂ) - (t : ℂ) * Complex.I‖ := mul_comm _ _
  · rw [max_eq_left (by exact_mod_cast (Nat.le_of_not_ge h))]
    calc
      min a 1 * (t.num.natAbs : ℝ) ≤ (t.num.natAbs : ℝ) := by
        nlinarith [min_le_right a 1,
          (show (0 : ℝ) ≤ min a 1 from le_min ha.le (by norm_num))]
      _ = (t.den : ℝ) * |(t : ℝ)| := hnum
      _ ≤ (t.den : ℝ) *
          ‖(a : ℂ) - (t : ℂ) * Complex.I‖ := by
        gcongr

/-- The exact real and finite inverse square-root factors are bounded by the
canonical height factor, with the positive real-scale loss left visible. -/
theorem inv_sqrt_norm_mul_inv_sqrt_den_le_rationalRankOneBruhatHeight
    {a : ℝ} (ha : 0 < a) (t : ℚ) :
    (Real.sqrt ‖(a : ℂ) - (t : ℂ) * Complex.I‖)⁻¹ *
        (Real.sqrt (t.den : ℝ))⁻¹ ≤
      (Real.sqrt (min a 1))⁻¹ *
        (Real.sqrt (rationalRankOneBruhatHeight t))⁻¹ := by
  have hm : 0 < min a 1 := lt_min ha zero_lt_one
  have hh : 0 < rationalRankOneBruhatHeight t := by
    rw [rationalRankOneBruhatHeight_eq_max]
    exact lt_of_lt_of_le (by exact_mod_cast t.den_pos)
      (le_max_right _ _)
  have hn : 0 < ‖(a : ℂ) - (t : ℂ) * Complex.I‖ := by
    have h :=
      Complex.abs_re_le_norm ((a : ℂ) - (t : ℂ) * Complex.I)
    have h' : a ≤ ‖(a : ℂ) - (t : ℂ) * Complex.I‖ := by
      simpa [abs_of_pos ha] using h
    exact lt_of_lt_of_le ha h'
  have hd : 0 < (t.den : ℝ) := by
    exact_mod_cast t.den_pos
  have hsqrt := Real.sqrt_le_sqrt
    (min_scale_mul_rationalRankOneBruhatHeight_le_den_mul_complex_norm
      ha t)
  rw [Real.sqrt_mul hm.le, Real.sqrt_mul hd.le] at hsqrt
  have hinv :
      (Real.sqrt (t.den : ℝ) *
          Real.sqrt ‖(a : ℂ) - (t : ℂ) * Complex.I‖)⁻¹ ≤
        (Real.sqrt (min a 1) *
          Real.sqrt (rationalRankOneBruhatHeight t))⁻¹ :=
    (inv_le_inv₀
      (mul_pos (Real.sqrt_pos.2 hd) (Real.sqrt_pos.2 hn))
      (mul_pos (Real.sqrt_pos.2 hm) (Real.sqrt_pos.2 hh))).2 hsqrt
  simpa [mul_inv, mul_comm] using hinv

/-- The natural power of the inverse square-root height is its literal real
height power of exponent `-n/2`. -/
theorem inv_sqrt_rationalRankOneBruhatHeight_pow_eq_rpow
    (t : ℚ) (n : ℕ) :
    (Real.sqrt (rationalRankOneBruhatHeight t))⁻¹ ^ n =
      rationalRankOneBruhatHeight t ^ (-((n : ℝ) / 2)) := by
  have hh : 0 ≤ rationalRankOneBruhatHeight t := by
    rw [rationalRankOneBruhatHeight_eq_max]
    positivity
  rw [Real.sqrt_eq_rpow, inv_pow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hh]
  rw [← Real.rpow_neg hh]
  congr 1
  ring

/-- In rank at least five, the inverse-square-root rational height to the rank
is summable. -/
theorem summable_inv_sqrt_rationalRankOneBruhatHeight_pow
    {n : ℕ} (hn : 5 ≤ n) :
    Summable (fun t : ℚ =>
      (Real.sqrt (rationalRankOneBruhatHeight t))⁻¹ ^ n) := by
  have hn' : (4 : ℕ) < n := by omega
  have hnR : (4 : ℝ) < (n : ℝ) := by exact_mod_cast hn'
  have hexp : (2 : ℝ) < (n : ℝ) / 2 := by linarith
  apply (summable_rationalRankOneBruhatHeight_rpow hexp).congr
  intro t
  exact (inv_sqrt_rationalRankOneBruhatHeight_pow_eq_rpow t n).symm

/-- Exact norm of the explicit archimedean factor in the Bruhat
factorization at a positive real Gaussian scale. -/
theorem norm_polarRealGaussian_explicit_bruhat_factor
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (t : ℚ) :
    ‖(L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / ((a : ℂ) - (t : ℂ) * Complex.I) ^
          (1 / 2 : ℂ)) ^ n‖ =
      (L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt ‖(a : ℂ) - (t : ℂ) * Complex.I‖)⁻¹ ^ n := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg
    (by exact_mod_cast L.polarRealDeterminantScale_pos.le)]
  rw [norm_pow, norm_div, norm_one,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_real]
  simp only [one_div, Real.sqrt_eq_rpow]

/-- The concrete Bruhat coefficient is dominated by the canonical rational
height kernel.  The polar determinant, lattice discriminant, and positive
real-scale losses remain literal. -/
theorem norm_rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_le_height
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (t : ℚ) :
    ‖L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) t‖ ≤
      ((L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt (L.polarDeterminant.natAbs : ℝ)) ^ n *
          (Real.sqrt (min a 1))⁻¹ ^ n) *
        (Real.sqrt (rationalRankOneBruhatHeight t))⁻¹ ^ n := by
  rw [rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finite
    L (by simpa using ha) t]
  rw [norm_mul, norm_polarRealGaussian_explicit_bruhat_factor]
  calc
    (L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt ‖(a : ℂ) - (t : ℂ) * Complex.I‖)⁻¹ ^ n *
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t‖ ≤
      (L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt ‖(a : ℂ) - (t : ℂ) * Complex.I‖)⁻¹ ^ n *
        ((Real.sqrt (L.polarDeterminant.natAbs : ℝ)) ^ n *
          (Real.sqrt (t.den : ℝ))⁻¹ ^ n) := by
            gcongr
            exact
              L.norm_quadraticGaussIntegral_le_polarDeterminant_sqrt_pow_mul_inv_den_sqrt_pow t
    _ = ((L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt (L.polarDeterminant.natAbs : ℝ)) ^ n) *
        ((Real.sqrt ‖(a : ℂ) - (t : ℂ) * Complex.I‖)⁻¹ *
          (Real.sqrt (t.den : ℝ))⁻¹) ^ n := by ring
    _ ≤ ((L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt (L.polarDeterminant.natAbs : ℝ)) ^ n) *
        ((Real.sqrt (min a 1))⁻¹ *
          (Real.sqrt (rationalRankOneBruhatHeight t))⁻¹) ^ n := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity)
                (inv_sqrt_norm_mul_inv_sqrt_den_le_rationalRankOneBruhatHeight
                  ha t) n)
              (by positivity)
    _ = ((L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt (L.polarDeterminant.natAbs : ℝ)) ^ n *
          (Real.sqrt (min a 1))⁻¹ ^ n) *
        (Real.sqrt (rationalRankOneBruhatHeight t))⁻¹ ^ n := by ring

/-- Actual summability of the concrete rational Bruhat family in every rank
at least five.  In particular this theorem is established before any `tsum`
or rank-one Eisenstein functional is defined. -/
theorem summable_rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_of_rankAtLeastFive
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (hn : 5 ≤ n) :
    Summable (fun t : ℚ =>
      L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) t) := by
  apply Summable.of_norm_bounded
    ((summable_inv_sqrt_rationalRankOneBruhatHeight_pow hn).mul_left
      ((L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt (L.polarDeterminant.natAbs : ℝ)) ^ n *
        (Real.sqrt (min a 1))⁻¹ ^ n))
  intro t
  exact
    L.norm_rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_le_height
      ha t

end PositiveDefiniteIntegralLattice

end
