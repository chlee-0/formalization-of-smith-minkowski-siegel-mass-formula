import SMSFormula.RationalAdeleArchimedeanGaussianRepresentation

/-!
# The Gaussian-regularized archimedean integral

The archimedean Bruhat factor is a literal Gaussian integral over `R^n` in which the
frequency enters only through the nonnegative polar value `P(x)`.  This file computes the
archimedean local integral against a Gaussian regulator `exp(-pi eps v^2)`, which makes
every interchange absolutely convergent and needs no contour, no Gamma identity and no
inversion theorem.

The result is the exact identity
```text
int_R e(t v) exp(-pi eps v^2) (int_{R^n} exp(-pi (c - v i) P(x)) dx) dv
  = int_{R^n} exp(-pi c P(x)) * eps^{-1/2} exp(-pi (t + P(x)/2)^2 / eps) dx.
```

Because `P(x) >= 0`, for a positive `t` the exponent `(t + P(x)/2)^2` is bounded below by
`t^2` uniformly in `x`, so the whole regularized integral is bounded by
`eps^{-1/2} exp(-pi t^2 / eps)` times the fixed Gaussian mass.

Negative scope: this is the regularized integral, not the integral itself.  Passing to the
limit `eps -> 0` is a separate step and is not taken here.  No new measure, chart, section
or Haar normalization is introduced: both integrals are the Lebesgue measures, and the
regulator is the existing mathlib Gaussian.
-/

noncomputable section

open MeasureTheory Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

theorem continuous_polarRealValue (L : PositiveDefiniteIntegralLattice n) : Continuous L.polarRealValue := by
  unfold polarRealValue
  simp only [dotProduct, Matrix.mulVec]
  exact continuous_finset_sum _ fun i _ =>
    (continuous_apply i).mul
      (continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j))

/-- The existing mathlib Gaussian Fourier formula, in the shape the regulator needs. -/
theorem integral_gaussianRegulator {ε : ℝ} (hε : 0 < ε) (t p : ℝ) :
    (∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
        Complex.exp (Real.pi * Complex.I * (v : ℂ) * (p : ℂ))) =
      (((Real.sqrt ε)⁻¹ : ℝ) : ℂ) *
        Complex.exp (((-Real.pi * (t + p / 2) ^ 2 / ε : ℝ) : ℂ)) := by
  have hB : (0 : ℝ) < ((((Real.pi * ε : ℝ)) : ℂ)).re := by
    simpa using mul_pos Real.pi_pos hε
  have hcomb : ∀ v : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
          Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
          Complex.exp (Real.pi * Complex.I * (v : ℂ) * (p : ℂ)) =
        Complex.exp (Complex.I * (((2 * Real.pi * (t + p / 2) : ℝ)) : ℂ) * (v : ℂ)) *
          Complex.exp (-(((Real.pi * ε : ℝ)) : ℂ) * (v : ℂ) ^ 2) := by
    intro v
    rw [show Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
          Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
          Complex.exp (Real.pi * Complex.I * (v : ℂ) * (p : ℂ)) =
        (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
          Complex.exp (Real.pi * Complex.I * (v : ℂ) * (p : ℂ))) *
          Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) from by ring,
      ← Complex.exp_add]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  simp_rw [hcomb]
  rw [fourierIntegral_gaussian hB (((2 * Real.pi * (t + p / 2) : ℝ)) : ℂ)]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  congr 1
  · rw [show ((Real.pi : ℂ) / (((Real.pi * ε : ℝ)) : ℂ)) = (((ε⁻¹ : ℝ)) : ℂ) by
      push_cast
      field_simp,
      show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity)]
    norm_cast
    rw [← Real.sqrt_eq_rpow, Real.sqrt_inv]
  · congr 1
    push_cast
    field_simp
    ring

/-- The modulus of the regularized archimedean integrand separates by variable. -/
theorem norm_regularizedArchimedeanIntegrand (L : PositiveDefiniteIntegralLattice n) (c ε t v : ℝ)
    (x : Fin n → ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
        polarRealGaussian L ((c : ℂ) - (v : ℂ) * Complex.I) x‖ =
      Real.exp (-(Real.pi * ε) * v ^ 2) *
        Real.exp (-Real.pi * c * L.polarRealValue x) := by
  rw [norm_mul, norm_mul, polarRealGaussian_sub_mul_I, norm_mul,
    norm_polarRealGaussian_ofReal]
  have h1 : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have h2 : ‖Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2)‖ =
      Real.exp (-(Real.pi * ε) * v ^ 2) := by
    have hcast : (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) =
        ((-(Real.pi * ε) * v ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_exp, Complex.ofReal_re]
  have h3 : ‖Complex.exp (Real.pi * Complex.I * (v : ℂ) *
      (L.polarRealValue x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [h1, h2, h3]
  ring

/-- The existing Gaussian mass of the polar Gaussian, as a real integrand. -/
theorem integrable_polarRealGaussianNorm (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-Real.pi * c * L.polarRealValue x))
      (volume : Measure (Fin n → ℝ)) := by
  have h := (integrable_polarRealGaussian (b := (c : ℂ)) (by simpa using hc) L).norm
  simpa only [norm_polarRealGaussian_ofReal] using h

/-- The regularized integrand is absolutely integrable on the product, so the interchange
below needs no uniformity assumption. -/
theorem integrable_uncurry_regularizedArchimedean (L : PositiveDefiniteIntegralLattice n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (t : ℝ) :
    Integrable (Function.uncurry fun (v : ℝ) (x : Fin n → ℝ) =>
        Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
          Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
          polarRealGaussian L ((c : ℂ) - (v : ℂ) * Complex.I) x)
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  have hmaj : Integrable (fun z : ℝ × (Fin n → ℝ) =>
      Real.exp (-(Real.pi * ε) * z.1 ^ 2) *
        Real.exp (-Real.pi * c * L.polarRealValue z.2))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
    (integrable_exp_neg_mul_sq (by positivity)).mul_prod
      (integrable_polarRealGaussianNorm L hc)
  refine hmaj.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have hrw : (Function.uncurry fun (v : ℝ) (x : Fin n → ℝ) =>
        Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
          Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
          polarRealGaussian L ((c : ℂ) - (v : ℂ) * Complex.I) x) =
        fun z : ℝ × (Fin n → ℝ) =>
          Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (z.1 : ℂ)) *
            Complex.exp (-Real.pi * (ε : ℂ) * (z.1 : ℂ) ^ 2) *
            Complex.exp (-Real.pi * ((c : ℂ) - (z.1 : ℂ) * Complex.I) *
              (L.polarRealValue z.2 : ℂ)) := by
      funext z
      rw [Function.uncurry_apply_pair, polarRealGaussian_eq_exp_polarRealValue]
    rw [hrw]
    have hP : Continuous fun z : ℝ × (Fin n → ℝ) => (L.polarRealValue z.2 : ℝ) :=
      L.continuous_polarRealValue.comp continuous_snd
    fun_prop
  · filter_upwards with z
    obtain ⟨v, x⟩ := z
    rw [Function.uncurry_apply_pair, norm_regularizedArchimedeanIntegrand]

set_option maxHeartbeats 1000000 in
/-- The exact regularized archimedean integral: a single absolutely convergent interchange
turns it into a Gaussian integral over `R^n` with a nonnegative shift. -/
theorem integral_regularizedArchimedean_eq (L : PositiveDefiniteIntegralLattice n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (t : ℝ) :
    (∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) =
      ∫ x : Fin n → ℝ, polarRealGaussian L (c : ℂ) x *
        ((((Real.sqrt ε)⁻¹ : ℝ) : ℂ) *
          Complex.exp
            (((-Real.pi * (t + L.polarRealValue x / 2) ^ 2 / ε : ℝ) : ℂ))) := by
  have hpull : ∀ v : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
          Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n) =
        ∫ x : Fin n → ℝ,
          Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
            Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
            polarRealGaussian L ((c : ℂ) - (v : ℂ) * Complex.I) x := by
    intro v
    rw [archimedeanBruhatFactor_eq_integral L hc v, integral_const_mul]
  simp_rw [hpull]
  rw [integral_integral_swap (integrable_uncurry_regularizedArchimedean L hc hε t)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hinner : ∀ v : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
          Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
          polarRealGaussian L ((c : ℂ) - (v : ℂ) * Complex.I) x =
        polarRealGaussian L (c : ℂ) x *
          (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
            Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
            Complex.exp (Real.pi * Complex.I * (v : ℂ) *
              (L.polarRealValue x : ℂ))) := by
    intro v
    rw [polarRealGaussian_sub_mul_I]
    ring
  simp_rw [hinner]
  rw [integral_const_mul, integral_gaussianRegulator hε t (L.polarRealValue x)]

set_option maxHeartbeats 1000000 in
/-- For a positive frequency parameter the regularized archimedean integral is bounded by
`eps^{-1/2} exp(-pi t^2 / eps)` times the fixed Gaussian mass.  This is where the
nonnegativity of the polar value is used. -/
theorem norm_integral_regularizedArchimedean_le (L : PositiveDefiniteIntegralLattice n) {c ε t : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (ht : 0 < t) :
    ‖∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)‖ ≤
      (Real.sqrt ε)⁻¹ * Real.exp (-Real.pi * t ^ 2 / ε) *
        ∫ x : Fin n → ℝ, Real.exp (-Real.pi * c * L.polarRealValue x) := by
  rw [integral_regularizedArchimedean_eq L hc hε t]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : ∀ x : Fin n → ℝ,
      ‖polarRealGaussian L (c : ℂ) x *
          ((((Real.sqrt ε)⁻¹ : ℝ) : ℂ) *
            Complex.exp
              (((-Real.pi * (t + L.polarRealValue x / 2) ^ 2 / ε : ℝ) : ℂ)))‖ ≤
        ((Real.sqrt ε)⁻¹ * Real.exp (-Real.pi * t ^ 2 / ε)) *
          Real.exp (-Real.pi * c * L.polarRealValue x) := by
    intro x
    rw [norm_mul, norm_mul, norm_polarRealGaussian_ofReal, Complex.norm_real,
      Complex.norm_exp, Complex.ofReal_re,
      Real.norm_of_nonneg (by positivity)]
    have hsq : t ^ 2 ≤ (t + L.polarRealValue x / 2) ^ 2 := by
      have hP := L.polarRealValue_nonneg x
      nlinarith
    have hexp : Real.exp (-Real.pi * (t + L.polarRealValue x / 2) ^ 2 / ε) ≤
        Real.exp (-Real.pi * t ^ 2 / ε) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff_of_pos_right hε]
      nlinarith [Real.pi_pos]
    have hsqrt : (0 : ℝ) ≤ (Real.sqrt ε)⁻¹ := by positivity
    have hEc : (0 : ℝ) ≤ Real.exp (-Real.pi * c * L.polarRealValue x) :=
      (Real.exp_pos _).le
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hsqrt) hEc).trans
      (le_of_eq (by ring))
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
    ((integrable_polarRealGaussianNorm L hc).const_mul _)
    (Filter.Eventually.of_forall hbound)).trans ?_
  rw [integral_const_mul]

end PositiveDefiniteIntegralLattice
