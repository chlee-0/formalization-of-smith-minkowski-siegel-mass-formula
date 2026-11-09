import SMSFormula.RationalAdeleBruhatIntegralLocalProduct

/-!
# The archimedean local integral converges, with a frequency-free bound

The cusp coefficient is a product of two local integrals.  This file supplies the
"cheaper intermediate" for the archimedean one: its integrand has modulus independent of
the frequency, that modulus is integrable on the real line in every rank at least three,
and consequently the archimedean local integral is bounded by one explicit constant for
every frequency.

The transport from the infinite adeles to `ℝ` is the existing definition of the infinite
Haar as the pushforward of Lebesgue measure; no new measure or chart is chosen.

Negative scope: this is convergence and a bound, not an evaluation.  The classical value
(zero for negative frequency, Gamma-type for positive frequency) is not proved here; that
needs either a complex-rate Gamma integral, which mathlib supplies only for a real rate, or
a contour argument.  Nothing here gives vanishing of the difference.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A natural power of an inverse square root is the existing negative half power. -/
theorem inv_sqrt_pow_eq_rpow {H : ℝ} (hH : 0 < H) (m : ℕ) :
    ((Real.sqrt H)⁻¹) ^ m = H ^ (-((m : ℝ) / 2)) := by
  rw [← Real.rpow_natCast ((Real.sqrt H)⁻¹) m, Real.sqrt_eq_rpow,
    ← Real.rpow_neg_one (H ^ (1 / 2 : ℝ)), ← Real.rpow_mul hH.le, ← Real.rpow_mul hH.le]
  congr 1
  ring

/-- The archimedean Bruhat factor has modulus independent of the frequency. -/
theorem norm_archimedeanBruhatFactor (L : PositiveDefiniteIntegralLattice n) (c w : ℝ) :
    ‖(L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / ((c : ℂ) - (w : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n‖ =
      (L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt ‖(c : ℂ) - (w : ℂ) * Complex.I‖)⁻¹ ^ n := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg
    (by exact_mod_cast L.polarRealDeterminantScale_pos.le)]
  rw [norm_pow, norm_div, norm_one,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real]
  simp only [one_div, Real.sqrt_eq_rpow]

/-- The archimedean modulus is bounded below by the existing Japanese-bracket weight. -/
theorem archimedean_norm_lower_bound {c : ℝ} (hc : 0 < c) (w : ℝ) :
    min c 1 / 2 * (1 + |w|) ≤ ‖(c : ℂ) - (w : ℂ) * Complex.I‖ := by
  have hre : c ≤ ‖(c : ℂ) - (w : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm ((c : ℂ) - (w : ℂ) * Complex.I)
    have hval : ((c : ℂ) - (w : ℂ) * Complex.I).re = c := by simp
    rw [hval, abs_of_pos hc] at h
    exact h
  have him : |w| ≤ ‖(c : ℂ) - (w : ℂ) * Complex.I‖ := by
    have h := Complex.abs_im_le_norm ((c : ℂ) - (w : ℂ) * Complex.I)
    have hval : ((c : ℂ) - (w : ℂ) * Complex.I).im = -w := by simp
    rw [hval, abs_neg] at h
    exact h
  have hmin : min c 1 * (1 + |w|) ≤ c + |w| := by
    rcases le_total c 1 with h | h
    · rw [min_eq_left h]
      nlinarith [abs_nonneg w, hc.le]
    · rw [min_eq_right h]
      nlinarith [abs_nonneg w]
  have hsum : c + |w| ≤ 2 * ‖(c : ℂ) - (w : ℂ) * Complex.I‖ := by linarith
  linarith

/-- The archimedean modulus is dominated by a constant times the existing integrable
Japanese-bracket weight. -/
theorem archimedeanBound_le {c : ℝ} (hc : 0 < c) (hn : 3 ≤ n) (w : ℝ) :
    (Real.sqrt ‖(c : ℂ) - (w : ℂ) * Complex.I‖)⁻¹ ^ n ≤
      (min c 1 / 2) ^ (-((n : ℝ) / 2)) * (1 + ‖w‖) ^ (-((n : ℝ) / 2)) := by
  have hK : 0 < min c 1 / 2 := by
    have : 0 < min c 1 := lt_min hc zero_lt_one
    linarith
  have hA : 0 < min c 1 / 2 * (1 + |w|) := by
    have : 0 < 1 + |w| := by positivity
    exact mul_pos hK this
  have hAN := archimedean_norm_lower_bound hc w
  have hN : 0 < ‖(c : ℂ) - (w : ℂ) * Complex.I‖ := lt_of_lt_of_le hA hAN
  have hexp : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
  rw [inv_sqrt_pow_eq_rpow hN]
  have hmono : ‖(c : ℂ) - (w : ℂ) * Complex.I‖ ^ (-((n : ℝ) / 2)) ≤
      (min c 1 / 2 * (1 + |w|)) ^ (-((n : ℝ) / 2)) := by
    rw [Real.rpow_neg hN.le, Real.rpow_neg hA.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hA _) (Real.rpow_le_rpow hA.le hAN hexp)
  refine hmono.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, Real.mul_rpow hK.le (by positivity)]

/-- The archimedean modulus is integrable on the real line in every rank at least three. -/
theorem integrable_archimedeanBound {c : ℝ} (hc : 0 < c) (hn : 3 ≤ n) :
    Integrable (fun w : ℝ => (Real.sqrt ‖(c : ℂ) - (w : ℂ) * Complex.I‖)⁻¹ ^ n)
      (volume : Measure ℝ) := by
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrank : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < (n : ℝ) / 2 := by
    rw [Module.finrank_self]
    push_cast
    linarith
  have hmajor : Integrable (fun w : ℝ =>
      (min c 1 / 2) ^ (-((n : ℝ) / 2)) * (1 + ‖w‖) ^ (-((n : ℝ) / 2)))
      (volume : Measure ℝ) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) hrank).const_mul _
  refine hmajor.mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have hcont : Continuous fun w : ℝ => ‖(c : ℂ) - (w : ℂ) * Complex.I‖ := by fun_prop
    exact ((Real.continuous_sqrt.comp hcont).measurable.inv).pow_const n
  · filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact archimedeanBound_le hc hn w

/-- The existing infinite Haar integral is the literal Lebesgue integral on `ℝ`. -/
theorem integral_infiniteAdele_eq_integral_real (F : RationalInfiniteAdele → ℂ) :
    (∫ w, F w ∂rationalInfiniteAdeleAddHaarMeasure) =
      ∫ v : ℝ, F (rationalInfiniteAdeleContinuousAddEquivReal.symm v) := by
  rw [rationalInfiniteAdeleAddHaarMeasure]
  exact integral_map_equiv
    rationalInfiniteAdeleContinuousAddEquivReal.symm.toHomeomorph.toMeasurableEquiv F

set_option maxHeartbeats 1000000 in
/-- The archimedean local integral is bounded by one explicit constant for every frequency:
the modulus of its integrand does not depend on the frequency at all. -/
theorem norm_archimedean_local_integral_le (L : PositiveDefiniteIntegralLattice n) (c : ℝ) (t : ℚ) :
    ‖∫ w : RationalInfiniteAdele,
        ((rationalInfiniteAdeleFourierChar
            (algebraMap ℚ RationalInfiniteAdele t * w) : Circle) : ℂ) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / ((c : ℂ) -
              ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
              Complex.I) ^ (1 / 2 : ℂ)) ^ n)
        ∂rationalInfiniteAdeleAddHaarMeasure‖ ≤
      (L.polarRealDeterminantScale : ℝ)⁻¹ *
        ∫ v : ℝ, (Real.sqrt ‖(c : ℂ) - (v : ℂ) * Complex.I‖)⁻¹ ^ n := by
  rw [integral_infiniteAdele_eq_integral_real]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpoint : ∀ v : ℝ,
      ‖((rationalInfiniteAdeleFourierChar
            (algebraMap ℚ RationalInfiniteAdele t *
              rationalInfiniteAdeleContinuousAddEquivReal.symm v) : Circle) : ℂ) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / ((c : ℂ) -
              ((rationalInfiniteAdeleContinuousAddEquivReal
                (rationalInfiniteAdeleContinuousAddEquivReal.symm v) : ℝ) : ℂ) *
              Complex.I) ^ (1 / 2 : ℂ)) ^ n)‖ =
        (L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt ‖(c : ℂ) - (v : ℂ) * Complex.I‖)⁻¹ ^ n := by
    intro v
    rw [norm_mul, Circle.norm_coe, one_mul,
      rationalInfiniteAdeleContinuousAddEquivReal.apply_symm_apply v,
      L.norm_archimedeanBruhatFactor c v]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul]

/-- The archimedean bounding constant of the cusp coefficient. -/
def archimedeanCuspBoundConstant (L : PositiveDefiniteIntegralLattice n) (c : ℝ) : ℝ :=
  (L.polarRealDeterminantScale : ℝ)⁻¹ *
    ∫ v : ℝ, (Real.sqrt ‖(c : ℂ) - (v : ℂ) * Complex.I‖)⁻¹ ^ n

theorem archimedeanCuspBoundConstant_nonneg (L : PositiveDefiniteIntegralLattice n) (c : ℝ) :
    0 ≤ L.archimedeanCuspBoundConstant c := by
  refine mul_nonneg (by positivity) (integral_nonneg fun v => by positivity)

end PositiveDefiniteIntegralLattice
