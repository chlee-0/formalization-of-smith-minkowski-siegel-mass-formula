import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The archimedean shifted-Gaussian bound

The admissibility estimate for shifted Gaussians has a finite side -- a bound at one conductor
(`FiniteQuadraticSumModulusBound`) and its sum over all conductors (`FiniteConductorSummability`) --
and an archimedean side, treated here.

The archimedean factor attached to a shifted real Gaussian of width `b > 0` at frequency `s` is a
power of `b - i s`, and its modulus is what the estimate needs.  Two facts are proved here.

Modulus.  For `b > 0` and any real exponent, `‖(b - i s)^(-n/2)‖ = (b^2 + s^2)^(-n/4)`.  The
complex power has a branch, but the exponent is real, so the `arg` contribution drops out and only
the modulus survives.

Integrability.  `(b^2 + s^2)^(-n/4)` is integrable in `s` over the line exactly when the rank
exceeds two, by scaling the Japanese-bracket estimate `(1 + ‖x‖^2)^(-r/2)` at `r = n/2`: the line
has dimension one, and that estimate needs `r > 1`.

Combining, the modulus of the archimedean factor is integrable in the frequency for rank above two.
The threshold here is two, not the four of the conductor sum -- the two sides have different
thresholds, and the rank-five hypothesis comes from the finite side, not from this one.

Negative scope: nothing here evaluates the archimedean integral, identifies the constant, or
constructs the sinc-squared triangular cutoff and its convolution cost.  No Gaussian integral is
computed; only the modulus of an assumed power is handled.
-/

namespace SMSFormula.Archimedean

open MeasureTheory Real

/-- The modulus of the archimedean factor.  For a positive width the complex power `b - i s` raised
to a real exponent has modulus `(b^2 + s^2)` to the half of that exponent; the branch contributes
nothing because the exponent has no imaginary part. -/
theorem norm_cpow_shifted (b s : ℝ) (hb : 0 < b) (r : ℝ) :
    ‖((b : ℂ) - (s : ℂ) * Complex.I) ^ (r : ℂ)‖ = (b ^ 2 + s ^ 2) ^ (r / 2) := by
  have hre : ((b : ℂ) - (s : ℂ) * Complex.I).re = b := by simp
  have him : ((b : ℂ) - (s : ℂ) * Complex.I).im = -s := by simp
  have hz : ((b : ℂ) - (s : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    exact hb.ne hre
  have hnorm : ‖((b : ℂ) - (s : ℂ) * Complex.I)‖ = (b ^ 2 + s ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him, Real.sqrt_eq_rpow]
    ring_nf
  rw [Complex.norm_cpow_of_ne_zero hz, hnorm]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.exp_zero]
  rw [← Real.rpow_mul (by positivity)]
  ring_nf

/-- The archimedean integrability, sharp at rank two.  The modulus bound is integrable in the
frequency exactly when the rank exceeds two; the line has dimension one, which is what the
Japanese-bracket estimate consumes. -/
theorem integrable_shifted_bound {n : ℕ} (hn : 2 < n) {b : ℝ} (hb : 0 < b) :
    Integrable (fun s : ℝ ↦ (b ^ 2 + s ^ 2) ^ (-(n : ℝ) / 4)) := by
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < (n : ℝ) / 2 := by
    rw [Module.finrank_self]
    have : (2 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    push_cast
    linarith
  have hbase : Integrable (fun x : ℝ ↦ ((1 : ℝ) + ‖x‖ ^ 2) ^ (-((n : ℝ) / 2) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) hr
  have hscale : Integrable (fun s : ℝ ↦ ((1 : ℝ) + ‖b⁻¹ * s‖ ^ 2) ^ (-((n : ℝ) / 2) / 2)) :=
    hbase.comp_mul_left' (inv_ne_zero hb.ne')
  have := hscale.const_mul (b ^ (-(n : ℝ) / 2))
  refine this.congr (Filter.Eventually.of_forall fun s ↦ ?_)
  show b ^ (-(n : ℝ) / 2) * ((1 : ℝ) + ‖b⁻¹ * s‖ ^ 2) ^ (-((n : ℝ) / 2) / 2) =
    (b ^ 2 + s ^ 2) ^ (-(n : ℝ) / 4)
  have hb2 : (0 : ℝ) < b ^ 2 := by positivity
  have hfactor : (b ^ 2 + s ^ 2) = b ^ 2 * (1 + ‖b⁻¹ * s‖ ^ 2) := by
    rw [Real.norm_eq_abs, sq_abs]
    field_simp
  rw [hfactor, Real.mul_rpow hb2.le (by positivity)]
  congr 1
  · rw [← Real.rpow_natCast b 2, ← Real.rpow_mul hb.le]
    congr 1
    ring
  · congr 1
    ring

/-- The two combined: the modulus of the archimedean factor is integrable in the frequency for rank
above two. -/
theorem integrable_norm_cpow_shifted {n : ℕ} (hn : 2 < n) {b : ℝ} (hb : 0 < b) :
    Integrable (fun s : ℝ ↦ ‖((b : ℂ) - (s : ℂ) * Complex.I) ^ ((-(n : ℝ) / 2 : ℝ) : ℂ)‖) := by
  refine (integrable_shifted_bound hn hb).congr (Filter.Eventually.of_forall fun s ↦ ?_)
  show (b ^ 2 + s ^ 2) ^ (-(n : ℝ) / 4) =
    ‖((b : ℂ) - (s : ℂ) * Complex.I) ^ ((-(n : ℝ) / 2 : ℝ) : ℂ)‖
  rw [norm_cpow_shifted b s hb]
  congr 1
  ring

end SMSFormula.Archimedean
