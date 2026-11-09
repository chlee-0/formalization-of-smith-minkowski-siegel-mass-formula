import SMSFormula.RationalAdeleArchimedeanLocalIntegral

/-!
# The archimedean Bruhat factor is a literal Gaussian integral in a nonnegative value

The archimedean local integral is known to converge.  Before it can be evaluated, the
factor `detScale^{-1} (1/(c - w i)^{1/2})^n` must be turned back into something whose
frequency dependence is visible.  This file does exactly that, using only existing
constructions: the polar Gaussian, the polar square root, and the existing exact
Fourier formula for that Gaussian, evaluated at the zero frequency.

The output is
```text
detScale^{-1} (1/(c - w i)^{1/2})^n = int_{R^n} exp(-pi (c - w i) P(x)) dx,
```
where `P(x) = x . (2F) x` is the real polar value.  Because `P(x)` is the sum of
squares of the coordinates of the polar square root, it is nonnegative, so the
frequency enters only through a phase `exp(pi i w P(x))` whose argument runs over a half
line.  That one-sidedness is the actual source of the classical negative-frequency
vanishing.

Negative scope: this is a representation, not an evaluation.  No contour, no Gamma
identity, no inversion theorem and no vanishing is proved here.  No new measure, chart,
section or Haar normalization is chosen: the integral is the coordinate Lebesgue
measure on `R^n` and the formula is the existing Fourier formula at frequency zero.
-/

noncomputable section

open MeasureTheory Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The real polar value carried by the archimedean Gaussian. -/
def polarRealValue (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec x)

/-- The polar value is the sum of squares of the polar square-root coordinates. -/
theorem polarRealValue_eq_sum_sq (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℝ) :
    L.polarRealValue x = ∑ i, (L.polarRealSqrtMatrix.mulVec x i) ^ 2 := by
  rw [polarRealValue, ← L.dotProduct_polarRealSqrtMatrix_mulVec x x]
  simp [dotProduct, pow_two]

/-- The polar value is nonnegative.  This is the one-sidedness the evaluation needs. -/
theorem polarRealValue_nonneg (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℝ) :
    0 ≤ L.polarRealValue x := by
  rw [polarRealValue_eq_sum_sq]
  positivity

/-- The polar Gaussian is a single exponential in the polar value. -/
theorem polarRealGaussian_eq_exp_polarRealValue (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    (x : Fin n → ℝ) :
    polarRealGaussian L b x =
      Complex.exp (-Real.pi * b * (L.polarRealValue x : ℂ)) := by
  rw [polarRealGaussian, realCoordinateGaussian_eq_exp_dotProduct,
    L.dotProduct_polarRealSqrtMatrix_mulVec x x, polarRealValue]

/-- The existing Fourier formula at the zero frequency: the archimedean amplitude is the
literal Gaussian integral over `R^n`. -/
theorem integral_polarRealGaussian {b : ℂ} (hb : 0 < b.re) (L : PositiveDefiniteIntegralLattice n) :
    (∫ x : Fin n → ℝ, polarRealGaussian L b x) =
      (L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / b ^ (1 / 2 : ℂ)) ^ n := by
  have h := polarReal_fourierIntegral_gaussian hb L 0
  rw [Matrix.mulVec_zero, Fourier.fourierIntegral_def] at h
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul] at h
  rw [h, polarRealGaussianFourierProduct, Matrix.mulVec_zero,
    realCoordinateGaussianFourierProduct]
  simp

/-- The archimedean Bruhat factor of the standard test, as a literal Gaussian
integral whose frequency enters only through the nonnegative polar value. -/
theorem archimedeanBruhatFactor_eq_integral (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c)
    (v : ℝ) :
    (L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n =
      ∫ x : Fin n → ℝ, polarRealGaussian L ((c : ℂ) - (v : ℂ) * Complex.I) x := by
  rw [integral_polarRealGaussian (by simpa using hc) L]

/-- The frequency enters only as a phase in the nonnegative polar value. -/
theorem polarRealGaussian_sub_mul_I (L : PositiveDefiniteIntegralLattice n) (c v : ℝ) (x : Fin n → ℝ) :
    polarRealGaussian L ((c : ℂ) - (v : ℂ) * Complex.I) x =
      polarRealGaussian L (c : ℂ) x *
        Complex.exp (Real.pi * Complex.I * (v : ℂ) * (L.polarRealValue x : ℂ)) := by
  rw [polarRealGaussian_eq_exp_polarRealValue, polarRealGaussian_eq_exp_polarRealValue,
    ← Complex.exp_add]
  congr 1
  ring

/-- The modulus of the polar Gaussian at a positive real width. -/
theorem norm_polarRealGaussian_ofReal (L : PositiveDefiniteIntegralLattice n) (c : ℝ) (x : Fin n → ℝ) :
    ‖polarRealGaussian L (c : ℂ) x‖ = Real.exp (-Real.pi * c * L.polarRealValue x) := by
  rw [polarRealGaussian_eq_exp_polarRealValue, Complex.norm_exp]
  congr 1
  simp

end PositiveDefiniteIntegralLattice
