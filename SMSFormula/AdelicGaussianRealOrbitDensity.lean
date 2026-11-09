import SMSFormula.AdelicGaussianResidueRestrictedReplacement
import SMSFormula.RationalAdeleArchimedeanLocalIntegralValue
import SMSFormula.RationalAdeleArchimedeanGaussianRepresentation
import SMSFormula.RationalAdeleRankOneAdelicBruhatFactorization
import SMSFormula.PolarGaussianQuadraticIdentification

/-!
# The archimedean density of the orbit test, in closed form

The real factor of the orbit test is `e^{2πb a_∞}·G_b` with `G_b` the polar Gaussian.  Its
real Bruhat coefficient is `B(s) = e^{2πb a_∞} · detScale⁻¹ · (1/(b − s i)^{1/2})^N` (phase
shift `e(sQ)·G_b = G_{b−si}` and the Gaussian integral), and the closed-form archimedean
local density then gives, for `a_∞ > 0` and `N ≥ 3`,

`d_∞(a) = detScale⁻¹ · (2π)^{N/2} / Γ(N/2) · a_∞^{N/2 − 1}`,

Independent of the width `b` (the factor `e^{2πb a_∞}` cancels `e^{−2πb a_∞}`).  This is the real
Leray mass of the sphere `{Q = a_∞}`, the archimedean factor of the explicit shell weight.
Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped Real

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The real Bruhat coefficient of the orbit test's real factor. -/
theorem realLocalBruhatCoefficient_gaussianOrbitTestRealFactor (L : PositiveDefiniteIntegralLattice n) {b : ℝ}
    (hb : 0 < b) (a : RationalAdele) (s : ℝ) :
    L.rationalQuadraticSpaceMatrix.realLocalBruhatCoefficient (gaussianOrbitTestRealFactor L b a) s =
      ((Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) : ℝ) : ℂ) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((b : ℂ) - (s : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n) := by
  have hG : ∀ y, ((realShiftedGaussian L b 0 y : ℝ) : ℂ) = polarRealGaussian L (b : ℂ) y := by
    intro y
    simp only [realShiftedGaussian, sub_zero, polarRealGaussian_eq_quadraticShiftedGaussian,
      Complex.ofReal_re]
  have hint : ∀ y, ((Real.fourierChar (s * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue y)
        : Circle) : ℂ) * gaussianOrbitTestRealFactor L b a y =
      ((Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) : ℝ) : ℂ) *
        polarRealGaussian L ((b : ℂ) - (s : ℂ) * Complex.I) y := by
    intro y
    rw [gaussianOrbitTestRealFactor, Complex.ofReal_mul, hG, mul_left_comm,
      realQuadraticPhase_mul_polarRealGaussian_real]
  rw [realLocalBruhatCoefficient]
  simp_rw [hint]
  rw [integral_const_mul, integral_polarRealGaussian (by simpa using hb) L]

/-- The archimedean density of the orbit test, in closed form and width-free:
`d_∞(a) = detScale⁻¹ (2π)^{N/2}/Γ(N/2) · a_∞^{N/2−1}` for `a_∞ > 0`, `N ≥ 3`. -/
theorem realLocalValueDensity_gaussianOrbitTestRealFactor (L : PositiveDefiniteIntegralLattice n) {b : ℝ}
    (hb : 0 < b) (hn : 3 ≤ n) (a : RationalAdele) (ha : 0 < rationalAdeleRealScalar a) :
    L.rationalQuadraticSpaceMatrix.realLocalValueDensity (gaussianOrbitTestRealFactor L b a)
        (rationalAdeleRealScalar a) =
      (((L.polarRealDeterminantScale : ℝ)⁻¹ *
        ((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
        (rationalAdeleRealScalar a) ^ ((n : ℝ) / 2 - 1) : ℝ) : ℂ) := by
  set t := rationalAdeleRealScalar a with htdef
  have hE : ∀ s : ℝ, ((Real.fourierChar (-(s * t)) : Circle) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * ((-t : ℝ) : ℂ) * (s : ℂ)) := by
    intro s
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [realLocalValueDensity]
  simp_rw [realLocalBruhatCoefficient_gaussianOrbitTestRealFactor L hb a, hE]
  have hswap : ∀ s : ℝ, Complex.exp (2 * Real.pi * Complex.I * ((-t : ℝ) : ℂ) * (s : ℂ)) *
      (((Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) : ℝ) : ℂ) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((b : ℂ) - (s : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) =
      ((Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) : ℝ) : ℂ) *
        (Complex.exp (2 * Real.pi * Complex.I * ((-t : ℝ) : ℂ) * (s : ℂ)) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / ((b : ℂ) - (s : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) := fun s ↦ by ring
  simp_rw [hswap]
  rw [integral_const_mul, integral_archimedeanBruhatFactor_eq_value L hb hn (by linarith : -t < 0)]
  have ht' : rationalInfiniteAdeleContinuousAddEquivReal a.1 = t := rfl
  rw [ht', ← Complex.ofReal_mul]
  congr 1
  rw [neg_neg]
  have hexp : Real.exp (Real.pi * b * (2 * t)) * Real.exp (-(2 * Real.pi * b) * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc Real.exp (Real.pi * b * (2 * t)) *
        ((L.polarRealDeterminantScale : ℝ)⁻¹ * ((2 * Real.pi) ^ ((n : ℝ) / 2) /
          Real.Gamma ((n : ℝ) / 2)) * t ^ ((n : ℝ) / 2 - 1) *
          Real.exp (-(2 * Real.pi * b) * t)) =
      ((L.polarRealDeterminantScale : ℝ)⁻¹ * ((2 * Real.pi) ^ ((n : ℝ) / 2) /
          Real.Gamma ((n : ℝ) / 2)) * t ^ ((n : ℝ) / 2 - 1)) *
        (Real.exp (Real.pi * b * (2 * t)) * Real.exp (-(2 * Real.pi * b) * t)) := by ring
    _ = _ := by rw [hexp, mul_one]

/-- The real part used in the explicit shell weight. -/
theorem re_realLocalValueDensity_gaussianOrbitTestRealFactor (L : PositiveDefiniteIntegralLattice n) {b : ℝ}
    (hb : 0 < b) (hn : 3 ≤ n) (a : RationalAdele) (ha : 0 < rationalAdeleRealScalar a) :
    (L.rationalQuadraticSpaceMatrix.realLocalValueDensity (gaussianOrbitTestRealFactor L b a)
        (rationalAdeleRealScalar a)).re =
      (L.polarRealDeterminantScale : ℝ)⁻¹ *
        ((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
        (rationalAdeleRealScalar a) ^ ((n : ℝ) / 2 - 1) := by
  rw [realLocalValueDensity_gaussianOrbitTestRealFactor L hb hn a ha, Complex.ofReal_re]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
