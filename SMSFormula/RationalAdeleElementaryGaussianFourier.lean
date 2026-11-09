import SMSFormula.RationalAdeleAdditiveSelfDualHaar
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# An elementary separating Fourier test on the rational adeles

This file combines a scaled real Gaussian with the standard finite-adelic
integral-lattice indicator.  For the already fixed global character and
additive Haar measure, its Fourier integral is computed directly from the
real Gaussian formula, the finite indicator formula, and Fubini.

The scale `4` gives a concrete test whose value at zero is `1`, while the
value at zero of its Fourier integral is `1 / 2`.  No abstract
Schwartz--Bruhat space, duality theorem, or Haar rescaling is introduced.
-/

noncomputable section

open MeasureTheory Set
open scoped FourierTransform
open Complex hiding exp

namespace PositiveDefiniteIntegralLattice

/-! ## The transported real Gaussian -/

/-- The complex Gaussian of scale `b` on the rational infinite adele. -/
def rationalInfiniteAdeleGaussian
    (b : ℂ) (x : RationalInfiniteAdele) : ℂ :=
  cexp (-Real.pi * b *
    (rationalInfiniteAdeleContinuousAddEquivReal x : ℂ) ^ 2)

private theorem integrable_real_gaussian
    {b : ℂ} (hb : 0 < b.re) :
    Integrable
      (fun x : ℝ => cexp (-Real.pi * b * (x : ℂ) ^ 2)) := by
  have hpi : 0 < ((Real.pi : ℂ) * b).re := by
    simpa using mul_pos Real.pi_pos hb
  simpa [mul_assoc] using integrable_cexp_quadratic hpi 0 0

/-- A positive-real-part Gaussian is integrable for the transported standard
real Haar measure. -/
theorem integrable_rationalInfiniteAdeleGaussian
    {b : ℂ} (hb : 0 < b.re) :
    Integrable (rationalInfiniteAdeleGaussian b)
      rationalInfiniteAdeleAddHaarMeasure := by
  rw [rationalInfiniteAdeleAddHaarMeasure]
  change Integrable (rationalInfiniteAdeleGaussian b)
    (Measure.map
      rationalInfiniteAdeleContinuousAddEquivReal.symm.toMeasurableEquiv
      (volume : Measure ℝ))
  rw [integrable_map_equiv]
  have hfunction :
      rationalInfiniteAdeleGaussian b ∘
          rationalInfiniteAdeleContinuousAddEquivReal.symm.toMeasurableEquiv =
        (fun x : ℝ => cexp (-Real.pi * b * (x : ℂ) ^ 2)) := by
    funext x
    have hsymm :
        rationalInfiniteAdeleContinuousAddEquivReal.symm.toMeasurableEquiv x =
          rationalInfiniteAdeleContinuousAddEquivReal.symm x := rfl
    rw [Function.comp_apply, hsymm]
    simp only [rationalInfiniteAdeleGaussian,
      rationalInfiniteAdeleContinuousAddEquivReal.apply_symm_apply]
  rw [hfunction]
  exact integrable_real_gaussian hb

/-- The exact Fourier integral of the transported real Gaussian. -/
theorem rationalInfiniteAdele_fourierIntegral_gaussian
    {b : ℂ} (hb : 0 < b.re) (w : RationalInfiniteAdele) :
    Fourier.fourierIntegral rationalInfiniteAdeleFourierChar
        rationalInfiniteAdeleAddHaarMeasure
        (rationalInfiniteAdeleGaussian b) w =
      1 / b ^ (1 / 2 : ℂ) *
        cexp (-Real.pi / b *
          (rationalInfiniteAdeleContinuousAddEquivReal w : ℂ) ^ 2) := by
  rw [Fourier.fourierIntegral_def,
    rationalInfiniteAdeleAddHaarMeasure]
  change (∫ v : RationalInfiniteAdele,
      rationalInfiniteAdeleFourierChar (-(v * w)) •
        rationalInfiniteAdeleGaussian b v
      ∂Measure.map
        rationalInfiniteAdeleContinuousAddEquivReal.symm.toMeasurableEquiv
        (volume : Measure ℝ)) = _
  rw [integral_map_equiv
    rationalInfiniteAdeleContinuousAddEquivReal.symm.toMeasurableEquiv]
  have hsymm (x : ℝ) :
      rationalInfiniteAdeleContinuousAddEquivReal.symm.toMeasurableEquiv x =
        rationalInfiniteAdeleContinuousAddEquivReal.symm x := rfl
  have hmul (x y : RationalInfiniteAdele) :
      rationalInfiniteAdeleContinuousAddEquivReal (x * y) =
        rationalInfiniteAdeleContinuousAddEquivReal x *
          rationalInfiniteAdeleContinuousAddEquivReal y := by
    exact rationalInfiniteAdeleRingEquivReal.map_mul x y
  simp_rw [hsymm]
  simp only [rationalInfiniteAdeleFourierChar_apply,
    map_neg, hmul,
    rationalInfiniteAdeleContinuousAddEquivReal.apply_symm_apply,
    rationalInfiniteAdeleGaussian, Circle.smul_def, smul_eq_mul]
  have h := congrFun (fourier_gaussian_pi hb)
    (rationalInfiniteAdeleContinuousAddEquivReal w)
  rw [Real.fourier_real_eq] at h
  simpa only [Circle.smul_def, smul_eq_mul] using h

/-! ## The full elementary adelic test -/

/-- A scaled real Gaussian times the indicator of the everywhere-integral
finite adeles. -/
def rationalAdeleGaussianIntegralTest
    (b : ℂ) (x : RationalAdele) : ℂ :=
  rationalInfiniteAdeleGaussian b x.1 *
    rationalFiniteAdeleIntegralIndicator x.2

/-- The elementary full-adelic Gaussian test is integrable. -/
theorem integrable_rationalAdeleGaussianIntegralTest
    {b : ℂ} (hb : 0 < b.re) :
    Integrable (rationalAdeleGaussianIntegralTest b)
      rationalAdeleAddHaarMeasure := by
  rw [rationalAdeleAddHaarMeasure_eq_prod]
  exact (integrable_rationalInfiniteAdeleGaussian hb).mul_prod
    integrable_rationalFiniteAdeleIntegralIndicator

set_option backward.isDefEq.respectTransparency false in
/-- The exact Fourier formula for the elementary Gaussian times finite-lattice
indicator test. -/
theorem rationalAdele_fourierIntegral_gaussianIntegralTest
    {b : ℂ} (hb : 0 < b.re) (w : RationalAdele) :
    Fourier.fourierIntegral rationalAdeleFourierChar
        rationalAdeleAddHaarMeasure
        (rationalAdeleGaussianIntegralTest b) w =
      (1 / b ^ (1 / 2 : ℂ) *
        cexp (-Real.pi / b *
          (rationalInfiniteAdeleContinuousAddEquivReal w.1 : ℂ) ^ 2)) *
        rationalFiniteAdeleIntegralIndicator w.2 := by
  rw [Fourier.fourierIntegral_def,
    rationalAdeleAddHaarMeasure_eq_prod]
  have hintegrand :
      (fun v : RationalAdele =>
        rationalAdeleFourierChar (-(v * w)) •
          rationalAdeleGaussianIntegralTest b v) =
      (fun v : RationalInfiniteAdele × RationalFiniteAdele =>
        (rationalInfiniteAdeleFourierChar (-(v.1 * w.1)) •
          rationalInfiniteAdeleGaussian b v.1) *
        (rationalFiniteAdeleFourierChar (-(v.2 * w.2)) •
          rationalFiniteAdeleIntegralIndicator v.2)) := by
    funext v
    change
      (rationalInfiniteAdeleFourierChar (-(v.1 * w.1)) *
          rationalFiniteAdeleFourierChar (-(v.2 * w.2))) •
            (rationalInfiniteAdeleGaussian b v.1 *
              rationalFiniteAdeleIntegralIndicator v.2) = _
    simp only [Circle.smul_def, smul_eq_mul, Circle.coe_mul]
    ring
  rw [hintegrand]
  rw [MeasureTheory.integral_prod_mul
    (μ := rationalInfiniteAdeleAddHaarMeasure)
    (ν := rationalFiniteAdeleAddHaarMeasure)
    (fun v : RationalInfiniteAdele =>
      rationalInfiniteAdeleFourierChar (-(v * w.1)) •
        rationalInfiniteAdeleGaussian b v)
    (fun v : RationalFiniteAdele =>
      rationalFiniteAdeleFourierChar (-(v * w.2)) •
        rationalFiniteAdeleIntegralIndicator v)]
  rw [← Fourier.fourierIntegral_def,
    ← Fourier.fourierIntegral_def]
  rw [rationalInfiniteAdele_fourierIntegral_gaussian hb w.1]
  simp

/-! ## A test separating the two zero values -/

/-- The scale-four elementary test.  This non-self-dual scale is chosen so
that its value at zero differs from the Fourier-integral value at zero. -/
def rationalAdeleSeparatingGaussianTest : RationalAdele → ℂ :=
  rationalAdeleGaussianIntegralTest 4

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem rationalAdeleSeparatingGaussianTest_zero :
    rationalAdeleSeparatingGaussianTest 0 = 1 := by
  simp [rationalAdeleSeparatingGaussianTest,
    rationalAdeleGaussianIntegralTest, rationalInfiniteAdeleGaussian]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem rationalAdele_fourierIntegral_separatingGaussianTest_zero :
    Fourier.fourierIntegral rationalAdeleFourierChar
      rationalAdeleAddHaarMeasure rationalAdeleSeparatingGaussianTest 0 =
        1 / 2 := by
  rw [show rationalAdeleSeparatingGaussianTest =
      rationalAdeleGaussianIntegralTest 4 by rfl,
    rationalAdele_fourierIntegral_gaussianIntegralTest
      (b := (4 : ℂ)) (by norm_num)]
  have hhalfPower : (4 : ℂ) ^ (2⁻¹ : ℂ) = 2 := by
    convert Complex.sq_cpow_two_inv (x := (2 : ℂ)) (by norm_num) using 1
    all_goals norm_num
  simp [hhalfPower]

/-- The scale-four test separates evaluation at zero from evaluation at zero
after Fourier integration. -/
theorem rationalAdeleSeparatingGaussianTest_zero_ne_fourierIntegral_zero :
    rationalAdeleSeparatingGaussianTest 0 ≠
      Fourier.fourierIntegral rationalAdeleFourierChar
        rationalAdeleAddHaarMeasure rationalAdeleSeparatingGaussianTest 0 := by
  rw [rationalAdeleSeparatingGaussianTest_zero,
    rationalAdele_fourierIntegral_separatingGaussianTest_zero]
  norm_num

end PositiveDefiniteIntegralLattice
