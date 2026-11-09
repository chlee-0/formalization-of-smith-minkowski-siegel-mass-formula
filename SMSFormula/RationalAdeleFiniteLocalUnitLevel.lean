import SMSFormula.RationalAdeleShellRepresentationNumber

/-!
# The finite local integrand at unit level

The finite local integral is the last unevaluated object at a positive integer frequency.
This file evaluates its unit-level part exactly, using only existing objects: the
integral finite adeles, the standard indicator and the existing self-duality of that
indicator.

Two facts drive everything.  The existing finite Gauss integral is identically one on the
integral finite adeles, because the phase is trivial there and the integral carrier
has mass one.  And the existing self-dual Fourier certificate says the Fourier integral of
the indicator is the indicator.  Together they give

```text
int_{A_fin} 1_Ztilde(y) psi_{-b}(y) G(y) dy = 1_Ztilde(b),
```

one at an integral frequency and zero otherwise.  As a consequence the finite L1 mass is at
least one, so it is positive as well as finite, and the existing local L1 product
decomposition is non-degenerate.

Negative scope: this is the unit-level part only.  The integral over the rest of the finite
adele ring is untouched, no Euler product is asserted, and no value of the full finite local
integral follows.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open scoped NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The integral carrier has mass one, read off the existing self-dual certificate at
the zero frequency. -/
theorem integral_rationalFiniteAdeleVectorIntegralIndicator (d : ℕ) :
    (∫ x : Fin d → RationalFiniteAdele, rationalFiniteAdeleVectorIntegralIndicator x
      ∂rationalFiniteAdeleCoordinateAddHaarMeasure d) = 1 := by
  have h := rationalFiniteAdeleCoordinate_fourierIntegral_integralIndicator d 0
  rw [Fourier.fourierIntegral_def] at h
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul] at h
  rw [h]
  exact rationalFiniteAdeleVectorIntegralIndicator_of_mem
    (fun _ => integralFiniteAdeleSubring.zero_mem)

/-- The existing finite Gauss integral is identically one on the integral finite adeles. -/
theorem rationalFiniteAdeleQuadraticGaussIntegralAt_of_mem_integral (L : PositiveDefiniteIntegralLattice n)
    {s : RationalFiniteAdele} (hs : s ∈ integralFiniteAdeleSubring) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt s = 1 := by
  have h0 :=
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt_add_integral
      L 0 s hs
  rw [zero_add] at h0
  rw [h0]
  have hphase : ∀ x : Fin n → RationalFiniteAdele,
      ((L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt 0 x :
        Circle) : ℂ) = 1 := by
    intro x
    change ((rationalFiniteAdeleFourierChar
      (0 * L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x) : Circle) : ℂ) = 1
    rw [zero_mul, AddChar.map_zero_eq_one]
    simp
  show (∫ x : Fin n → RationalFiniteAdele,
      ((L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt 0 x : Circle) : ℂ) *
        rationalFiniteAdeleVectorIntegralIndicator x
      ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) = 1
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
    rw [hphase x, one_mul])]
  exact integral_rationalFiniteAdeleVectorIntegralIndicator n

/-- The unit-level value: the finite local integrand integrated against the standard
indicator is exactly the integrality indicator of the frequency. -/
theorem integral_integralIndicator_mul_finiteLocal (L : PositiveDefiniteIntegralLattice n) (b : ℚ) :
    (∫ y : RationalFiniteAdele,
        rationalFiniteAdeleIntegralIndicator y *
          (((rationalFiniteAdeleFourierChar
              (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
            L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y)
        ∂rationalFiniteAdeleAddHaarMeasure) =
      rationalFiniteAdeleIntegralIndicator (algebraMap ℚ RationalFiniteAdele b) := by
  have hfourier := rationalFiniteAdele_fourierIntegral_integralIndicator
    (algebraMap ℚ RationalFiniteAdele b)
  rw [Fourier.fourierIntegral_def] at hfourier
  rw [← hfourier]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  have harg : algebraMap ℚ RationalFiniteAdele (-b) * y =
      -(y * algebraMap ℚ RationalFiniteAdele b) := by
    rw [map_neg, neg_mul, mul_comm]
  by_cases hy : y ∈ integralFiniteAdeleSubring
  · rw [rationalFiniteAdeleIntegralIndicator_of_mem hy,
      L.rationalFiniteAdeleQuadraticGaussIntegralAt_of_mem_integral hy, harg]
    simp [Circle.smul_def]
  · rw [rationalFiniteAdeleIntegralIndicator_of_not_mem hy]
    simp

/-- The finite L1 mass is at least one, hence positive as well as finite. -/
theorem one_le_integral_norm_finiteGaussIntegral (L : PositiveDefiniteIntegralLattice n) {scale : ℝ}
    (hscale : 0 < scale) (hrank : 5 ≤ n) :
    1 ≤ ∫ y : RationalFiniteAdele,
      ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y‖
      ∂rationalFiniteAdeleAddHaarMeasure := by
  have hindint : Integrable
      (Set.indicator (integralFiniteAdeleSubring : Set RationalFiniteAdele)
        (fun _ => (1 : ℝ))) rationalFiniteAdeleAddHaarMeasure := by
    refine (integrableOn_const (C := (1 : ℝ)) ?_).integrable_indicator ?_
    · simp
    · exact isOpen_integralFiniteAdeleSubring.measurableSet
  have hGnorm := (L.integrable_finiteGaussIntegral hscale hrank).norm
  have hle : ∀ y : RationalFiniteAdele,
      Set.indicator (integralFiniteAdeleSubring : Set RationalFiniteAdele)
        (fun _ => (1 : ℝ)) y ≤
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y‖ := by
    intro y
    by_cases hy : y ∈ integralFiniteAdeleSubring
    · rw [Set.indicator_of_mem hy,
        L.rationalFiniteAdeleQuadraticGaussIntegralAt_of_mem_integral hy]
      simp
    · rw [Set.indicator_of_notMem hy]
      exact norm_nonneg _
  have hmono := integral_mono hindint hGnorm hle
  have hone : (∫ y : RationalFiniteAdele,
      Set.indicator (integralFiniteAdeleSubring : Set RationalFiniteAdele)
        (fun _ => (1 : ℝ)) y ∂rationalFiniteAdeleAddHaarMeasure) = 1 := by
    rw [integral_indicator_const (1 : ℝ) isOpen_integralFiniteAdeleSubring.measurableSet]
    simp [measureReal_def, rationalFiniteAdeleAddHaarMeasure_integral]
  rwa [hone] at hmono

/-! ## Scaling the integration variable by a natural number -/

/-- The existing scalar Haar scaling law, in integral form. -/
theorem integral_comp_natScale_inv {m : ℕ} (hm : m ≠ 0) (F : RationalFiniteAdele → ℂ) :
    (∫ y : RationalFiniteAdele,
        F (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * y)
        ∂rationalFiniteAdeleAddHaarMeasure) =
      ((m : ℂ))⁻¹ * ∫ y : RationalFiniteAdele, F y ∂rationalFiniteAdeleAddHaarMeasure := by
  have hq : ((m : ℚ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hm)
  let hhom : RationalFiniteAdele ≃ₜ RationalFiniteAdele :=
    { toEquiv := (rationalFiniteAdeleScaleAddEquiv hq).toEquiv
      continuous_toFun := continuous_rationalFiniteAdeleScaleAddEquiv hq
      continuous_invFun := continuous_rationalFiniteAdeleScaleAddEquiv_symm hq }
  have he : MeasurableEmbedding (rationalFiniteAdeleScaleAddEquiv hq) :=
    hhom.toMeasurableEquiv.measurableEmbedding
  have hchange : (∫ y : RationalFiniteAdele,
      F (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * y)
      ∂rationalFiniteAdeleAddHaarMeasure) =
      ∫ y : RationalFiniteAdele, F y
        ∂Measure.map (rationalFiniteAdeleScaleAddEquiv hq)
          rationalFiniteAdeleAddHaarMeasure := by
    rw [he.integral_map]
    rfl
  rw [hchange, map_rationalFiniteAdeleAddHaarMeasure_scale_inv hm hq,
    integral_smul_nnreal_measure]
  have hcast : ((((m : ℝ≥0))⁻¹ : ℝ≥0) : ℝ) = ((m : ℝ))⁻¹ := by
    push_cast
    ring
  rw [NNReal.smul_def, hcast, Complex.real_smul]
  congr 1
  push_cast
  ring

/-- Scaling the integration variable up by a natural number multiplies the integral by that
number. -/
theorem integral_comp_natScale {m : ℕ} (hm : m ≠ 0) (F : RationalFiniteAdele → ℂ) :
    (∫ y : RationalFiniteAdele, F ((m : RationalFiniteAdele) * y)
        ∂rationalFiniteAdeleAddHaarMeasure) =
      (m : ℂ) * ∫ y : RationalFiniteAdele, F y ∂rationalFiniteAdeleAddHaarMeasure := by
  have hmq : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hmc : ((m : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hcancel : ∀ y : RationalFiniteAdele,
      (m : RationalFiniteAdele) * (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * y) = y := by
    intro y
    have hcast : (m : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele ((m : ℚ)) := by
      norm_num
    rw [hcast, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hmq, map_one, one_mul]
  have hkey : (∫ y : RationalFiniteAdele, F y ∂rationalFiniteAdeleAddHaarMeasure) =
      ((m : ℂ))⁻¹ * ∫ y : RationalFiniteAdele, F ((m : RationalFiniteAdele) * y)
        ∂rationalFiniteAdeleAddHaarMeasure := by
    have h := integral_comp_natScale_inv hm
      (fun u : RationalFiniteAdele => F ((m : RationalFiniteAdele) * u))
    rw [← h]
    exact (integral_congr_ae (Filter.Eventually.of_forall fun y => by
      rw [hcancel y])).symm
  rw [hkey]
  field_simp

/-- The existing self-duality, scaled: the character integral over the `m`-divided integral
finite adeles. -/
theorem integral_natScaleIndicator_mul_char {m : ℕ} (hm : m ≠ 0) (w : RationalFiniteAdele) :
    (∫ y : RationalFiniteAdele,
        rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
          ((rationalFiniteAdeleFourierChar (y * w) : Circle) : ℂ)
        ∂rationalFiniteAdeleAddHaarMeasure) =
      (m : ℂ) * rationalFiniteAdeleIntegralIndicator
        (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w) := by
  have hmq : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hcast : (m : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele ((m : ℚ)) := by
    norm_num
  have hkey := integral_comp_natScale hm (fun u : RationalFiniteAdele =>
    rationalFiniteAdeleIntegralIndicator u *
      ((rationalFiniteAdeleFourierChar
        (u * (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w)) : Circle) : ℂ))
  have hleft : ∀ y : RationalFiniteAdele,
      rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
          ((rationalFiniteAdeleFourierChar
            ((m : RationalFiniteAdele) * y *
              (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w)) : Circle) : ℂ) =
        rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
          ((rationalFiniteAdeleFourierChar (y * w) : Circle) : ℂ) := by
    intro y
    have harg : (m : RationalFiniteAdele) * y *
        (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w) = y * w := by
      rw [hcast, show algebraMap ℚ RationalFiniteAdele ((m : ℚ)) * y *
          (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w) =
          (algebraMap ℚ RationalFiniteAdele ((m : ℚ)) *
            algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹) * (y * w) from by ring,
        ← map_mul, mul_inv_cancel₀ hmq, map_one, one_mul]
    rw [harg]
  simp only [hleft] at hkey
  rw [hkey]
  congr 1
  have hdual := rationalFiniteAdele_fourierIntegral_integralIndicator
    (-(algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w))
  rw [Fourier.fourierIntegral_def] at hdual
  rw [show (∫ y : RationalFiniteAdele,
      rationalFiniteAdeleIntegralIndicator y *
        ((rationalFiniteAdeleFourierChar
          (y * (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w)) : Circle) : ℂ)
      ∂rationalFiniteAdeleAddHaarMeasure) =
      ∫ y : RationalFiniteAdele,
        rationalFiniteAdeleFourierChar
          (-(y * -(algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w))) •
          rationalFiniteAdeleIntegralIndicator y
        ∂rationalFiniteAdeleAddHaarMeasure from by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [mul_neg, neg_neg]
    simp [Circle.smul_def, mul_comm]]
  rw [hdual]
  by_cases hw : -(algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w) ∈
      integralFiniteAdeleSubring
  · have hw' : algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w ∈
        integralFiniteAdeleSubring := by
      simpa using integralFiniteAdeleSubring.neg_mem hw
    rw [rationalFiniteAdeleIntegralIndicator_of_mem hw,
      rationalFiniteAdeleIntegralIndicator_of_mem hw']
  · have hw' : algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * w ∉
        integralFiniteAdeleSubring := by
      intro h
      exact hw (integralFiniteAdeleSubring.neg_mem h)
    rw [rationalFiniteAdeleIntegralIndicator_of_not_mem hw,
      rationalFiniteAdeleIntegralIndicator_of_not_mem hw']

end PositiveDefiniteIntegralLattice
