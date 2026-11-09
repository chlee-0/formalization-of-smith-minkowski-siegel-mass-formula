import SMSFormula.RationalAdeleFourierFiniteMeasureExt
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

theorem rationalAdele_real_ae_zero_of_integral_fourierChar_mul_eq_zero
    {measure : Measure RationalAdele} [SigmaFinite measure]
    {density : RationalAdele → ℝ} (hdensity : Integrable density measure)
    (hzero : ∀ frequency : RationalAdele,
      ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) * density value ∂measure = 0) :
    density =ᵐ[measure] 0 := by
  let positive := measure.withDensity (fun value => ENNReal.ofReal (density value))
  let negative := measure.withDensity (fun value => ENNReal.ofReal (-density value))
  letI : IsFiniteMeasure positive := isFiniteMeasure_withDensity_ofReal hdensity.hasFiniteIntegral
  letI : IsFiniteMeasure negative :=
    isFiniteMeasure_withDensity_ofReal hdensity.neg.hasFiniteIntegral
  have hphase (test : RationalAdele → ℝ) (htest : Integrable test measure)
      (frequency : RationalAdele) :
      Integrable (fun value => (rationalAdeleFourierChar (frequency * value) : ℂ) *
        (test value : ℂ)) measure := by
    exact htest.ofReal.bdd_mul
      (rationalAdeleBoundedFourierChar frequency).continuous.aestronglyMeasurable
      (by filter_upwards [] with value; exact le_of_eq (Circle.norm_coe _))
  have heq : positive = negative := by
    apply rationalAdele_measure_eq_of_integral_fourierChar_eq
    intro frequency
    dsimp only [positive, negative]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hdensity.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (by filter_upwards [] with value; exact ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀
      (f := fun value => ENNReal.ofReal (-density value))
      hdensity.aestronglyMeasurable.aemeasurable.neg.ennreal_ofReal
      (by filter_upwards [] with value; exact ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', Complex.real_smul]
    have hswap (amount : ℝ) (value : RationalAdele) :
        (amount : ℂ) * (rationalAdeleFourierChar (frequency * value) : ℂ) =
          (rationalAdeleFourierChar (frequency * value) : ℂ) * amount := mul_comm _ _
    simp_rw [hswap]
    apply sub_eq_zero.mp
    have hnegative := hphase _ hdensity.neg.pos_part frequency
    change Integrable (fun value => (rationalAdeleFourierChar (frequency * value) : ℂ) *
      ((max (-density value) 0 : ℝ) : ℂ)) measure at hnegative
    rw [← integral_sub (hphase _ hdensity.pos_part frequency) hnegative]
    convert hzero frequency using 1
    congr 1
    funext value
    rw [← mul_sub, ← Complex.ofReal_sub]
    congr 2
    rcases le_total 0 (density value) with hnonneg | hnonpos
    · rw [max_eq_left hnonneg, max_eq_right (neg_nonpos.mpr hnonneg), sub_zero]
    · rw [max_eq_right hnonpos, max_eq_left (neg_nonneg.mpr hnonpos)]
      ring
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hdensity.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hdensity.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp heq
  filter_upwards [hae] with value hvalue
  have hreal := congrArg ENNReal.toReal hvalue
  simp only [ENNReal.toReal_ofReal'] at hreal
  change max (density value) 0 = max (-density value) 0 at hreal
  change density value = 0
  rcases le_total 0 (density value) with hnonneg | hnonpos
  · simpa only [max_eq_left hnonneg, max_eq_right (neg_nonpos.mpr hnonneg)] using hreal
  · rw [max_eq_right hnonpos, max_eq_left (neg_nonneg.mpr hnonpos)] at hreal
    linarith

theorem rationalAdele_complex_ae_zero_of_integral_fourierChar_mul_eq_zero
    {measure : Measure RationalAdele} [SigmaFinite measure]
    {density : RationalAdele → ℂ} (hdensity : Integrable density measure)
    (hzero : ∀ frequency : RationalAdele,
      ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) * density value ∂measure = 0) :
    density =ᵐ[measure] 0 := by
  have hconjugateIntegrable : Integrable (fun value => star (density value)) measure :=
    (@RCLike.conjLIE ℂ _).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hdensity
  have hphase (test : RationalAdele → ℂ) (htest : Integrable test measure)
      (frequency : RationalAdele) :
      Integrable (fun value => (rationalAdeleFourierChar (frequency * value) : ℂ) *
        test value) measure := by
    exact htest.bdd_mul
      (rationalAdeleBoundedFourierChar frequency).continuous.aestronglyMeasurable
      (by filter_upwards [] with value; exact le_of_eq (Circle.norm_coe _))
  have hconjugate (frequency : RationalAdele) :
      ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) *
        star (density value) ∂measure = 0 := by
    have heq := congrArg (starRingEnd ℂ) (hzero (-frequency))
    rw [← integral_conj] at heq
    convert heq using 1
    · congr 1
      funext value
      simp only [map_mul, neg_mul, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj,
        Complex.star_def, starRingEnd_self_apply]
    · simp
  have hreal : (fun value => (density value).re) =ᵐ[measure] 0 := by
    apply rationalAdele_real_ae_zero_of_integral_fourierChar_mul_eq_zero hdensity.re
    intro frequency
    change (∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) *
      ((density value).re : ℂ) ∂measure) = 0
    simp_rw [Complex.re_eq_add_conj, ← mul_div_assoc, mul_add, starRingEnd_apply]
    rw [integral_div, integral_add (hphase _ hdensity frequency)
      (hphase _ hconjugateIntegrable frequency), hzero, hconjugate]
    simp
  have himaginary : (fun value => (density value).im) =ᵐ[measure] 0 := by
    apply rationalAdele_real_ae_zero_of_integral_fourierChar_mul_eq_zero hdensity.im
    intro frequency
    change (∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) *
      ((density value).im : ℂ) ∂measure) = 0
    simp_rw [Complex.im_eq_sub_conj, ← mul_div_assoc, mul_sub, starRingEnd_apply]
    rw [integral_div, integral_sub (hphase _ hdensity frequency)
      (hphase _ hconjugateIntegrable frequency), hzero, hconjugate]
    simp
  filter_upwards [hreal, himaginary] with value hreal himaginary
  exact Complex.ext hreal himaginary

end PositiveDefiniteIntegralLattice
