import SMSFormula.RationalAdeleFourierIntegrableUniqueness
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

theorem rationalAdele_real_density_of_character_pairings
    {reference target : Measure RationalAdele} [IsFiniteMeasure target]
    {density : RationalAdele → ℝ} (hmeasurable : Measurable density)
    (hintegrable : Integrable density reference)
    (hpairing : ∀ frequency : RationalAdele,
      ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) * density value ∂reference =
        ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) ∂target) :
    (∀ᵐ value ∂reference, 0 ≤ density value) ∧
      reference.withDensity (fun value => ENNReal.ofReal (density value)) = target := by
  let positive := reference.withDensity (fun value => ENNReal.ofReal (density value))
  let negative := reference.withDensity (fun value => ENNReal.ofReal (-density value))
  letI : IsFiniteMeasure positive := isFiniteMeasure_withDensity_ofReal hintegrable.hasFiniteIntegral
  letI : IsFiniteMeasure negative := isFiniteMeasure_withDensity_ofReal hintegrable.neg.hasFiniteIntegral
  have hphase (test : RationalAdele → ℝ) (htest : Integrable test reference)
      (frequency : RationalAdele) :
      Integrable (fun value => (rationalAdeleFourierChar (frequency * value) : ℂ) *
        (test value : ℂ)) reference :=
    htest.ofReal.bdd_mul (rationalAdeleBoundedFourierChar frequency).continuous.aestronglyMeasurable
      (by filter_upwards [] with value; exact le_of_eq (Circle.norm_coe _))
  have hbalance : positive = target + negative := by
    apply rationalAdele_measure_eq_of_integral_fourierChar_eq
    intro frequency
    rw [integral_add_measure
      (f := fun value => (rationalAdeleFourierChar (frequency * value) : ℂ))
      (BoundedContinuousFunction.integrable target (rationalAdeleBoundedFourierChar frequency))
      (BoundedContinuousFunction.integrable negative (rationalAdeleBoundedFourierChar frequency))]
    apply sub_eq_iff_eq_add.mp
    dsimp only [positive, negative]
    rw [integral_withDensity_eq_integral_toReal_smul hmeasurable.ennreal_ofReal
      (by filter_upwards [] with value; exact ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul
      (f := fun value => ENNReal.ofReal (-density value)) hmeasurable.neg.ennreal_ofReal
      (by filter_upwards [] with value; exact ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', Complex.real_smul]
    have hswap (amount : ℝ) (value : RationalAdele) :
        (amount : ℂ) * (rationalAdeleFourierChar (frequency * value) : ℂ) =
          (rationalAdeleFourierChar (frequency * value) : ℂ) * amount := mul_comm _ _
    simp_rw [hswap]
    have hnegative := hphase _ hintegrable.neg.pos_part frequency
    change Integrable (fun value => (rationalAdeleFourierChar (frequency * value) : ℂ) *
      ((max (-density value) 0 : ℝ) : ℂ)) reference at hnegative
    rw [← integral_sub (hphase _ hintegrable.pos_part frequency) hnegative]
    convert hpairing frequency using 1
    congr 1
    funext value
    rw [← mul_sub, ← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]
  have hsingular : positive ⟂ₘ negative := withDensity_ofReal_mutuallySingular hmeasurable
  rw [hbalance, Measure.MutuallySingular.add_left_iff] at hsingular
  have hnegativeZero : negative = 0 := (Measure.MutuallySingular.self_iff negative).mp hsingular.2
  have hae := (withDensity_eq_zero_iff hmeasurable.neg.ennreal_ofReal.aemeasurable).mp hnegativeZero
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with value hvalue
    exact neg_nonpos.mp (ENNReal.ofReal_eq_zero.mp hvalue)
  · simpa only [hnegativeZero, add_zero] using hbalance

theorem rationalAdele_complex_density_of_character_pairings
    {reference target : Measure RationalAdele} [SigmaFinite reference] [IsFiniteMeasure target]
    {density : RationalAdele → ℂ} (hmeasurable : Measurable density)
    (hintegrable : Integrable density reference)
    (hpairing : ∀ frequency : RationalAdele,
      ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) * density value ∂reference =
        ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) ∂target) :
    (∀ᵐ value ∂reference, (density value).im = 0 ∧ 0 ≤ (density value).re) ∧
      reference.withDensity (fun value => ENNReal.ofReal (density value).re) = target := by
  have hconjugateIntegrable : Integrable (fun value => star (density value)) reference :=
    (@RCLike.conjLIE ℂ _).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hintegrable
  have hphase (test : RationalAdele → ℂ) (htest : Integrable test reference)
      (frequency : RationalAdele) :
      Integrable (fun value => (rationalAdeleFourierChar (frequency * value) : ℂ) *
        test value) reference :=
    htest.bdd_mul (rationalAdeleBoundedFourierChar frequency).continuous.aestronglyMeasurable
      (by filter_upwards [] with value; exact le_of_eq (Circle.norm_coe _))
  have hconjugate (frequency : RationalAdele) :
      ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) * star (density value) ∂reference =
        ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) ∂target := by
    have heq := congrArg (starRingEnd ℂ) (hpairing (-frequency))
    rw [← integral_conj, ← integral_conj] at heq
    convert heq using 1 <;> congr 1 <;> funext value <;>
      simp only [map_mul, neg_mul, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj,
        Complex.star_def, starRingEnd_self_apply]
  have himaginary : (fun value => (density value).im) =ᵐ[reference] 0 := by
    apply rationalAdele_real_ae_zero_of_integral_fourierChar_mul_eq_zero hintegrable.im
    intro frequency
    change (∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) *
      ((density value).im : ℂ) ∂reference) = 0
    simp_rw [Complex.im_eq_sub_conj, ← mul_div_assoc, mul_sub, starRingEnd_apply]
    rw [integral_div, integral_sub (hphase _ hintegrable frequency)
      (hphase _ hconjugateIntegrable frequency), hpairing, hconjugate, sub_self, zero_div]
  have hrealPairing (frequency : RationalAdele) :
      ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) *
          ((density value).re : ℂ) ∂reference =
        ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) ∂target := by
    simp_rw [Complex.re_eq_add_conj, ← mul_div_assoc, mul_add, starRingEnd_apply]
    rw [integral_div, integral_add (hphase _ hintegrable frequency)
      (hphase _ hconjugateIntegrable frequency), hpairing, hconjugate]
    ring
  obtain ⟨hnonnegative, hmeasure⟩ := rationalAdele_real_density_of_character_pairings
    hmeasurable.re hintegrable.re hrealPairing
  refine ⟨?_, hmeasure⟩
  filter_upwards [himaginary, hnonnegative] with value himaginary hnonnegative
  exact ⟨himaginary, hnonnegative⟩

end PositiveDefiniteIntegralLattice
