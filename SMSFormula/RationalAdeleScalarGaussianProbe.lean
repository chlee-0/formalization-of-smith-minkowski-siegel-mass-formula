import SMSFormula.RationalAdeleElementaryGaussianFourier

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

theorem rationalAdele_unitGaussian_fourier (value : RationalAdele) :
    Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
      (rationalAdeleGaussianIntegralTest 1) value = rationalAdeleGaussianIntegralTest 1 value := by
  rw [rationalAdele_fourierIntegral_gaussianIntegralTest (by norm_num : 0 < (1 : ℂ).re)]
  simp [rationalAdeleGaussianIntegralTest, rationalInfiniteAdeleGaussian]

theorem rationalAdele_unitGaussian_neg (value : RationalAdele) :
    rationalAdeleGaussianIntegralTest 1 (-value) = rationalAdeleGaussianIntegralTest 1 value := by
  change rationalInfiniteAdeleGaussian 1 (-value.1) * rationalFiniteAdeleIntegralIndicator (-value.2) = _
  have hfinite : rationalFiniteAdeleIntegralIndicator (-value.2) =
      rationalFiniteAdeleIntegralIndicator value.2 := by
    by_cases hmem : value.2 ∈ integralFiniteAdeleSubring
    · rw [rationalFiniteAdeleIntegralIndicator_of_mem (integralFiniteAdeleSubring.neg_mem hmem),
        rationalFiniteAdeleIntegralIndicator_of_mem hmem]
    · rw [rationalFiniteAdeleIntegralIndicator_of_not_mem
        (fun hneg => hmem (integralFiniteAdeleSubring.neg_mem_iff.mp hneg)),
        rationalFiniteAdeleIntegralIndicator_of_not_mem hmem]
  rw [hfinite]
  simp only [rationalAdeleGaussianIntegralTest, rationalInfiniteAdeleGaussian,
    map_neg, Complex.ofReal_neg, neg_sq]

theorem rationalAdele_fourier_modulation (test : RationalAdele → ℂ)
    (frequency value : RationalAdele) :
    Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
      (fun parameter => (rationalAdeleFourierChar (frequency * parameter) : ℂ) * test parameter) value =
      Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure test
        (value - frequency) := by
  simp only [Fourier.fourierIntegral_def, Circle.smul_def, smul_eq_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro parameter
  dsimp only
  rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 3
  ring

def rationalAdeleScalarGaussianProbe (shift frequency value : RationalAdele) : ℂ :=
  (rationalAdeleFourierChar (frequency * value) : ℂ) *
    rationalAdeleGaussianIntegralTest 1 (value + shift)

def rationalAdeleScalarGaussianProbeTransform (shift frequency parameter : RationalAdele) : ℂ :=
  (rationalAdeleFourierChar (shift * (parameter - frequency)) : ℂ) *
    rationalAdeleGaussianIntegralTest 1 (parameter - frequency)

theorem integrable_rationalAdeleScalarGaussianProbe (shift frequency : RationalAdele) :
    Integrable (rationalAdeleScalarGaussianProbe shift frequency) rationalAdeleAddHaarMeasure := by
  have htest := integrable_rationalAdeleGaussianIntegralTest (by norm_num : 0 < (1 : ℂ).re)
  have htranslate : Integrable (fun value => rationalAdeleGaussianIntegralTest 1 (value + shift))
      rationalAdeleAddHaarMeasure := by
    exact (measurePreserving_add_right rationalAdeleAddHaarMeasure shift).integrable_comp
      htest.aestronglyMeasurable |>.mpr htest
  exact htranslate.bdd_mul
    ((continuous_rationalAdeleFourierChar.comp
      (continuous_const.mul continuous_id)).subtype_val.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => le_of_eq (Circle.norm_coe _))

theorem integrable_rationalAdeleScalarGaussianProbeTransform (shift frequency : RationalAdele) :
    Integrable (rationalAdeleScalarGaussianProbeTransform shift frequency) rationalAdeleAddHaarMeasure := by
  have htest := integrable_rationalAdeleScalarGaussianProbe 0 shift
  have htranslate := (measurePreserving_add_right rationalAdeleAddHaarMeasure (-frequency)).integrable_comp
    htest.aestronglyMeasurable |>.mpr htest
  unfold rationalAdeleScalarGaussianProbeTransform
  simpa only [rationalAdeleScalarGaussianProbeTransform, rationalAdeleScalarGaussianProbe,
    Function.comp_def, sub_eq_add_neg, add_zero] using htranslate

theorem fourier_rationalAdeleScalarGaussianProbe (shift frequency value : RationalAdele) :
    Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
      (rationalAdeleScalarGaussianProbe shift frequency) value =
      rationalAdeleScalarGaussianProbeTransform shift frequency value := by
  unfold rationalAdeleScalarGaussianProbe
  rw [rationalAdele_fourier_modulation]
  change Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
    ((rationalAdeleGaussianIntegralTest 1) ∘ (fun point => point + shift)) (value - frequency) = _
  rw [Fourier.fourierIntegral_comp_add_right]
  dsimp only
  rw [rationalAdele_unitGaussian_fourier]
  rfl

theorem fourier_rationalAdeleScalarGaussianProbeTransform_neg (shift frequency value : RationalAdele) :
    Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
      (rationalAdeleScalarGaussianProbeTransform shift frequency) (-value) =
      rationalAdeleScalarGaussianProbe shift frequency value := by
  have hfun : rationalAdeleScalarGaussianProbeTransform shift frequency =
      (fun parameter => (rationalAdeleFourierChar (shift * parameter) : ℂ) *
        rationalAdeleGaussianIntegralTest 1 parameter) ∘ (fun parameter => parameter + -frequency) := by
    funext parameter
    simp only [Function.comp_def, rationalAdeleScalarGaussianProbeTransform, sub_eq_add_neg]
  rw [hfun, Fourier.fourierIntegral_comp_add_right]
  dsimp only
  rw [rationalAdele_fourier_modulation,
    rationalAdele_unitGaussian_fourier]
  have hneg : -value - shift = -(value + shift) := by abel
  rw [hneg, rationalAdele_unitGaussian_neg]
  simp only [neg_mul_neg, Circle.smul_def, smul_eq_mul, rationalAdeleScalarGaussianProbe]

end PositiveDefiniteIntegralLattice
