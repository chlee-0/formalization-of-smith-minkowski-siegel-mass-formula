import SMSFormula.RationalAdeleScalarGaussianProbe

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

theorem rationalAdele_unitGaussian_eq_ite (value : RationalAdele) :
    rationalAdeleGaussianIntegralTest 1 value =
      if value.2 ∈ integralFiniteAdeleSubring then
        ((Real.exp (-Real.pi * (rationalInfiniteAdeleContinuousAddEquivReal value.1) ^ 2) : ℝ) : ℂ)
      else 0 := by
  classical
  unfold rationalAdeleGaussianIntegralTest
  by_cases hmem : value.2 ∈ integralFiniteAdeleSubring
  · rw [rationalFiniteAdeleIntegralIndicator_of_mem hmem, mul_one, if_pos hmem]
    simp only [rationalInfiniteAdeleGaussian, mul_one, Complex.ofReal_exp,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
  · rw [rationalFiniteAdeleIntegralIndicator_of_not_mem hmem, mul_zero, if_neg hmem]

theorem measurable_rationalAdele_unitGaussian : Measurable (rationalAdeleGaussianIntegralTest 1) := by
  change Measurable (fun value => rationalAdeleGaussianIntegralTest 1 value)
  simp_rw [rationalAdele_unitGaussian_eq_ite]
  apply Measurable.ite
    (isOpen_integralFiniteAdeleSubring.measurableSet.preimage measurable_snd)
  · fun_prop
  · exact measurable_const

theorem continuous_rationalAdele_unitGaussian : Continuous (rationalAdeleGaussianIntegralTest 1) := by
  have hfunction : Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
      (rationalAdeleGaussianIntegralTest 1) = rationalAdeleGaussianIntegralTest 1 :=
    funext rationalAdele_unitGaussian_fourier
  rw [← hfunction]
  exact VectorFourier.fourierIntegral_continuous continuous_rationalAdeleFourierChar
    (by change Continuous (fun pair : RationalAdele × RationalAdele => pair.1 * pair.2); fun_prop)
    (integrable_rationalAdeleGaussianIntegralTest (by norm_num : 0 < (1 : ℂ).re))

theorem rationalAdele_unitGaussian_eq_coe_norm (value : RationalAdele) :
    rationalAdeleGaussianIntegralTest 1 value = (‖rationalAdeleGaussianIntegralTest 1 value‖ : ℂ) := by
  rw [rationalAdele_unitGaussian_eq_ite]
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  · simp only [norm_zero, Complex.ofReal_zero]

theorem norm_rationalAdele_unitGaussian_le_one (value : RationalAdele) :
    ‖rationalAdeleGaussianIntegralTest 1 value‖ ≤ 1 := by
  rw [rationalAdele_unitGaussian_eq_ite]
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)
  · simp

def rationalAdeleScalarGaussianWeight (shift value : RationalAdele) : ℝ :=
  ‖rationalAdeleGaussianIntegralTest 1 (value + shift)‖

theorem measurable_rationalAdeleScalarGaussianWeight (shift : RationalAdele) :
    Measurable (rationalAdeleScalarGaussianWeight shift) :=
  (measurable_rationalAdele_unitGaussian.comp (measurable_id.add_const shift)).norm

theorem continuous_rationalAdeleScalarGaussianWeight (shift : RationalAdele) :
    Continuous (rationalAdeleScalarGaussianWeight shift) :=
  (continuous_rationalAdele_unitGaussian.comp (continuous_id.add continuous_const)).norm

theorem rationalAdeleScalarGaussianWeight_neg_self (value : RationalAdele) :
    rationalAdeleScalarGaussianWeight (-value) value = 1 := by
  unfold rationalAdeleScalarGaussianWeight
  rw [add_neg_cancel]
  change ‖rationalAdeleGaussianIntegralTest 1 (0, 0)‖ = 1
  simp [rationalAdele_unitGaussian_eq_ite]

theorem rationalAdeleScalarGaussianWeight_nonneg (shift value : RationalAdele) :
    0 ≤ rationalAdeleScalarGaussianWeight shift value := norm_nonneg _

theorem rationalAdeleScalarGaussianWeight_le_one (shift value : RationalAdele) :
    rationalAdeleScalarGaussianWeight shift value ≤ 1 := norm_rationalAdele_unitGaussian_le_one _

theorem rationalAdeleScalarGaussianWeight_pos_of_mem (shift value : RationalAdele)
    (hmem : (value + shift).2 ∈ integralFiniteAdeleSubring) :
    0 < rationalAdeleScalarGaussianWeight shift value := by
  unfold rationalAdeleScalarGaussianWeight
  rw [rationalAdele_unitGaussian_eq_ite, if_pos hmem, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_pos _

theorem rationalAdeleScalarGaussianProbe_eq_weight (shift frequency value : RationalAdele) :
    rationalAdeleScalarGaussianProbe shift frequency value =
      (rationalAdeleFourierChar (frequency * value) : ℂ) *
        rationalAdeleScalarGaussianWeight shift value := by
  unfold rationalAdeleScalarGaussianProbe rationalAdeleScalarGaussianWeight
  rw [← rationalAdele_unitGaussian_eq_coe_norm]

theorem integrable_rationalAdeleScalarGaussianWeight (shift : RationalAdele) :
    Integrable (rationalAdeleScalarGaussianWeight shift) rationalAdeleAddHaarMeasure := by
  have htest := (integrable_rationalAdeleScalarGaussianProbe shift 0).norm
  simpa only [rationalAdeleScalarGaussianProbe_eq_weight, zero_mul,
    AddChar.map_zero_eq_one, Circle.coe_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (rationalAdeleScalarGaussianWeight_nonneg shift _)] using htest

theorem integrable_rationalAdeleScalarGaussianWeight_finiteMeasure
    (measure : Measure RationalAdele) [IsFiniteMeasure measure] (shift : RationalAdele) :
    Integrable (rationalAdeleScalarGaussianWeight shift) measure := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_rationalAdeleScalarGaussianWeight shift).aestronglyMeasurable
  filter_upwards [] with value
  rw [Real.norm_eq_abs, abs_of_nonneg (rationalAdeleScalarGaussianWeight_nonneg shift value)]
  exact rationalAdeleScalarGaussianWeight_le_one shift value

end PositiveDefiniteIntegralLattice
