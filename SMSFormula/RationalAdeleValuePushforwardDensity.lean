import SMSFormula.RationalAdeleValuePushforwardDeterminesCoefficient
import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeNonnegative
import SMSFormula.RationalAdeleRankOneFiniteOnlyDilationBruhat
import SMSFormula.RationalAdeleElementaryGaussianFourier
import SMSFormula.RationalAdeleRankOneAdelicBruhatIntegrable
import SMSFormula.RationalAdeleScalarGaussianProbe
import SMSFormula.RationalAdeleFourierPositiveDensityComparison
import SMSFormula.RationalAdeleScalarGaussianWeight
import SMSFormula.RationalAdeleScalarGaussianWeightRemoval

/-!
# The value density for the whole L1 class

Another module proves that the value pushforward of the polar Gaussian--lattice test is absolutely
continuous with a nonnegative continuous density, at positive scale and rank at least five.  That
proof used the Gaussian only through three facts: the pushforward is finite, its Fourier--Stieltjes
transform is the adelic Bruhat coefficient, and that coefficient is integrable.

All three are available for an arbitrary nonnegative test in the L1 class, so this file runs
the chain with the test abstracted.  The rank and scale hypotheses disappear; what replaces them is
membership in the class.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The complex test attached to a nonnegative one, written out so that every statement matches
the previous file's syntactically. -/
abbrev toComplexTest (Phi : (Fin n → RationalAdele) → ℝ≥0∞) : (Fin n → RationalAdele) → ℂ :=
  fun x ↦ (((Phi x).toReal : ℝ) : ℂ)

/-- The value density of a nonnegative test: the Fourier transform of its adelic Bruhat
coefficient.  This is the existing construction with the test abstracted. -/
def valueFourierDensity (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) : RationalAdele → ℂ :=
  Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
    (V.rationalAdeleRankOneAdelicBruhatCoefficient (toComplexTest Phi))

theorem isFiniteMeasure_valuePushforward (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi)) :
    IsFiniteMeasure (V.valuePushforward Phi) :=
  ⟨lt_top_iff_ne_top.mpr
    (V.valuePushforward_ne_top_of_integrable_toReal hmeas hfin hclass.1)⟩

theorem continuous_valueFourierDensity (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi)) :
    Continuous (V.valueFourierDensity Phi) :=
  VectorFourier.fourierIntegral_continuous continuous_rationalAdeleFourierChar
    (by change Continuous (fun pair : RationalAdele × RationalAdele => pair.1 * pair.2); fun_prop)
    hclass.2

theorem norm_valueFourierDensity_le (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) (value : RationalAdele) :
    ‖V.valueFourierDensity Phi value‖ ≤
      ∫ parameter, ‖V.rationalAdeleRankOneAdelicBruhatCoefficient (toComplexTest Phi) parameter‖
        ∂rationalAdeleAddHaarMeasure :=
  Fourier.norm_fourierIntegral_le_integral_norm _ _ _ _

theorem integrable_valueFourierDensity_mul (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi))
    (test : RationalAdele → ℂ) (htest : Integrable test rationalAdeleAddHaarMeasure) :
    Integrable (fun value ↦ V.valueFourierDensity Phi value * test value)
      rationalAdeleAddHaarMeasure :=
  htest.bdd_mul (V.continuous_valueFourierDensity hclass).aestronglyMeasurable
    (Filter.Eventually.of_forall fun value ↦ V.norm_valueFourierDensity_le Phi value)

/-! ## The Fubini pairing, with the test abstracted -/

theorem integrable_valuePushforwardFourierPairing (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi))
    (test : RationalAdele → ℂ) (htest : Integrable test rationalAdeleAddHaarMeasure) :
    Integrable (fun pair : RationalAdele × RationalAdele ↦
      test pair.1 * (rationalAdeleFourierChar (pair.1 * pair.2) : ℂ))
      (rationalAdeleAddHaarMeasure.prod (V.valuePushforward Phi)) := by
  letI := V.isFiniteMeasure_valuePushforward hmeas hfin hclass
  have hbase := htest.mul_prod
    (integrable_const (1 : ℂ) : Integrable (fun _ : RationalAdele ↦ (1 : ℂ))
      (V.valuePushforward Phi))
  have hproduct := hbase.bdd_mul
    continuous_uncurry_rationalAdeleFourierKernel.subtype_val.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ ↦ le_of_eq (Circle.norm_coe _))
  simpa only [rationalAdeleFourierKernel, Function.uncurry_def, mul_one, mul_comm] using hproduct

theorem integral_valuePushforwardFourierPairing (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi))
    (test : RationalAdele → ℂ) (htest : Integrable test rationalAdeleAddHaarMeasure) :
    (∫ parameter, test parameter *
      V.rationalAdeleRankOneAdelicBruhatCoefficient (toComplexTest Phi) parameter
        ∂rationalAdeleAddHaarMeasure) =
      ∫ value, (∫ parameter, test parameter *
        (rationalAdeleFourierChar (parameter * value) : ℂ) ∂rationalAdeleAddHaarMeasure)
        ∂(V.valuePushforward Phi) := by
  letI := V.isFiniteMeasure_valuePushforward hmeas hfin hclass
  simp_rw [← V.integral_fourierChar_valuePushforward hmeas hfin, ← integral_const_mul]
  exact integral_integral_swap
    (V.integrable_valuePushforwardFourierPairing hmeas hfin hclass test htest)

private theorem scalarFourier_neg_eq' (test : RationalAdele → ℂ) (value : RationalAdele) :
    Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure test (-value) =
      ∫ parameter, test parameter * (rationalAdeleFourierChar (parameter * value) : ℂ)
        ∂rationalAdeleAddHaarMeasure := by
  simp only [Fourier.fourierIntegral_def, mul_neg, neg_neg, Circle.smul_def,
    smul_eq_mul, mul_comm]

theorem integral_bruhat_eq_integral_fourier_valuePushforward (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi))
    (test : RationalAdele → ℂ) (htest : Integrable test rationalAdeleAddHaarMeasure) :
    (∫ parameter, test parameter *
      V.rationalAdeleRankOneAdelicBruhatCoefficient (toComplexTest Phi) parameter
        ∂rationalAdeleAddHaarMeasure) =
      ∫ value, Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
        test (-value) ∂(V.valuePushforward Phi) := by
  simpa only [scalarFourier_neg_eq'] using
    V.integral_valuePushforwardFourierPairing hmeas hfin hclass test htest

/-! ## The probe pairing and the density -/

theorem integral_valueFourierDensity_mul_probe (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi)) (shift frequency : RationalAdele) :
    (∫ value, V.valueFourierDensity Phi value *
      rationalAdeleScalarGaussianProbe shift frequency value ∂rationalAdeleAddHaarMeasure) =
      ∫ value, rationalAdeleScalarGaussianProbe shift frequency value
        ∂(V.valuePushforward Phi) := by
  have hflip : (LinearMap.mul RationalAdele RationalAdele).flip =
      LinearMap.mul RationalAdele RationalAdele := by
    ext
    exact mul_comm _ _
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := LinearMap.mul RationalAdele RationalAdele)
    continuous_rationalAdeleFourierChar
    (by change Continuous (fun pair : RationalAdele × RationalAdele => pair.1 * pair.2); fun_prop)
    hclass.2 (integrable_rationalAdeleScalarGaussianProbe shift frequency)
  rw [hflip] at hswap
  change (∫ value, V.valueFourierDensity Phi value *
      rationalAdeleScalarGaussianProbe shift frequency value ∂rationalAdeleAddHaarMeasure) =
    ∫ parameter, V.rationalAdeleRankOneAdelicBruhatCoefficient (toComplexTest Phi) parameter *
      Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
        (rationalAdeleScalarGaussianProbe shift frequency) parameter
      ∂rationalAdeleAddHaarMeasure at hswap
  rw [hswap]
  simp_rw [fourier_rationalAdeleScalarGaussianProbe, mul_comm]
  rw [V.integral_bruhat_eq_integral_fourier_valuePushforward hmeas hfin hclass
    _ (integrable_rationalAdeleScalarGaussianProbeTransform shift frequency)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun value =>
    fourier_rationalAdeleScalarGaussianProbeTransform_neg shift frequency value

theorem valuePushforward_weighted_density_comparison (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi)) (shift : RationalAdele) :
    (∀ᵐ value ∂rationalAdeleAddHaarMeasure,
      (V.valueFourierDensity Phi value *
        rationalAdeleScalarGaussianWeight shift value).im = 0 ∧
      0 ≤ (V.valueFourierDensity Phi value *
        rationalAdeleScalarGaussianWeight shift value).re) ∧
    rationalAdeleAddHaarMeasure.withDensity
      (fun value ↦ ENNReal.ofReal (V.valueFourierDensity Phi value *
        rationalAdeleScalarGaussianWeight shift value).re) =
      (V.valuePushforward Phi).withDensity
        (fun value ↦ ENNReal.ofReal (rationalAdeleScalarGaussianWeight shift value)) := by
  letI := V.isFiniteMeasure_valuePushforward hmeas hfin hclass
  letI : IsFiniteMeasure ((V.valuePushforward Phi).withDensity
      (fun value ↦ ENNReal.ofReal (rationalAdeleScalarGaussianWeight shift value))) :=
    isFiniteMeasure_withDensity_ofReal
      (integrable_rationalAdeleScalarGaussianWeight_finiteMeasure
        (V.valuePushforward Phi) shift).hasFiniteIntegral
  have hweight := measurable_rationalAdeleScalarGaussianWeight shift
  have hdensity := V.continuous_valueFourierDensity hclass
  apply rationalAdele_complex_density_of_character_pairings
    (hdensity.measurable.mul hweight.complex_ofReal)
    (V.integrable_valueFourierDensity_mul hclass _
      (integrable_rationalAdeleScalarGaussianWeight shift).ofReal)
  intro frequency
  rw [integral_withDensity_eq_integral_toReal_smul hweight.ennreal_ofReal
    (by filter_upwards [] with value; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (rationalAdeleScalarGaussianWeight_nonneg shift _),
    Complex.real_smul]
  have hpairing := V.integral_valueFourierDensity_mul_probe hmeas hfin hclass shift frequency
  simp only [rationalAdeleScalarGaussianProbe_eq_weight] at hpairing
  convert hpairing using 1 <;> congr 1 <;> funext value <;> ring

theorem valuePushforward_weighted_measure_eq (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi)) (shift : RationalAdele) :
    (rationalAdeleAddHaarMeasure.withDensity
      (fun value ↦ ENNReal.ofReal (V.valueFourierDensity Phi value).re)).withDensity
        (fun value ↦ ENNReal.ofReal (rationalAdeleScalarGaussianWeight shift value)) =
      (V.valuePushforward Phi).withDensity
        (fun value ↦ ENNReal.ofReal (rationalAdeleScalarGaussianWeight shift value)) := by
  rw [← withDensity_mul rationalAdeleAddHaarMeasure
    (f := fun value ↦ ENNReal.ofReal (V.valueFourierDensity Phi value).re)
    (V.continuous_valueFourierDensity hclass).measurable.re.ennreal_ofReal
    (measurable_rationalAdeleScalarGaussianWeight shift).ennreal_ofReal]
  convert (V.valuePushforward_weighted_density_comparison hmeas hfin hclass shift).2 using 1
  congr 1
  funext value
  dsimp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul' (rationalAdeleScalarGaussianWeight_nonneg shift value)]
  simp

/-- The value density for the whole class: the value pushforward of any nonnegative test in the L1
class is absolutely continuous, with the real part of the Fourier transform of its adelic Bruhat
coefficient as density. -/
theorem valuePushforward_eq_withDensity (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi)) :
    V.valuePushforward Phi =
      rationalAdeleAddHaarMeasure.withDensity
        (fun value ↦ ENNReal.ofReal (V.valueFourierDensity Phi value).re) := by
  symm
  apply rationalAdele_measure_eq_of_gaussian_weight_eq
  exact V.valuePushforward_weighted_measure_eq hmeas hfin hclass

theorem valuePushforward_absolutelyContinuous (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi)) :
    V.valuePushforward Phi ≪ rationalAdeleAddHaarMeasure := by
  rw [V.valuePushforward_eq_withDensity hmeas hfin hclass]
  exact withDensity_absolutelyContinuous _ _

/-- The density is real and nonnegative at every adelic value, not merely almost everywhere. -/
theorem valueFourierDensity_real_nonnegative (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi)) (value : RationalAdele) :
    (V.valueFourierDensity Phi value).im = 0 ∧ 0 ≤ (V.valueFourierDensity Phi value).re := by
  have hcontinuous := (V.continuous_valueFourierDensity hclass).mul
    (Complex.continuous_ofReal.comp (continuous_rationalAdeleScalarGaussianWeight (-value)))
  have hae := (V.valuePushforward_weighted_density_comparison hmeas hfin hclass (-value)).1
  have himaginary := Measure.eq_of_ae_eq (hae.mono fun _ hpoint ↦ hpoint.1)
    (Complex.continuous_im.comp hcontinuous) continuous_const
  have hminimum : (fun point ↦ min (V.valueFourierDensity Phi point *
      rationalAdeleScalarGaussianWeight (-value) point).re 0)
      =ᵐ[rationalAdeleAddHaarMeasure] 0 := by
    filter_upwards [hae] with point hpoint
    exact min_eq_right hpoint.2
  have hnonnegative := Measure.eq_of_ae_eq hminimum
    ((Complex.continuous_re.comp hcontinuous).min continuous_const) continuous_const
  have himaginaryValue := congrFun himaginary value
  have hnonnegativeValue := congrFun hnonnegative value
  rw [rationalAdeleScalarGaussianWeight_neg_self, Complex.ofReal_one, mul_one]
    at himaginaryValue hnonnegativeValue
  exact ⟨himaginaryValue, min_eq_right_iff.mp hnonnegativeValue⟩

/-- The density is itself integrable, so the class has an L1 value density as well as an L1
coefficient. -/
theorem integrable_valueFourierDensity (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi)) :
    Integrable (V.valueFourierDensity Phi) rationalAdeleAddHaarMeasure := by
  letI := V.isFiniteMeasure_valuePushforward hmeas hfin hclass
  have hfinite := measure_ne_top (V.valuePushforward Phi) Set.univ
  rw [V.valuePushforward_eq_withDensity hmeas hfin hclass,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hfinite
  have hreal : Integrable (fun value ↦ (V.valueFourierDensity Phi value).re)
      rationalAdeleAddHaarMeasure := by
    have hintegrable := integrable_toReal_of_lintegral_ne_top
      (f := fun value ↦ ENNReal.ofReal (V.valueFourierDensity Phi value).re)
      (V.continuous_valueFourierDensity hclass).measurable.re.ennreal_ofReal.aemeasurable
      hfinite
    convert hintegrable using 1
    funext value
    exact (ENNReal.toReal_ofReal
      (V.valueFourierDensity_real_nonnegative hmeas hfin hclass value).2).symm
  apply hreal.ofReal.congr
  filter_upwards [] with value
  apply Complex.ext
  · rfl
  · exact (V.valueFourierDensity_real_nonnegative hmeas hfin hclass value).1.symm

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {rank : ℕ}

end PositiveDefiniteIntegralLattice

end
