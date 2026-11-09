import SMSFormula.RationalAdeleRankOneAdelicEisensteinSiegelIntegrable
import SMSFormula.RationalAdeleAdditiveQuotientCharacter

noncomputable section

open MeasureTheory Set RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {rank : ℕ}

local instance : T2Space RationalAdele := by
  letI (place : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv place).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).2⟩
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

theorem integrable_rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice
    (lattice : PositiveDefiniteIntegralLattice rank) {scale : ℝ} (hscale : 0 < scale) (hrank : 5 ≤ rank) :
    Integrable
      (lattice.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest lattice (scale : ℂ)))
      rationalAdeleAddHaarMeasure := by
  let coefficient :=
    lattice.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
      (rationalAdeleVectorPolarGaussianLatticeTest lattice (scale : ℂ))
  let blocks : ℚ → Set RationalAdele := fun rational =>
    (fun adele => adele + algebraMap ℚ RationalAdele rational) '' rationalAdeleStandardBlock
  let majorant : ℚ → ℝ := fun rational =>
    lattice.rationalAdeleRankOneAdelicBruhatStandardBlockConstant scale *
      (Real.sqrt (rationalRankOneBruhatHeight rational))⁻¹ ^ rank
  have hcontinuous : Continuous coefficient :=
    lattice.rationalQuadraticSpaceMatrix.continuous_rationalAdeleRankOneAdelicBruhatCoefficient
      _ (integrable_rationalAdeleVectorPolarGaussianLatticeTest (by simpa using hscale) lattice)
  have hcompact (rational : ℚ) : IsCompact (blocks rational) :=
    isCompact_rationalAdeleStandardBlock.image (continuous_id.add continuous_const)
  have hmeasure (rational : ℚ) : rationalAdeleAddHaarMeasure (blocks rational) = 1 := by
    have heq : blocks rational =
        (fun adele => adele + -(algebraMap ℚ RationalAdele rational)) ⁻¹'
          rationalAdeleStandardBlock := by
      ext adele
      constructor
      · rintro ⟨blockAdele, hv, rfl⟩
        simpa using hv
      · intro hu
        exact ⟨adele + -(algebraMap ℚ RationalAdele rational), hu, by simp⟩
    rw [heq, measure_preimage_add_right]
    exact rationalAdeleAddHaarMeasure_standardBlock
  have hbound (rational : ℚ) (adele : RationalAdele) (hu : adele ∈ blocks rational) :
      ‖coefficient adele‖ ≤ majorant rational := by
    rcases hu with ⟨blockAdele, hv, rfl⟩
    exact lattice.norm_rationalAdeleRankOneAdelicBruhatCoefficient_add_diagonal_le_height_of_mem_standardBlock
      hscale blockAdele hv rational
  have hsum : Summable (fun rational : ℚ =>
      ∫ adele in blocks rational, ‖coefficient adele‖ ∂rationalAdeleAddHaarMeasure) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun rational => ?_)
      ((summable_inv_sqrt_rationalRankOneBruhatHeight_pow hrank).mul_left
        (lattice.rationalAdeleRankOneAdelicBruhatStandardBlockConstant scale))
    have hnorm := norm_setIntegral_le_of_norm_le_const
      (f := fun adele => ‖coefficient adele‖) ((hcompact rational).measure_lt_top
        (μ := rationalAdeleAddHaarMeasure))
      (fun adele hu => (norm_norm _).trans_le (hbound rational adele hu))
    simpa only [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
      measureReal_def, hmeasure, ENNReal.toReal_one, mul_one] using hnorm
  have hcover : (⋃ rational : ℚ, blocks rational) = univ := by
    apply eq_univ_of_forall
    intro adele
    obtain ⟨rational, hrational⟩ := exists_rational_sub_mem_rationalAdeleStandardBlock adele
    exact mem_iUnion.mpr ⟨rational, adele - algebraMap ℚ RationalAdele rational,
      hrational, sub_add_cancel _ _⟩
  have hintegrable := integrableOn_iUnion_of_summable_integral_norm
    (fun rational => hcontinuous.continuousOn.integrableOn_compact (hcompact rational)) hsum
  simpa only [hcover, integrableOn_univ] using hintegrable

theorem integrable_rationalAdeleRankOneAdelicBruhatCoefficient_fourier_polarGaussianLattice
    (lattice : PositiveDefiniteIntegralLattice rank) {scale : ℝ} (hscale : 0 < scale) (hrank : 5 ≤ rank) (frequency : ℚ) :
    Integrable (fun adele : RationalAdele =>
      (rationalAdeleScaledFourierChar (-frequency) adele : ℂ) *
        lattice.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
          (rationalAdeleVectorPolarGaussianLatticeTest lattice (scale : ℂ)) adele)
      rationalAdeleAddHaarMeasure := by
  apply (lattice.integrable_rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice
    hscale hrank).bdd_mul
  · exact (continuous_rationalAdeleScaledFourierChar (-frequency)).subtype_val.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun _ => le_of_eq (Circle.norm_coe _)

theorem summable_integral_norm_rationalAdeleRankOneAdelicBruhatCoefficient_standardBlock
    (lattice : PositiveDefiniteIntegralLattice rank) {scale : ℝ} (hscale : 0 < scale) (hrank : 5 ≤ rank) :
    Summable (fun rational : ℚ =>
      ∫ adele in rationalAdeleStandardBlock,
        ‖lattice.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
          (rationalAdeleVectorPolarGaussianLatticeTest lattice (scale : ℂ))
          (adele + algebraMap ℚ RationalAdele rational)‖ ∂rationalAdeleAddHaarMeasure) := by
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun rational => ?_)
    ((summable_inv_sqrt_rationalRankOneBruhatHeight_pow hrank).mul_left
      (lattice.rationalAdeleRankOneAdelicBruhatStandardBlockConstant scale))
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (f := fun adele =>
      ‖lattice.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest lattice (scale : ℂ))
        (adele + algebraMap ℚ RationalAdele rational)‖)
    (isCompact_rationalAdeleStandardBlock.measure_lt_top
      (μ := rationalAdeleAddHaarMeasure))
    (fun adele hu => (norm_norm _).trans_le
      (lattice.norm_rationalAdeleRankOneAdelicBruhatCoefficient_add_diagonal_le_height_of_mem_standardBlock
        hscale adele hu rational))
  simpa only [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
    measureReal_def, rationalAdeleAddHaarMeasure_standardBlock, ENNReal.toReal_one,
    mul_one] using hnorm

theorem integral_tsum_rationalAdeleRankOneAdelicBruhatCoefficient_fourier_standardBlock
    (lattice : PositiveDefiniteIntegralLattice rank) {scale : ℝ} (hscale : 0 < scale) (hrank : 5 ≤ rank) (frequency : ℚ) :
    (∫ adele in rationalAdeleStandardBlock,
      (rationalAdeleScaledFourierChar (-frequency) adele : ℂ) *
        ∑' rational : ℚ,
          lattice.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
            (rationalAdeleVectorPolarGaussianLatticeTest lattice (scale : ℂ))
            (adele + algebraMap ℚ RationalAdele rational) ∂rationalAdeleAddHaarMeasure) =
      ∑' rational : ℚ, ∫ adele in rationalAdeleStandardBlock,
        (rationalAdeleScaledFourierChar (-frequency) adele : ℂ) *
          lattice.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
            (rationalAdeleVectorPolarGaussianLatticeTest lattice (scale : ℂ))
            (adele + algebraMap ℚ RationalAdele rational) ∂rationalAdeleAddHaarMeasure := by
  simp_rw [← tsum_mul_left]
  symm
  apply integral_tsum_of_summable_integral_norm
  · intro rational
    apply ContinuousOn.integrableOn_compact isCompact_rationalAdeleStandardBlock
    exact ((continuous_rationalAdeleScaledFourierChar (-frequency)).subtype_val.mul
      ((lattice.rationalQuadraticSpaceMatrix.continuous_rationalAdeleRankOneAdelicBruhatCoefficient
        _ (integrable_rationalAdeleVectorPolarGaussianLatticeTest (by simpa using hscale) lattice)).comp
        (continuous_id.add continuous_const))).continuousOn
  · simpa only [norm_mul, Circle.norm_coe, one_mul] using
      lattice.summable_integral_norm_rationalAdeleRankOneAdelicBruhatCoefficient_standardBlock hscale hrank

end PositiveDefiniteIntegralLattice
