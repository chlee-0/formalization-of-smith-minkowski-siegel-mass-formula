import SMSFormula.RationalAdeleStandardThetaShellGap
import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeNonnegative

noncomputable section

open PositiveDefiniteIntegralLattice Matrix

namespace Real

theorem realCusp_gaussian_majorant {exponent damping dilation value : ℝ}
    (hexponent : 0 ≤ exponent) (hdamping : 0 < damping)
    (hdilation : 1 ≤ dilation) (hvalue : 1 ≤ value) :
    dilation ^ exponent * exp (-2 * damping * dilation ^ 2 * value) ≤
      exp (exponent ^ 2 / (4 * damping)) * exp (-damping * value) := by
  have hpositive : 0 < dilation := lt_of_lt_of_le zero_lt_one hdilation
  have hlog : log dilation * exponent ≤ dilation * exponent := by
    apply mul_le_mul_of_nonneg_right _ hexponent
    linarith [log_le_sub_one_of_pos hpositive]
  have hsquare : 1 ≤ dilation ^ 2 := by nlinarith
  have hgap : dilation ^ 2 ≤ 2 * dilation ^ 2 * value - value := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsquare) (sub_nonneg.mpr hvalue)]
  have hgapScaled := mul_le_mul_of_nonneg_left hgap hdamping.le
  have hcomplete : dilation * exponent - damping * dilation ^ 2 ≤
      exponent ^ 2 / (4 * damping) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * damping)).mpr
    nlinarith [sq_nonneg (exponent - 2 * damping * dilation)]
  rw [rpow_def_of_pos hpositive, ← exp_add, ← exp_add]
  apply exp_le_exp.mpr
  nlinarith

end Real

namespace RationalQuadraticSpaceMatrix

variable {rank : ℕ}

theorem norm_polarRealGaussian_eq_native_exp (lattice : PositiveDefiniteIntegralLattice rank)
    (parameter : ℂ) (vector : Fin rank → ℝ) :
    ‖polarRealGaussian lattice parameter vector‖ =
      Real.exp (-2 * Real.pi * parameter.re *
        lattice.rationalQuadraticSpaceMatrix.realQuadraticFormValue vector) := by
  rw [polarRealGaussian, realCoordinateGaussian_eq_exp_dotProduct, Complex.norm_exp,
    lattice.dotProduct_polarRealSqrtMatrix_mulVec,
    realPolarMatrix_eq_two_smul_realFormMatrix, Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero, mul_zero]
  congr 1
  unfold realQuadraticFormValue
  ring

theorem norm_standardTest_eq_native_exp_of_integral
    (lattice : PositiveDefiniteIntegralLattice rank) (parameter : ℂ) (vector : Fin rank → RationalAdele)
    (hintegral : rationalAdeleVectorFinitePart rank vector ∈ integralFiniteAdeleVectors rank) :
    ‖rationalAdeleVectorPolarGaussianLatticeTest lattice parameter vector‖ =
      Real.exp (-2 * Real.pi * parameter.re *
        lattice.rationalQuadraticSpaceMatrix.realQuadraticFormValue
          (rationalAdeleVectorRealPart rank vector)) := by
  rw [rationalAdeleVectorPolarGaussianLatticeTest,
    rationalFiniteAdeleVectorIntegralIndicator_of_mem hintegral, mul_one,
    norm_polarRealGaussian_eq_native_exp]

theorem norm_realCuspTest_eq_native_exp_of_integral
    (lattice : PositiveDefiniteIntegralLattice rank) (gaussianScale phase : ℝ) {dilation : ℝ}
    (hdilation : 0 < dilation) (vector : Fin rank → RationalAdele)
    (hintegral : rationalAdeleVectorFinitePart rank vector ∈ integralFiniteAdeleVectors rank) :
    ‖rationalAdeleRealCuspGaussianLatticeTest lattice gaussianScale dilation phase vector‖ =
      dilation ^ ((rank : ℝ) / 2) * Real.exp (-2 * Real.pi * (gaussianScale * dilation ^ 2) *
        lattice.rationalQuadraticSpaceMatrix.realQuadraticFormValue
          (rationalAdeleVectorRealPart rank vector)) := by
  rw [rationalAdeleRealCuspGaussianLatticeTest_eq, norm_mul,
    norm_standardTest_eq_native_exp_of_integral lattice _ vector hintegral,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hdilation _)]
  simp [← Complex.ofReal_pow]

theorem uniform_realCuspTest_gaussian_majorant_on_rational_shell
    (lattice : PositiveDefiniteIntegralLattice rank) {gaussianScale : ℝ} (hgaussian : 0 < gaussianScale) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ dilation : ℝ, 1 ≤ dilation → ∀ phase : ℝ,
      ∀ vector : Fin rank → RationalAdele, ∀ value : ℚ,
      lattice.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue vector =
        algebraMap ℚ RationalAdele value → value ≠ 0 →
      ‖rationalAdeleRealCuspGaussianLatticeTest lattice gaussianScale dilation phase vector‖ ≤
        bound * ‖rationalAdeleVectorPolarGaussianLatticeTest lattice
          ((gaussianScale / 2 : ℝ) : ℂ) vector‖ := by
  refine ⟨Real.exp (((rank : ℝ) / 2) ^ 2 / (4 * (Real.pi * gaussianScale))),
    Real.exp_pos _, ?_⟩
  intro dilation hdilation phase vector value hvalue hnonzero
  by_cases htest : rationalAdeleRealCuspGaussianLatticeTest lattice gaussianScale dilation phase vector = 0
  · rw [htest, norm_zero]
    positivity
  have hgap := one_le_rational_shell_of_realCuspTest_ne_zero lattice gaussianScale dilation phase
    vector value hvalue hnonzero htest
  have hreal : lattice.rationalQuadraticSpaceMatrix.realQuadraticFormValue
      (rationalAdeleVectorRealPart rank vector) = (value : ℝ) := by
    rw [← rationalAdeleVectorRealPart_fullAdelicQuadraticFormValue, hvalue]
    exact rationalInfiniteAdeleContinuousAddEquivReal_algebraMap value
  have hgapReal : (1 : ℝ) ≤ (value : ℝ) := by exact_mod_cast hgap
  rw [rationalAdeleRealCuspGaussianLatticeTest_eq] at htest
  have hintegral := standardTest_ne_zero_finitePart_integral lattice _ vector
    (mul_ne_zero_iff.mp htest).2
  rw [norm_realCuspTest_eq_native_exp_of_integral lattice gaussianScale phase
      (lt_of_lt_of_le zero_lt_one hdilation) vector hintegral,
    norm_standardTest_eq_native_exp_of_integral lattice _ vector hintegral, hreal]
  simpa only [Complex.ofReal_re, show -2 * Real.pi * (gaussianScale / 2) =
      -(Real.pi * gaussianScale) by ring,
    show -2 * Real.pi * (gaussianScale * dilation ^ 2) =
      -2 * (Real.pi * gaussianScale) * dilation ^ 2 by ring] using
    Real.realCusp_gaussian_majorant (by positivity : 0 ≤ (rank : ℝ) / 2)
      (mul_pos Real.pi_pos hgaussian) hdilation hgapReal

theorem uniform_realCuspTest_gaussian_majorant_generalSpin
    (lattice : PositiveDefiniteIntegralLattice rank) {gaussianScale : ℝ} (hgaussian : 0 < gaussianScale) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ dilation : ℝ, 1 ≤ dilation → ∀ phase : ℝ,
      ∀ groupElement : lattice.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup,
      ∀ vector : Fin rank → ℚ, vector ≠ 0 →
      ‖rationalAdeleRealCuspGaussianLatticeTest lattice gaussianScale dilation phase
        (lattice.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRationalVectorAction
          groupElement vector)‖ ≤
        bound * ‖rationalAdeleVectorPolarGaussianLatticeTest lattice
          ((gaussianScale / 2 : ℝ) : ℂ)
          (lattice.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRationalVectorAction
            groupElement vector)‖ := by
  obtain ⟨bound, hbound, huniform⟩ :=
    uniform_realCuspTest_gaussian_majorant_on_rational_shell lattice hgaussian
  refine ⟨bound, hbound, ?_⟩
  intro dilation hdilation phase groupElement vector hnonzero
  exact huniform dilation hdilation phase _ _
    (fullAdelicQuadraticFormValue_generalSpinRationalAction _ groupElement vector)
    (ne_of_gt (lattice.rationalQuadraticSpaceMatrix_nativeRationalQuadraticForm_pos hnonzero))

end RationalQuadraticSpaceMatrix
