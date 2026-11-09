import SMSFormula.RationalAdeleRankOneBruhatFactorization

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {rank : ℕ}

def rationalAdeleRealDilationVector (dilation : ℝ)
    (vector : Fin rank → RationalAdele) : Fin rank → RationalAdele :=
  (rationalAdeleVectorRealFiniteEquiv rank).symm
    (dilation • rationalAdeleVectorRealPart rank vector,
      rationalAdeleVectorFinitePart rank vector)

theorem realPart_rationalAdeleRealDilationVector (dilation : ℝ)
    (vector : Fin rank → RationalAdele) :
    rationalAdeleVectorRealPart rank (rationalAdeleRealDilationVector dilation vector) =
      dilation • rationalAdeleVectorRealPart rank vector := by
  exact congrArg Prod.fst ((rationalAdeleVectorRealFiniteEquiv rank).apply_symm_apply
    (dilation • rationalAdeleVectorRealPart rank vector,
      rationalAdeleVectorFinitePart rank vector))

theorem finitePart_rationalAdeleRealDilationVector (dilation : ℝ)
    (vector : Fin rank → RationalAdele) :
    rationalAdeleVectorFinitePart rank (rationalAdeleRealDilationVector dilation vector) =
      rationalAdeleVectorFinitePart rank vector := by
  exact congrArg Prod.snd ((rationalAdeleVectorRealFiniteEquiv rank).apply_symm_apply
    (dilation • rationalAdeleVectorRealPart rank vector,
      rationalAdeleVectorFinitePart rank vector))

theorem polarRealGaussian_real_dilation (lattice : PositiveDefiniteIntegralLattice rank)
    (parameter : ℂ) (dilation : ℝ) (vector : Fin rank → ℝ) :
    polarRealGaussian lattice parameter (dilation • vector) =
      polarRealGaussian lattice (parameter * (dilation : ℂ) ^ 2) vector := by
  unfold polarRealGaussian
  rw [Matrix.mulVec_smul, realCoordinateGaussian_eq_exp_dotProduct,
    realCoordinateGaussian_eq_exp_dotProduct]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  push_cast
  congr 1
  ring

theorem realQuadraticPhase_mul_polarRealGaussian_real
    (lattice : PositiveDefiniteIntegralLattice rank) (parameter : ℂ) (phase : ℝ)
    (vector : Fin rank → ℝ) :
    (Real.fourierChar (phase * lattice.rationalQuadraticSpaceMatrix.realQuadraticFormValue
      vector) : ℂ) * polarRealGaussian lattice parameter vector =
      polarRealGaussian lattice (parameter - (phase : ℂ) * Complex.I) vector := by
  rw [polarRealGaussian, polarRealGaussian,
    realCoordinateGaussian_eq_exp_dotProduct, realCoordinateGaussian_eq_exp_dotProduct,
    lattice.dotProduct_polarRealSqrtMatrix_mulVec]
  have hpolar : lattice.rationalQuadraticSpaceMatrix.realPolarMatrix =
      (2 : ℝ) • lattice.rationalQuadraticSpaceMatrix.realFormMatrix := by
    ext row column
    simp [realPolarMatrix, realFormMatrix, polarMatrix]
  rw [hpolar]
  simp only [realQuadraticFormValue, Matrix.smul_mulVec, dotProduct_smul]
  rw [Real.fourierChar_apply]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem rationalAdeleRankOneQuadraticPhase_real_only
    (space : RationalQuadraticSpaceMatrix rank) (phase : ℝ)
    (vector : Fin rank → RationalAdele) :
    (space.rationalAdeleRankOneQuadraticPhase
      (rationalInfiniteAdeleRingEquivReal.symm phase, 0) vector : ℂ) =
      (Real.fourierChar (phase * space.realQuadraticFormValue
        (rationalAdeleVectorRealPart rank vector)) : ℂ) := by
  unfold rationalAdeleRankOneQuadraticPhase
  rw [rationalAdeleFourierChar_apply, rationalAdeleArchimedeanFourierChar_apply]
  have hreal : rationalInfiniteAdeleContinuousAddEquivReal
      (rationalInfiniteAdeleRingEquivReal.symm phase *
        (space.fullAdelicQuadraticFormValue vector).1) =
      phase * space.realQuadraticFormValue (rationalAdeleVectorRealPart rank vector) := by
    change rationalInfiniteAdeleRingEquivReal
      (rationalInfiniteAdeleRingEquivReal.symm phase * _) = _
    rw [map_mul, RingEquiv.apply_symm_apply]
    exact congrArg (phase * ·) (space.rationalAdeleVectorRealPart_fullAdelicQuadraticFormValue vector)
  change ((Real.fourierChar (rationalInfiniteAdeleContinuousAddEquivReal
    (rationalInfiniteAdeleRingEquivReal.symm phase * (space.fullAdelicQuadraticFormValue vector).1)) *
    rationalFiniteAdeleFourierChar (0 * (space.fullAdelicQuadraticFormValue vector).2) : Circle) : ℂ) = _
  rw [hreal]
  simp

def rationalAdeleRealCuspGaussianLatticeTest (lattice : PositiveDefiniteIntegralLattice rank)
    (gaussianScale dilation phase : ℝ) : (Fin rank → RationalAdele) → ℂ :=
  lattice.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator
    (rationalInfiniteAdeleRingEquivReal.symm phase, 0)
    (fun vector ↦ ((dilation ^ ((rank : ℝ) / 2) : ℝ) : ℂ) *
      rationalAdeleVectorPolarGaussianLatticeTest lattice (gaussianScale : ℂ)
        (rationalAdeleRealDilationVector dilation vector))

theorem rationalAdeleRealCuspGaussianLatticeTest_eq (lattice : PositiveDefiniteIntegralLattice rank)
    (gaussianScale dilation phase : ℝ) :
    rationalAdeleRealCuspGaussianLatticeTest lattice gaussianScale dilation phase =
      fun vector ↦ ((dilation ^ ((rank : ℝ) / 2) : ℝ) : ℂ) *
        rationalAdeleVectorPolarGaussianLatticeTest lattice
          ((gaussianScale : ℂ) * (dilation : ℂ) ^ 2 - (phase : ℂ) * Complex.I) vector := by
  funext vector
  unfold rationalAdeleRealCuspGaussianLatticeTest rationalAdeleRankOneUnipotentOperator
  rw [rationalAdeleRankOneQuadraticPhase_real_only]
  simp only [rationalAdeleVectorPolarGaussianLatticeTest,
    realPart_rationalAdeleRealDilationVector, finitePart_rationalAdeleRealDilationVector,
    polarRealGaussian_real_dilation]
  rw [← realQuadraticPhase_mul_polarRealGaussian_real]
  ring

theorem rationalAdeleRealCuspGaussianLatticeTest_zero
    (lattice : PositiveDefiniteIntegralLattice rank) (gaussianScale dilation phase : ℝ) :
    rationalAdeleRealCuspGaussianLatticeTest lattice gaussianScale dilation phase 0 =
      ((dilation ^ ((rank : ℝ) / 2) : ℝ) : ℂ) := by
  rw [rationalAdeleRealCuspGaussianLatticeTest_eq]
  change _ * rationalAdeleVectorPolarGaussianLatticeTest lattice _ 0 = _
  rw [rationalAdeleVectorPolarGaussianLatticeTest]
  have hreal : rationalAdeleVectorRealPart rank (0 : Fin rank → RationalAdele) = 0 := by
    funext index
    change rationalInfiniteAdeleContinuousAddEquivReal 0 = 0
    exact map_zero _
  have hfinite : rationalAdeleVectorFinitePart rank (0 : Fin rank → RationalAdele) = 0 := by
    funext index
    rfl
  have hintegral : (0 : Fin rank → RationalFiniteAdele) ∈ integralFiniteAdeleVectors rank := by
    intro index
    exact Subring.zero_mem integralFiniteAdeleSubring
  rw [hreal, hfinite, rationalFiniteAdeleVectorIntegralIndicator_of_mem hintegral]
  simp [polarRealGaussian, realCoordinateGaussian]

theorem integrable_rationalAdeleRealCuspGaussianLatticeTest
    (lattice : PositiveDefiniteIntegralLattice rank) {gaussianScale dilation : ℝ}
    (hgaussian : 0 < gaussianScale) (hdilation : 0 < dilation) (phase : ℝ) :
    Integrable (rationalAdeleRealCuspGaussianLatticeTest lattice gaussianScale dilation phase)
      (rationalAdeleCoordinateAddHaarMeasure rank) := by
  rw [rationalAdeleRealCuspGaussianLatticeTest_eq]
  apply Integrable.const_mul
  apply integrable_rationalAdeleVectorPolarGaussianLatticeTest _ lattice
  simpa only [← Complex.ofReal_pow, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero] using mul_pos hgaussian (sq_pos_of_pos hdilation)

theorem rationalAdeleRankOneBruhatCoefficient_const_mul
    (space : RationalQuadraticSpaceMatrix rank) (amplitude : ℂ)
    (test : (Fin rank → RationalAdele) → ℂ) (frequency : ℚ) :
    space.rationalAdeleRankOneBruhatCoefficient (fun vector ↦ amplitude * test vector) frequency =
      amplitude * space.rationalAdeleRankOneBruhatCoefficient test frequency := by
  unfold rationalAdeleRankOneBruhatCoefficient rationalAdeleRankOneWeylOperator
  rw [Fourier.fourierIntegral_def, Fourier.fourierIntegral_def]
  simp only [Matrix.mulVec_zero, mul_zero, neg_zero, AddChar.map_zero_eq_one,
    one_smul, rationalAdeleRankOneUnipotentOperator]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun vector ↦ by ring

theorem rationalAdeleRealCuspGaussianLatticeTest_bruhat
    (lattice : PositiveDefiniteIntegralLattice rank) {gaussianScale dilation : ℝ}
    (hgaussian : 0 < gaussianScale) (hdilation : 0 < dilation)
    (phase : ℝ) (frequency : ℚ) :
    lattice.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
      (rationalAdeleRealCuspGaussianLatticeTest lattice gaussianScale dilation phase) frequency =
      ((dilation ^ ((rank : ℝ) / 2) : ℝ) : ℂ) *
        (((lattice.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((gaussianScale : ℂ) * (dilation : ℂ) ^ 2 -
            ((phase : ℂ) + (frequency : ℂ)) * Complex.I) ^ (1 / 2 : ℂ)) ^ rank) *
          lattice.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral frequency) := by
  rw [rationalAdeleRealCuspGaussianLatticeTest_eq, rationalAdeleRankOneBruhatCoefficient_const_mul,
    rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finite
      lattice (by simpa only [← Complex.ofReal_pow, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero] using mul_pos hgaussian (sq_pos_of_pos hdilation))]
  rw [show (gaussianScale : ℂ) * (dilation : ℂ) ^ 2 - (phase : ℂ) * Complex.I -
      (frequency : ℂ) * Complex.I = (gaussianScale : ℂ) * (dilation : ℂ) ^ 2 -
        ((phase : ℂ) + (frequency : ℂ)) * Complex.I by ring]

end RationalQuadraticSpaceMatrix
