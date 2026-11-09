import SMSFormula.RationalAdeleRealCuspGaussianFactorization
import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeSummability

noncomputable section

open PositiveDefiniteIntegralLattice Matrix

namespace RationalQuadraticSpaceMatrix

variable {rank : ℕ}

theorem standardTest_ne_zero_finitePart_integral
    (lattice : PositiveDefiniteIntegralLattice rank) (parameter : ℂ) (vector : Fin rank → RationalAdele)
    (htest : rationalAdeleVectorPolarGaussianLatticeTest lattice parameter vector ≠ 0) :
    rationalAdeleVectorFinitePart rank vector ∈ integralFiniteAdeleVectors rank := by
  by_contra hnonintegral
  apply htest
  rw [rationalAdeleVectorPolarGaussianLatticeTest,
    rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hnonintegral, mul_zero]

theorem rational_shell_integer_of_finitePart_integral
    (lattice : PositiveDefiniteIntegralLattice rank) (vector : Fin rank → RationalAdele) (value : ℚ)
    (hvalue : lattice.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue vector =
      algebraMap ℚ RationalAdele value)
    (hintegral : rationalAdeleVectorFinitePart rank vector ∈ integralFiniteAdeleVectors rank) :
    ∃ integer : ℤ, (integer : ℚ) = value := by
  have hfinite : lattice.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
      (rationalAdeleVectorFinitePart rank vector) = algebraMap ℚ RationalFiniteAdele value := by
    rw [← rationalAdeleVectorFinitePart_fullAdelicQuadraticFormValue, hvalue]
    rfl
  have hform : lattice.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
      (rationalAdeleVectorFinitePart rank vector) ∈ integralFiniteAdeleSubring := by
    simpa [finiteAdelicQuadraticFormValue] using
      lattice.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring _ _ hintegral hintegral
  rw [hfinite] at hform
  exact (rational_mem_integralFiniteAdeleSubring_iff value).mp hform

theorem realQuadraticFormValue_nonneg_standard
    (lattice : PositiveDefiniteIntegralLattice rank) (vector : Fin rank → ℝ) :
    0 ≤ lattice.rationalQuadraticSpaceMatrix.realQuadraticFormValue vector := by
  have hpos := lattice.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.posSemidef.dotProduct_mulVec_nonneg vector
  rw [realPolarMatrix_eq_two_smul_realFormMatrix, Matrix.smul_mulVec, dotProduct_smul] at hpos
  change 0 ≤ (2 : ℝ) * lattice.rationalQuadraticSpaceMatrix.realQuadraticFormValue vector at hpos
  linarith

theorem one_le_rational_shell_of_standardTest_ne_zero
    (lattice : PositiveDefiniteIntegralLattice rank) (parameter : ℂ) (vector : Fin rank → RationalAdele)
    (value : ℚ) (hvalue : lattice.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue vector =
      algebraMap ℚ RationalAdele value) (hnonzero : value ≠ 0)
    (htest : rationalAdeleVectorPolarGaussianLatticeTest lattice parameter vector ≠ 0) :
    1 ≤ value := by
  obtain ⟨integer, hinteger⟩ := rational_shell_integer_of_finitePart_integral lattice vector value hvalue
    (standardTest_ne_zero_finitePart_integral lattice parameter vector htest)
  have hreal : lattice.rationalQuadraticSpaceMatrix.realQuadraticFormValue
      (rationalAdeleVectorRealPart rank vector) = (value : ℝ) := by
    rw [← rationalAdeleVectorRealPart_fullAdelicQuadraticFormValue, hvalue]
    exact rationalInfiniteAdeleContinuousAddEquivReal_algebraMap value
  have hnonneg := realQuadraticFormValue_nonneg_standard lattice (rationalAdeleVectorRealPart rank vector)
  rw [hreal] at hnonneg
  have hnonnegRat : (0 : ℚ) ≤ value := by exact_mod_cast hnonneg
  have hpos : (0 : ℚ) < value := lt_of_le_of_ne hnonnegRat hnonzero.symm
  rw [← hinteger] at hpos ⊢
  have hposInt : (0 : ℤ) < integer := by exact_mod_cast hpos
  exact_mod_cast (show (1 : ℤ) ≤ integer by omega)

theorem one_le_rational_shell_of_realCuspTest_ne_zero
    (lattice : PositiveDefiniteIntegralLattice rank) (gaussianScale dilation phase : ℝ)
    (vector : Fin rank → RationalAdele) (value : ℚ)
    (hvalue : lattice.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue vector =
      algebraMap ℚ RationalAdele value) (hnonzero : value ≠ 0)
    (htest : rationalAdeleRealCuspGaussianLatticeTest lattice gaussianScale dilation phase vector ≠ 0) :
    1 ≤ value := by
  rw [rationalAdeleRealCuspGaussianLatticeTest_eq] at htest
  exact one_le_rational_shell_of_standardTest_ne_zero lattice _ vector value hvalue hnonzero
    (mul_ne_zero_iff.mp htest).2

theorem fullAdelicQuadraticFormValue_generalSpinRationalAction
    (space : RationalQuadraticSpaceMatrix rank) (groupElement : space.FullAdelicCliffordGeneralSpinGroup)
    (vector : Fin rank → ℚ) :
    space.fullAdelicQuadraticFormValue
      (space.fullAdelicCliffordGeneralSpinRationalVectorAction groupElement vector) =
      algebraMap ℚ RationalAdele (space.nativeRationalQuadraticForm vector) := by
  have hconj : (groupElement.matrixGroup⁻¹).1.1.1.transpose * space.fullAdelicFormMatrix *
      (groupElement.matrixGroup⁻¹).1.1.1 = space.fullAdelicFormMatrix := by
    exact (groupElement.matrixGroup⁻¹).1.2
  rw [fullAdelicQuadraticFormValue_eq_dotProduct, fullAdelicCliffordGeneralSpinRationalVectorAction,
    dotProduct_mulVec_eq_of_matrix_conj hconj]
  simpa only [fullAdelicQuadraticFormValue_eq_dotProduct] using
    space.fullAdelicQuadraticFormValue_rationalDiagonal vector

theorem one_le_standardTheta_supported_nonzero_norm
    (lattice : PositiveDefiniteIntegralLattice rank) (gaussianScale dilation phase : ℝ)
    (groupElement : lattice.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (vector : Fin rank → ℚ) (hnonzero : lattice.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm vector ≠ 0)
    (htest : rationalAdeleRealCuspGaussianLatticeTest lattice gaussianScale dilation phase
      (lattice.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRationalVectorAction groupElement vector) ≠ 0) :
    1 ≤ lattice.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm vector :=
  one_le_rational_shell_of_realCuspTest_ne_zero lattice gaussianScale dilation phase _ _
    (fullAdelicQuadraticFormValue_generalSpinRationalAction _ groupElement vector) hnonzero htest

end RationalQuadraticSpaceMatrix
