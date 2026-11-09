import SMSFormula.RationalAdeleCongruenceThetaNormalization

/-!
# Congruence-class Poisson with the Fourier integrals

Connect the exact centered-theta normalization to the negative real Fourier
integral and the finite character on the quotient. The sign change between
the finite and real characters is explicit.
-/

noncomputable section
open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ}

/-- The existing real Fourier integral at an arbitrary frequency, in inverse
matrix coordinates and with its original determinant coefficient. -/
theorem fourierIntegral_polarGaussian_eq_inverseMatrix_exp
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (w : Fin n → ℝ) :
    Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b) w =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ * realGaussianFourierCoefficient n b) *
        Complex.exp (-Real.pi * b⁻¹ *
          ((w ⬝ᵥ L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹.mulVec w : ℝ) : ℂ)) := by
  let S := L.rationalQuadraticSpaceMatrix.realPolarMatrix
  have hcancel : S.mulVec (S⁻¹.mulVec w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S
      (isUnit_iff_ne_zero.mpr L.rationalQuadraticSpaceMatrix.realPolarMatrix_det_ne_zero),
      Matrix.one_mulVec]
  rw [polarReal_fourierIntegral_gaussian_arbitraryFrequency hb,
    polarRealGaussianFourierProduct, realCoordinateGaussianFourierProduct_eq_const_mul]
  change (L.polarRealDeterminantScale : ℂ)⁻¹ *
      (realGaussianFourierCoefficient n b * polarRealGaussian L b⁻¹ (S⁻¹.mulVec w)) = _
  rw [polarRealGaussian_eq_exp_polar, hcancel, dotProduct_comm (S⁻¹.mulVec w) w]
  ring

/-- The divided diagonal produces precisely the inverse width `1/(b*N^2)`.
This formula uses the actual Fourier integral, not an abstract coefficient. -/
theorem fourierIntegral_polarGaussian_dividedInteger
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    {N : ℕ} (_hN : N ≠ 0) (k : Fin n → ℤ) :
    Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
        (rationalRealVector n (rationalScaledIntegerVector N k)) =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ * realGaussianFourierCoefficient n b) *
        shiftedMatrixGaussianSummand L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
          (b * (N : ℂ) ^ 2)⁻¹ 0 k := by
  rw [fourierIntegral_polarGaussian_eq_inverseMatrix_exp L hb]
  congr 1
  have harg : rationalRealVector n (rationalScaledIntegerVector N k) =
      (N : ℝ)⁻¹ • integerVectorReal k := by
    ext i
    simp [rationalRealVector, rationalScaledIntegerVector, integerVectorReal, div_eq_mul_inv,
      mul_comm]
  rw [harg, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, shiftedMatrixGaussianSummand, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, mul_zero, add_zero]
  congr 1
  push_cast
  simp only [_root_.mul_inv_rev]
  ring

/-- Twisting the divided Fourier output by the real character gives the
existing purely imaginary linear summand, with no extra phase. -/
theorem fourierIntegral_polarGaussian_dividedInteger_mul_char
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    {N : ℕ} (hN : N ≠ 0) (r : Fin n → ℝ) (k : Fin n → ℤ) :
    Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
        (rationalRealVector n (rationalScaledIntegerVector N k)) *
        (Real.fourierChar (r ⬝ᵥ integerVectorReal k) : ℂ) =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ * realGaussianFourierCoefficient n b) *
        shiftedMatrixGaussianSummand L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
          (b * (N : ℂ) ^ 2)⁻¹ (pureImaginaryLinear r) k := by
  rw [fourierIntegral_polarGaussian_dividedInteger L hb hN,
    shiftedMatrixGaussianSummand, shiftedMatrixGaussianSummand]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
    Real.fourierChar_apply, mul_assoc, ← Complex.exp_add]
  congr 2
  congr 1
  simp only [dotProduct, integerVectorReal, pureImaginaryLinear]
  push_cast
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

/-- Reversing the integer index reverses the imaginary twist and preserves
its quadratic part. -/
theorem shiftedMatrixGaussianSummand_neg_index (S : Matrix (Fin n) (Fin n) ℝ)
    (b : ℂ) (r : Fin n → ℝ) (k : Fin n → ℤ) :
    shiftedMatrixGaussianSummand S b (pureImaginaryLinear (-r)) (-k) =
      shiftedMatrixGaussianSummand S b (pureImaginaryLinear r) k := by
  have hvec : integerVectorReal (-k) = -integerVectorReal k := by
    ext i
    simp [integerVectorReal]
  simp only [shiftedMatrixGaussianSummand, hvec, Matrix.mulVec_neg, neg_dotProduct,
    dotProduct_neg, neg_neg, pureImaginaryLinear, Pi.neg_apply, Complex.ofReal_neg,
    Int.cast_neg]
  congr 1
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Poisson for one integer congruence class, using the actual real Fourier
integral. The finite-volume factor `N^-n` is explicit. -/
theorem tsum_integerCongruence_polarGaussian_eq_fourierIntegral
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    {N : ℕ} (hN : N ≠ 0) (m' : Fin n → ℤ) :
    (∑' m : Fin n → ℤ,
      polarRealGaussian L b (rationalRealVector n (fun i => ((m i : ℤ) : ℚ))) *
        integerCongruenceIndicator n N m' m) =
      (N : ℂ)⁻¹ ^ n * ∑' k : Fin n → ℤ,
        Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
          (rationalRealVector n (rationalScaledIntegerVector N k)) *
          (Real.fourierChar ((fun i => (m' i : ℝ) / (N : ℝ)) ⬝ᵥ integerVectorReal k) : ℂ) := by
  let r : Fin n → ℝ := fun i => (m' i : ℝ) / (N : ℝ)
  let C : ℂ := (L.polarRealDeterminantScale : ℂ)⁻¹ * realGaussianFourierCoefficient n b
  let T := shiftedMatrixGaussianSummand L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
    (b * (N : ℂ) ^ 2)⁻¹
  have hneg : (∑' k : Fin n → ℤ, T (pureImaginaryLinear (-r)) k) =
      ∑' k : Fin n → ℤ, T (pureImaginaryLinear r) k := by
    rw [← (Equiv.neg (Fin n → ℤ)).tsum_eq]
    exact tsum_congr fun k => shiftedMatrixGaussianSummand_neg_index _ _ r k
  calc
    _ = (N : ℂ)⁻¹ ^ n * C * ∑' k : Fin n → ℤ, T (pureImaginaryLinear (-r)) k :=
      tsum_integerCongruence_polarGaussian_eq_twisted_inv L hb hN m'
    _ = (N : ℂ)⁻¹ ^ n * (C * ∑' k : Fin n → ℤ, T (pureImaginaryLinear r) k) := by
      rw [hneg, mul_assoc]
    _ = (N : ℂ)⁻¹ ^ n * ∑' k : Fin n → ℤ, C * T (pureImaginaryLinear r) k := by
      rw [tsum_mul_left]
    _ = _ := congrArg ((N : ℂ)⁻¹ ^ n * ·) (tsum_congr fun k =>
      (fourierIntegral_polarGaussian_dividedInteger_mul_char L hb hN r k).symm)

/-- On rational frequencies the native negative finite character is the
positive real twist, by the already fixed global character convention. -/
theorem standardQuotientDualChar_integer_class {N : ℕ} (hN : N ≠ 0)
    (m' k : Fin n → ℤ) :
    standardQuotientDualChar n hN k
      ((integerToIntegralFiniteAdeleVector n m' : (Fin n → IntegralFiniteAdele) ⧸
        (integralFiniteAdeleCoordinateNatDilation n N).range)) =
      (Real.fourierChar ((fun i => (m' i : ℝ) / (N : ℝ)) ⬝ᵥ integerVectorReal k) : ℂ) := by
  rw [standardQuotientDualChar_coe]
  have harg :
      -(dotProduct (fun i => ((integerToIntegralFiniteAdeleVector n m' i :
        IntegralFiniteAdele) : RationalFiniteAdele))
        (rationalFiniteAdeleVectorDiagonal n (rationalScaledIntegerVector N k))) =
      algebraMap ℚ RationalFiniteAdele
        (-(∑ i, (m' i : ℚ) * ((k i : ℚ) / (N : ℚ)))) := by
    simp [dotProduct, integerToIntegralFiniteAdeleVector, integerToIntegralFiniteAdele,
      rationalFiniteAdeleVectorDiagonal, rationalScaledIntegerVector, map_sum]
  rw [harg, rationalFiniteAdeleFourierChar_algebraMap, Rat.cast_neg,
    AddChar.map_neg_eq_inv, inv_inv]
  congr 2
  simp only [dotProduct, integerVectorReal]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Poisson for an integer-supplied class, as two rational-diagonal sums of
actual real and finite Fourier transforms. No representative function occurs. -/
theorem tsum_polarGaussian_standardCoset_poisson_integerClass
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    {N : ℕ} (hN : N ≠ 0) (m' : Fin n → ℤ) :
    (∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
      standardCosetIndicator n N
        ((integerToIntegralFiniteAdeleVector n m' : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range))
        (rationalFiniteAdeleVectorDiagonal n q)) =
    ∑' q : Fin n → ℚ,
      Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
        (rationalRealVector n q) *
      standardFiniteFourier (standardCosetIndicator n N
        ((integerToIntegralFiniteAdeleVector n m' : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range)))
        (rationalFiniteAdeleVectorDiagonal n q) := by
  rw [tsum_rationalDiagonal_standardCosetIndicator hN,
    tsum_integerCongruence_polarGaussian_eq_fourierIntegral L hb hN]
  rw [tsum_rationalDiagonal_mul hN
    (isStandardPeriodic_standardCosetIndicator n hN _).isStandardCarried_standardFiniteFourier]
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [standardFiniteFourier_standardCosetIndicator n hN
    (inv_ne_zero (Nat.cast_ne_zero.mpr hN)),
    nsmul_rationalScaledIntegerVector_diagonal hN,
    rationalFiniteAdeleVectorIntegralIndicator_of_mem
      (integerDiagonal_mem_integralFiniteAdeleVectors k)]
  rw [← standardQuotientDualChar_coe n hN k, standardQuotientDualChar_integer_class hN]
  ring

/-- Every class is covered by the old integer surjectivity theorem. The
existential witness is eliminated locally, with no stored representatives. -/
theorem tsum_polarGaussian_standardCoset_poisson
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    {N : ℕ} (hN : N ≠ 0)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range) :
    (∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
      standardCosetIndicator n N alpha (rationalFiniteAdeleVectorDiagonal n q)) =
    ∑' q : Fin n → ℚ,
      Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
        (rationalRealVector n q) *
      standardFiniteFourier (standardCosetIndicator n N alpha)
        (rationalFiniteAdeleVectorDiagonal n q) := by
  induction alpha using Quotient.inductionOn' with
  | _ y =>
    obtain ⟨m', hm'⟩ := exists_integerVector_quotient_eq hN y
    have h := tsum_polarGaussian_standardCoset_poisson_integerClass L hb hN m'
    rw [hm'] at h
    exact h

end RationalQuadraticSpaceMatrix
