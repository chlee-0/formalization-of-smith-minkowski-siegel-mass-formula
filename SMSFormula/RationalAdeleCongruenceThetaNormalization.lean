import SMSFormula.RationalAdeleCongruenceClassThetaInput
import SMSFormula.RealPolarGaussianOperators

/-!
# Exact complex normalization for congruence-class theta sums

The principal root at width `b * N^2` contributes exactly `N^-n`.
Inverting both the matrix and the width in the existing twisted theta theorem
then evaluates the centered theta input, with the old polar determinant factor.
No Haar normalization, representative, limiting argument or phase product is used.
-/

noncomputable section
open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Positive real dilation stays on the principal square-root branch. -/
theorem cpow_half_mul_nat_sq {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0) :
    (b * (N : ℂ) ^ 2) ^ (1 / 2 : ℂ) = b ^ (1 / 2 : ℂ) * (N : ℂ) := by
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have h := cpow_half_mul_posReal b hb ((N : ℝ) ^ 2) (sq_pos_of_pos hNR)
  simpa only [Complex.ofReal_pow, Complex.ofReal_natCast, Real.sqrt_sq hNR.le] using h

theorem complexShiftedMatrixThetaNormalization_nat_sq
    (S : Matrix (Fin n) (Fin n) ℝ) {b : ℂ} (hb : 0 < b.re)
    {N : ℕ} (hN : N ≠ 0) :
    complexShiftedMatrixThetaNormalization S (b * (N : ℂ) ^ 2) =
      (N : ℂ)⁻¹ ^ n * complexShiftedMatrixThetaNormalization S b := by
  unfold complexShiftedMatrixThetaNormalization
  rw [cpow_half_mul_nat_sq hb hN]
  simp only [Fintype.card_fin, mul_pow, one_div, _root_.mul_inv_rev, inv_pow]
  ring

/-- Matrix and width inversion give reciprocal normalizations, with the
principal-root branch justified by the positive real part. -/
theorem complexShiftedMatrixThetaNormalization_mul_inv
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {b : ℂ} (hb : 0 < b.re) :
    complexShiftedMatrixThetaNormalization S b *
      complexShiftedMatrixThetaNormalization S⁻¹ b⁻¹ = 1 := by
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hroot : b ^ (1 / 2 : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hb0)
  have hdet : (Real.sqrt S.det : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hS.det_pos).ne'
  have harg : b.arg ≠ Real.pi := (Complex.arg_lt_pi_iff.mpr (Or.inl hb.le)).ne
  simp only [complexShiftedMatrixThetaNormalization, Fintype.card_fin,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.sqrt_inv,
    Complex.ofReal_inv, Complex.inv_cpow b _ harg]
  simp only [one_div, inv_pow, _root_.mul_inv_rev]
  field_simp [hroot, hdet]
  exact div_self (pow_ne_zero n hroot)

/-- The existing twisted theta theorem, solved for its centered side. -/
theorem tsum_complexCenteredMatrixGaussianSummand_eq_twisted_inv
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {b : ℂ} (hb : 0 < b.re) (r : Fin n → ℝ) :
    (∑' z : Fin n → ℤ, complexCenteredMatrixGaussianSummand S b r z) =
      complexShiftedMatrixThetaNormalization S b *
        ∑' k : Fin n → ℤ,
          shiftedMatrixGaussianSummand S⁻¹ b⁻¹ (pureImaginaryLinear r) k := by
  have h := tsum_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear_eq_centered_inv
    n S⁻¹ hS.inv (inv_re_pos hb) r
  rw [Matrix.nonsing_inv_nonsing_inv S (isUnit_iff_ne_zero.mpr hS.det_pos.ne'),
    inv_inv] at h
  rw [h, ← mul_assoc, complexShiftedMatrixThetaNormalization_mul_inv S hS hb, one_mul]

/-- Exact match with the coefficient of the real polar Fourier transform. -/
theorem complexShiftedMatrixThetaNormalization_polar
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    complexShiftedMatrixThetaNormalization L.rationalQuadraticSpaceMatrix.realPolarMatrix b =
      (L.polarRealDeterminantScale : ℂ)⁻¹ * realGaussianFourierCoefficient n b := by
  change 1 / ((b ^ (1 / 2 : ℂ)) ^ Fintype.card (Fin n) *
    (Real.sqrt L.rationalQuadraticSpaceMatrix.realPolarMatrix.det : ℂ)) = _
  simp [realGaussianFourierCoefficient, one_div, _root_.mul_inv_rev, inv_pow,
    ← coe_polarRealDeterminantScale]

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The congruence-class theta sum equals the twisted inverse-matrix sum,
with exactly `N^-n` times the actual polar Fourier coefficient. -/
theorem tsum_integerCongruence_polarGaussian_eq_twisted_inv
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    {N : ℕ} (hN : N ≠ 0) (m' : Fin n → ℤ) :
    (∑' m : Fin n → ℤ,
      polarRealGaussian L b (rationalRealVector n (fun i => ((m i : ℤ) : ℚ))) *
        integerCongruenceIndicator n N m' m) =
      (N : ℂ)⁻¹ ^ n *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ * realGaussianFourierCoefficient n b) *
        ∑' k : Fin n → ℤ,
          shiftedMatrixGaussianSummand L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
            (b * (N : ℂ) ^ 2)⁻¹
            (pureImaginaryLinear (fun i => -((m' i : ℝ) / (N : ℝ)))) k := by
  have hwidth : 0 < (b * (N : ℂ) ^ 2).re := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using mul_pos hb (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN) :
      (0 : ℝ) < N))
  rw [tsum_integerCongruence_polarGaussian L b hN,
    tsum_complexCenteredMatrixGaussianSummand_eq_twisted_inv _
      L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef hwidth,
    complexShiftedMatrixThetaNormalization_nat_sq _ hb hN,
    complexShiftedMatrixThetaNormalization_polar]

end RationalQuadraticSpaceMatrix
