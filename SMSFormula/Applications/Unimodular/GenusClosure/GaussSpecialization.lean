import SMSFormula.Applications.Unimodular.GenusClosure.BinaryGauss
import SMSFormula.RationalAdeleRankOneFiniteGaussReciprocity
import SMSFormula.RationalAdeleGaussRamanujanCoefficient
import SMSFormula.Applications.Unimodular.Gram

noncomputable section

namespace UnimodularGenusClosure
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped BigOperators

theorem quarticPhase_eq_stdAddChar (value : R4) :
    quarticPhase value = ZMod.stdAddChar value := by
  have hgenerator : ZMod.stdAddChar (1 : R4) = Complex.I := by
    calc
      _ = Complex.exp (2 * Real.pi * Complex.I * (1 : ℤ) / (4 : ℕ)) := by
        simpa only [Int.cast_one] using (ZMod.stdAddChar_coe (N := 4) (1 : ℤ))
      _ = Complex.I := by
        convert Complex.exp_pi_div_two_mul_I using 1
        congr 1
        push_cast
        ring
  calc
    quarticPhase value = ZMod.stdAddChar (1 : R4) ^ value.val := by
      rw [quarticPhase, hgenerator]
    _ = ZMod.stdAddChar (value.val • (1 : R4)) := by
      rw [AddChar.map_nsmul_eq_pow]
    _ = ZMod.stdAddChar value := by simp [nsmul_eq_mul]

theorem quarterIntegralPhase_eq_quarticPhase {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (vector : Fin n → ℤ) :
    rationalFiniteAdeleIntegralQuadraticPhase lattice (1 / 4) (integerToIntegralFiniteAdeleVector n vector) =
      quarticPhase (-(lattice.quadForm vector : R4)) := by
  rw [lattice.rationalFiniteAdeleIntegralQuadraticPhase_integerVector,
    quarticPhase_eq_stdAddChar]
  convert PositiveDefiniteIntegralLattice.fourierChar_intDiv_inv_eq_stdAddChar 4
    (lattice.quadForm vector) using 1; congr 3; push_cast; ring

theorem standardGaussIntegral_int_eq_one {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (value : ℤ) :
    lattice.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
      (value : ℚ) = 1 := by
  have hzero : (default : ZMod 1) = 0 := Subsingleton.elim _ _
  simpa [PositiveDefiniteIntegralLattice.zmodQuadForm, hzero] using
    (lattice.rationalFiniteAdeleQuadraticGaussIntegral_intDiv_eq_levelSum 1 value)

theorem sqrt_two_mul_principal_neg_I :
    (Real.sqrt 2 : ℂ) * (-Complex.I) ^ (1 / 2 : ℂ) = 1 - Complex.I := by
  have hre := Complex.cpow_inv_two_re (-Complex.I)
  have him := Complex.cpow_inv_two_im_eq_neg_sqrt
    (by norm_num : (-Complex.I).im < 0)
  norm_num at hre him
  simp only [one_div] at hre him
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, one_div, hre, him, hsqrt]

theorem sqrt_two_pow (rank : ℕ) : Real.sqrt ((2 : ℝ) ^ rank) = Real.sqrt 2 ^ rank := by
  induction rank with
  | zero => simp
  | succ rank ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) rank),
        ih, pow_succ]

theorem polarScale_of_unimodular {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) :
    (lattice.polarRealDeterminantScale : ℝ) = Real.sqrt 2 ^ n := by
  rw [lattice.coe_polarRealDeterminantScale,
    lattice.rationalQuadraticSpaceMatrix_realPolarMatrix_det,
    lattice.polarDeterminant_eq_two_pow_of_isUnimodular hunimodular]
  simpa only [Int.cast_pow, Int.cast_ofNat] using sqrt_two_pow n

theorem dualGaussIntegral_one_of_unimodular {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hn : n ≠ 0) (hunimodular : lattice.IsUnimodular) :
    lattice.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral 1 =
      (1 - Complex.I) ^ n := by
  have hstandard :
      lattice.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral (-1) = 1 := by
    simpa using standardGaussIntegral_int_eq_one lattice (-1)
  have hscale : (lattice.polarRealDeterminantScale : ℂ) = (Real.sqrt 2 : ℂ) ^ n := by
    exact_mod_cast polarScale_of_unimodular lattice hunimodular
  calc
    _ = (lattice.polarRealDeterminantScale : ℂ) *
        ((-Complex.I) ^ (1 / 2 : ℂ)) ^ n := by
      simpa only [Rat.cast_one, Complex.ofReal_one, neg_one_mul, inv_one, hstandard,
        mul_one] using lattice.rationalFiniteAdeleQuadraticGaussReciprocity hn
          (t := 1) (by norm_num)
    _ = (1 - Complex.I) ^ n := by
      rw [hscale, ← mul_pow, sqrt_two_mul_principal_neg_I]

#assert_standard_axioms quarticPhase_eq_stdAddChar
#assert_standard_axioms quarterIntegralPhase_eq_quarticPhase
#assert_standard_axioms standardGaussIntegral_int_eq_one
#assert_standard_axioms sqrt_two_mul_principal_neg_I
#assert_standard_axioms dualGaussIntegral_one_of_unimodular

end UnimodularGenusClosure
