import SMSFormula.RationalAdeleWeylTransformThetaFiniteness

/-!
# The Weyl transform of the standard test is nonnegative real at a real width

At a real width the standard polar Gaussian--lattice test is already known to be a nonnegative
real number at every point.  Its polar Weyl transform is, by the existing identification, a
constant multiple of the dual-carrier test at the reciprocal width, and at a real width both
factors are nonnegative reals: the constant is a reciprocal determinant scale times a real
half-power, and the dual-carrier test is a real Gaussian times a zero-one indicator.

Consequently the existing nonnegative test `weylStandardTestENNReal`, which is by definition the
modulus of the Weyl transform, loses no information: its real value coerces back to the complex
Weyl transform itself.  That is what lets the complex layer and the nonnegative layer be
compared at the Weyl transform, exactly as they already are at the standard test.

Negative scope: this is a pointwise positivity statement.  No theta, cutoff integral, covariance
or separation statement is made here, and no new test function is introduced -- both objects
named are the existing ones.
-/

noncomputable section

open Matrix MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- At a real width the dual-carrier test is a nonnegative real number, so it equals the real
coercion of its own complex norm. -/
theorem rationalAdeleVectorPolarGaussianDualTest_ofReal_eq_coe_norm
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianDualTest L (a : ℂ) x =
      (‖rationalAdeleVectorPolarGaussianDualTest L (a : ℂ) x‖ : ℂ) := by
  by_cases hx : L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
      (rationalAdeleVectorFinitePart n x) ∈ integralFiniteAdeleVectors n
  · rw [rationalAdeleVectorPolarGaussianDualTest,
      RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem _
        ((RationalQuadraticSpaceMatrix.mem_finitePolarDualLattice_iff _ _).2 hx),
      mul_one, L.polarRealGaussian_ofReal]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · rw [rationalAdeleVectorPolarGaussianDualTest,
      RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _
        (fun hmem ↦ hx ((RationalQuadraticSpaceMatrix.mem_finitePolarDualLattice_iff _ _).1 hmem)),
      mul_zero, norm_zero, Complex.ofReal_zero]

/-- The existing constant relating the Weyl transform to the dual-carrier test is, at a real
positive width, the coercion of a nonnegative real. -/
theorem polarRealDeterminantScale_halfPower_ofReal
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / (a : ℂ) ^ (1 / 2 : ℂ)) ^ n) =
      (((L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ n : ℝ) : ℂ) := by
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hcpow : ((a ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (a : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Complex.ofReal_cpow ha.le, hhalf]
  push_cast
  rw [← hcpow]

/-- The existing constant is nonnegative at a real positive width. -/
theorem polarRealDeterminantScale_halfPower_nonneg
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    0 ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ n :=
  mul_nonneg (inv_nonneg.2 L.polarRealDeterminantScale.coe_nonneg)
    (pow_nonneg (by positivity) n)

/-- The positivity: at a real positive width the polar Weyl transform of the standard test is a
nonnegative real number at every point, so it equals the real coercion of its own norm. -/
theorem rationalAdeleRankOneWeylOperator_polarGaussianLatticeTest_ofReal_eq_coe_norm
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (y : Fin n → RationalAdele) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) y =
      (‖L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) y‖ : ℂ) := by
  have hb : 0 < ((a : ℂ)).re := by simpa using ha
  have hinv : ((a : ℂ))⁻¹ = ((a⁻¹ : ℝ) : ℂ) := by push_cast; ring
  have hval : L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
      (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) y =
      (((L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ n : ℝ) : ℂ) *
        rationalAdeleVectorPolarGaussianDualTest L ((a⁻¹ : ℝ) : ℂ) y := by
    rw [RationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator_polarGaussianLattice L hb,
      rationalAdeleVectorPolarGaussianLatticeFourierProduct_eq_const_mul_dualTest, hinv,
      L.polarRealDeterminantScale_halfPower_ofReal ha]
  rw [hval, L.rationalAdeleVectorPolarGaussianDualTest_ofReal_eq_coe_norm a⁻¹ y,
    ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (L.polarRealDeterminantScale_halfPower_nonneg ha) (norm_nonneg _))]

/-- The bridge: the existing nonnegative Weyl-transform test loses no information.  Its real
value coerces back to the existing complex Weyl transform of the standard test, exactly as the
nonnegative standard test coerces back to the complex standard test. -/
theorem weylStandardTestENNReal_toReal
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (y : Fin n → RationalAdele) :
    (((L.weylStandardTestENNReal a y).toReal : ℝ) : ℂ) =
      L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) y := by
  rw [weylStandardTestENNReal, ENNReal.toReal_ofReal (norm_nonneg _)]
  exact (L.rationalAdeleRankOneWeylOperator_polarGaussianLatticeTest_ofReal_eq_coe_norm ha y).symm

end PositiveDefiniteIntegralLattice

end
