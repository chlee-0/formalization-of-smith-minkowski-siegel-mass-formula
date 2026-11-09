import SMSFormula.RationalAdeleArchimedeanLocalIntegralValue
import SMSFormula.RationalFiniteAdeleQuadraticGaussStrongApproximation

/-!
# The finite local integral vanishes at every non-integral frequency

The archimedean factor of the cusp coefficient is evaluated.  This file treats the finite
factor, and settles it completely at every frequency that is not a rational integer.

The argument is translation invariance, nothing else.  The existing finite Gauss integral
is invariant under adding an everywhere-integral finite adele, while the finite
character is not: translating the integration variable by `1` multiplies the integral by
the character value at the rational frequency.  That value is one exactly when the
frequency is an integer, so at every non-integral frequency the integral equals a
non-trivial multiple of itself and therefore vanishes.

Negative scope: this says nothing at an integral frequency, where the character value is
one and the identity is vacuous.  No Euler product is asserted, no local density is
computed, and no value of the integral is produced at any integral frequency.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Translating the finite local integrand by an everywhere-integral finite adele
multiplies the integral by one character value. -/
theorem integral_finiteLocal_eq_char_mul (L : PositiveDefiniteIntegralLattice n) (b : ℚ)
    {z : RationalFiniteAdele} (hz : z ∈ integralFiniteAdeleSubring) :
    (∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
        ∂rationalFiniteAdeleAddHaarMeasure) =
      ((rationalFiniteAdeleFourierChar
          (algebraMap ℚ RationalFiniteAdele (-b) * z) : Circle) : ℂ) *
        ∫ y : RationalFiniteAdele,
          ((rationalFiniteAdeleFourierChar
              (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
            L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
          ∂rationalFiniteAdeleAddHaarMeasure := by
  have hshift := integral_add_right_eq_self
    (μ := rationalFiniteAdeleAddHaarMeasure)
    (fun y : RationalFiniteAdele =>
      ((rationalFiniteAdeleFourierChar
          (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y) z
  conv_lhs => rw [← hshift]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [mul_add, AddChar.map_add_eq_mul, Circle.coe_mul,
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt_add_integral
      L y z hz]
  ring

/-- The finite local integral vanishes at every non-integral rational frequency. -/
theorem integral_finiteLocal_eq_zero_of_not_int (L : PositiveDefiniteIntegralLattice n) {b : ℚ}
    (hb : b ∉ (algebraMap ℤ ℚ).range) :
    (∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
        ∂rationalFiniteAdeleAddHaarMeasure) = 0 := by
  have hone : (1 : RationalFiniteAdele) ∈ integralFiniteAdeleSubring := one_mem _
  have h := L.integral_finiteLocal_eq_char_mul b hone
  rw [mul_one] at h
  have hchar : rationalFiniteAdeleFourierChar
      (algebraMap ℚ RationalFiniteAdele (-b)) ≠ 1 := by
    intro hc
    rw [rationalFiniteAdeleFourierChar_eq_one_iff,
      rational_mem_integralFiniteAdeleSubring_iff] at hc
    obtain ⟨m, hm⟩ := hc
    exact hb ⟨-m, by push_cast at hm ⊢; linarith⟩
  have hne : ((rationalFiniteAdeleFourierChar
      (algebraMap ℚ RationalFiniteAdele (-b)) : Circle) : ℂ) ≠ 1 := by
    intro hc
    exact hchar (Circle.coe_inj.mp (by rw [hc]; simp))
  have hsub : (1 - ((rationalFiniteAdeleFourierChar
      (algebraMap ℚ RationalFiniteAdele (-b)) : Circle) : ℂ)) *
      (∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
        ∂rationalFiniteAdeleAddHaarMeasure) = 0 := by
    rw [sub_mul, one_mul, ← h]
    ring
  rcases mul_eq_zero.mp hsub with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm hne
  · exact h2

/-- The rational quadratic value of an integral rational vector is an integer: the
form matrix of an `PositiveDefiniteIntegralLattice` is an integer matrix. -/
theorem nativeRationalQuadraticForm_mem_intRange (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
    (hx : x ∈ rationalIntegralVectors n) :
    L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ∈
      (algebraMap ℤ ℚ).range := by
  have hxi : ∀ i, x i ∈ (algebraMap ℤ ℚ).range := hx
  have hform : ∀ i j, L.rationalQuadraticSpaceMatrix.pairingMatrix i j ∈
      (algebraMap ℤ ℚ).range := fun i j => ⟨L.pairingMatrix i j, rfl⟩
  have heq : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x =
      ∑ i, x i * ∑ j, L.rationalQuadraticSpaceMatrix.pairingMatrix i j * x j := by
    simp [RationalQuadraticSpaceMatrix.nativeRationalQuadraticForm,
      RationalQuadraticSpaceMatrix.quadraticForm,
      Matrix.toQuadraticMap', Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply',
      Matrix.mulVec, dotProduct]
  rw [heq]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hxi i)
    (Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hform i j) (hxi j))

/-- The rational shell at a non-integral frequency contributes nothing: every integral
vector has an integral value, and every non-integral vector is killed by the
indicator. -/
theorem tsum_shell_eq_zero_of_not_int (L : PositiveDefiniteIntegralLattice n) (c : ℂ) {b : ℚ}
    (hb : b ∉ (algebraMap ℤ ℚ).range) :
    (∑' x : {x : Fin n → ℚ //
        L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = b},
      rationalAdeleVectorPolarGaussianLatticeTest L c
        (rationalAdeleVectorDiagonal n x.1)) = 0 := by
  have hzero : ∀ x : {x : Fin n → ℚ //
      L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = b},
      rationalAdeleVectorPolarGaussianLatticeTest L c
        (rationalAdeleVectorDiagonal n x.1) = 0 := by
    intro x
    by_cases hmem : x.1 ∈ rationalIntegralVectors n
    · exact absurd (x.2 ▸ L.nativeRationalQuadraticForm_mem_intRange hmem) hb
    · exact rationalAdeleVectorPolarGaussianLatticeTest_rationalDiagonal_eq_zero_of_not_mem
        L c x.1 hmem
  simp [hzero]

set_option maxHeartbeats 1000000 in
/-- The finite local Gauss integral is absolutely integrable.  This is derived from the
existing adelic integrability by slicing at one archimedean point where the archimedean
amplitude is nonzero; no new estimate is introduced. -/
theorem integrable_finiteGaussIntegral (L : PositiveDefiniteIntegralLattice n) {scale : ℝ}
    (hscale : 0 < scale) (hrank : 5 ≤ n) :
    Integrable (fun y : RationalFiniteAdele =>
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y)
      rationalFiniteAdeleAddHaarMeasure := by
  have hre : 0 < ((scale : ℝ) : ℂ).re := by simpa using hscale
  have hB := L.integrable_rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice
    hscale hrank
  rw [rationalAdeleAddHaarMeasure_eq_prod] at hB
  obtain ⟨w₀, hw₀⟩ := hB.prod_right_ae.exists
  set r : ℝ := rationalInfiniteAdeleContinuousAddEquivReal w₀ with hr
  have hz : ((scale : ℂ) - (r : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hzero : ((scale : ℂ) - (r : ℂ) * Complex.I).re = 0 := by rw [h]; simp
    simp at hzero
    exact hscale.ne' hzero
  have hamp : ((L.polarRealDeterminantScale : ℂ)⁻¹ *
      (1 / ((scale : ℂ) - (r : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n) ≠ 0 := by
    have hcpow : (((scale : ℂ) - (r : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      rintro ⟨h, -⟩
      exact hz h
    have hdet : ((L.polarRealDeterminantScale : ℝ) : ℂ)⁻¹ ≠ 0 := by
      refine inv_ne_zero ?_
      exact_mod_cast (ne_of_gt L.polarRealDeterminantScale_pos)
    exact mul_ne_zero hdet (pow_ne_zero _ (by simpa using hcpow))
  have hpoint : ∀ y : RationalFiniteAdele,
      L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L ((scale : ℝ) : ℂ)) (w₀, y) =
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((scale : ℂ) - (r : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y :=
    fun y =>
      RationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finiteAt
        L hre (w₀, y)
  have hmul := hw₀.const_mul (((L.polarRealDeterminantScale : ℂ)⁻¹ *
      (1 / ((scale : ℂ) - (r : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)⁻¹)
  refine hmul.congr (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [hpoint y, ← mul_assoc, inv_mul_cancel₀ hamp, one_mul]

/-- The finite local integrand is integrable at every rational frequency: the character
has modulus one. -/
theorem integrable_finiteLocalIntegrand (L : PositiveDefiniteIntegralLattice n) {scale : ℝ}
    (hscale : 0 < scale) (hrank : 5 ≤ n) (b : ℚ) :
    Integrable (fun y : RationalFiniteAdele =>
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y)
      rationalFiniteAdeleAddHaarMeasure := by
  refine (L.integrable_finiteGaussIntegral hscale hrank).bdd_mul (c := 1) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_induced_dom.comp
      (continuous_rationalFiniteAdeleFourierChar.comp (by fun_prop))
  · filter_upwards with y
    exact le_of_eq (Circle.norm_coe _)

/-- One frequency-free bound for the finite local integral. -/
theorem norm_integral_finiteLocal_le (L : PositiveDefiniteIntegralLattice n) (b : ℚ) :
    ‖∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
        ∂rationalFiniteAdeleAddHaarMeasure‖ ≤
      ∫ y : RationalFiniteAdele,
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y‖
        ∂rationalFiniteAdeleAddHaarMeasure := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [norm_mul, Circle.norm_coe, one_mul]

end PositiveDefiniteIntegralLattice
