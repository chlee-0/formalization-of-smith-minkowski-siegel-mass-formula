import SMSFormula.RationalAdeleWeylTransformThetaFiniteness
import SMSFormula.RationalCliffordGeneralSpinCutoffNormalizedStandardTest
import SMSFormula.RationalAdeleRankOneBruhatFactorization

/-!
# The standard test and its Weyl transform are not self-dual at the origin

The separation step needs an admissible pair whose origin values differ: a self-dual test gives
nothing, because the expansion identity it produces is vacuous.  The candidate pair is the
standard polar Gaussian--lattice test and its Weyl transform, both of which now have finite
cutoff-normalized functionals.

The standard test is one at the origin.  Its Weyl transform is, by the existing zero-frequency
Fourier evaluation and the fact that the origin lies in the polar dual lattice, the reciprocal
determinant scale times one complex square-root factor per coordinate; its modulus is therefore
`detScale^-1 * (a^(1/2))^-n`.  Since that is `detScale^-1` at width one and strictly less than
one at width four when `detScale^-1 = 1`, a separating width always exists in rank at least one.

Negative scope: this is a prerequisite for the separation step, not the step.  No covariance is
proved here, neither geometric nor Eisenstein, and no consequence for `tau(Spin)` follows: the
identity `(t_V - 1)(Phi(0) - (W Phi)(0)) = 0` still needs both functionals to agree on the pair.
-/

noncomputable section

open Matrix MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The origin lies in the polar dual lattice, so its dual indicator is one. -/
@[simp]
theorem finitePolarDualLatticeIndicator_zero (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator 0 = 1 := by
  refine RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem _ ?_
  rw [RationalQuadraticSpaceMatrix.mem_finitePolarDualLattice_iff, Matrix.mulVec_zero]
  intro i
  simpa using Subring.zero_mem integralFiniteAdeleSubring

/-- The origin value of the Weyl transform of the standard test. -/
theorem weylStandardTestENNReal_zero (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    L.weylStandardTestENNReal a 0 =
      ENNReal.ofReal (((L.polarRealDeterminantScale : ℝ))⁻¹ * ((a ^ (1 / 2 : ℝ))⁻¹) ^ n) := by
  have hb : 0 < ((a : ℂ)).re := by simpa using ha
  unfold weylStandardTestENNReal
  rw [RationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator_polarGaussianLattice L hb,
    rationalAdeleVectorPolarGaussianLatticeFourierProduct]
  have hreal : rationalAdeleVectorRealPart n (0 : Fin n → RationalAdele) = 0 := by
    funext i
    change rationalInfiniteAdeleContinuousAddEquivReal (0 : RationalInfiniteAdele) = 0
    exact map_zero _
  have hfin : rationalAdeleVectorFinitePart n (0 : Fin n → RationalAdele) = 0 := rfl
  rw [hreal, hfin, L.finitePolarDualLatticeIndicator_zero, mul_one,
    RationalQuadraticSpaceMatrix.polarRealGaussianFourierProduct_zero]
  congr 1
  rw [norm_mul, norm_inv, norm_pow, norm_div, norm_one,
    Complex.norm_cpow_eq_rpow_re_of_pos ha]
  simp [div_eq_mul_inv]

/-- Separation is available: some positive width makes the origin value of the Weyl transform
differ from the origin value of the standard test, so the candidate pair is not self-dual. -/
theorem exists_width_weylStandardTestENNReal_zero_ne_standard
    (L : PositiveDefiniteIntegralLattice n) (hn : 1 ≤ n) :
    ∃ a : ℝ, 0 < a ∧
      L.weylStandardTestENNReal a 0 ≠
        rationalAdeleVectorPolarGaussianLatticeTestENNReal L a 0 := by
  by_cases hone : ((L.polarRealDeterminantScale : ℝ))⁻¹ = 1
  · refine ⟨4, by norm_num, ?_⟩
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [L.weylStandardTestENNReal_zero (by norm_num : (0:ℝ) < 4), h4, hone,
      rationalAdeleVectorPolarGaussianLatticeTestENNReal_zero]
    have hlt : (1 : ℝ) * ((2 : ℝ)⁻¹) ^ n < 1 := by
      rw [one_mul]
      calc ((2 : ℝ)⁻¹) ^ n ≤ ((2 : ℝ)⁻¹) ^ 1 := by
            apply pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
        _ < 1 := by norm_num
    intro hcontra
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp] at hcontra
    have := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by norm_num)).1 hcontra
    exact absurd this (ne_of_lt hlt)
  · refine ⟨1, by norm_num, ?_⟩
    rw [L.weylStandardTestENNReal_zero (by norm_num : (0:ℝ) < 1),
      rationalAdeleVectorPolarGaussianLatticeTestENNReal_zero, Real.one_rpow]
    intro hcontra
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp] at hcontra
    have := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by norm_num)).1 hcontra
    simp only [inv_one, one_pow, mul_one] at this
    exact hone this

end PositiveDefiniteIntegralLattice

end
