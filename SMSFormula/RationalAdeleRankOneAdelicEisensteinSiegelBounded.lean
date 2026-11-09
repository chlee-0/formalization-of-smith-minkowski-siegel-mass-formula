import SMSFormula.RationalAdeleRankOneAdelicBruhatSummability
import SMSFormula.RationalAdeleRankOneEisensteinSiegelFunctional
import SMSFormula.RationalAdeleAdditiveQuotient

/-!
# A uniform bound for the adelic rank-one cusp functional

Every additive adelic quotient class has a representative in the fixed
standard block.  On that block the finite component is integral, so the
generalized finite Gauss integral is literally the old rational one.  The
real component lies in `[0,1]`, and hence the translated archimedean factor
has one uniform loss.  The already summable rational-height kernel therefore
majorizes the entire Bruhat family uniformly on the standard block.

Summing this pointwise bound and using the surjectivity of the standard block
onto `RationalAdele / ℚ` proves boundedness of the descended cusp functional.
The final descent is existential and chooses no quotient representative.  No
continuity, compactness argument, shell scaling, theta comparison, or
coefficient identity is asserted.
-/

noncomputable section

open Matrix MeasureTheory RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The literal uniform majorant constant for the adelic Bruhat family on the
standard additive block. -/
noncomputable def rationalAdeleRankOneAdelicBruhatStandardBlockConstant
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) : ℝ :=
  Real.sqrt (1 + 1 / a) ^ n *
    ((L.polarRealDeterminantScale : ℝ)⁻¹ *
      Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ n *
      (Real.sqrt (min a 1))⁻¹ ^ n)

/-- On the standard additive block, every adelic Bruhat translate is
uniformly dominated by the old rational-height kernel. -/
theorem norm_rationalAdeleRankOneAdelicBruhatCoefficient_add_diagonal_le_height_of_mem_standardBlock
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (u : RationalAdele) (hu : u ∈ rationalAdeleStandardBlock) (t : ℚ) :
    ‖L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))
        (u + algebraMap ℚ RationalAdele t)‖ ≤
      L.rationalAdeleRankOneAdelicBruhatStandardBlockConstant a *
        (Real.sqrt (rationalRankOneBruhatHeight t))⁻¹ ^ n := by
  rw [rationalAdeleStandardBlock_eq] at hu
  rcases hu with ⟨huReal, huFinite⟩
  rw [rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finiteAt
    L (by simpa using ha)]
  rw [norm_mul, norm_polarRealGaussian_explicit_real_bruhat_factor]
  have hfinite :
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt
          (u + algebraMap ℚ RationalAdele t).2 =
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
          t := by
    change
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt
          (u.2 + algebraMap ℚ RationalFiniteAdele t) = _
    rw [add_comm]
    exact
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt_add_integral
        L (algebraMap ℚ RationalFiniteAdele t) u.2 huFinite
  rw [hfinite]
  let delta : ℝ := rationalAdeleRealScalar u
  have hdelta : |delta| ≤ 1 := by
    change |rationalInfiniteAdeleContinuousAddEquivReal u.1| ≤ 1
    change rationalInfiniteAdeleContinuousAddEquivReal u.1 ∈ Set.Icc (0 : ℝ) 1 at huReal
    rw [abs_of_nonneg huReal.1]
    exact huReal.2
  have hreal : rationalAdeleRealScalar
      (u + algebraMap ℚ RationalAdele t) = (t : ℝ) + delta := by
    rw [rationalAdeleRealScalar_add_rationalDiagonal]
    dsimp [delta]
    ring
  rw [hreal]
  have hshift := inv_sqrt_norm_translated_bruhat_parameter_le
    (delta := delta) ha t
  norm_cast at hshift
  have hconstant : Real.sqrt (1 + |delta| / a) ≤
      Real.sqrt (1 + 1 / a) := by
    apply Real.sqrt_le_sqrt
    gcongr
  have hrealBound :
      (Real.sqrt ‖(a : ℂ) - (((t : ℝ) + delta : ℝ) : ℂ) * Complex.I‖)⁻¹ ≤
        Real.sqrt (1 + 1 / a) *
          (Real.sqrt ‖(a : ℂ) - (t : ℂ) * Complex.I‖)⁻¹ := by
    norm_cast
    exact hshift.trans (mul_le_mul_of_nonneg_right hconstant (by positivity))
  calc
    (L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt ‖(a : ℂ) - (((t : ℝ) + delta : ℝ) : ℂ) * Complex.I‖)⁻¹ ^ n *
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t‖ ≤
      (L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt (1 + 1 / a) *
            (Real.sqrt ‖(a : ℂ) - (t : ℂ) * Complex.I‖)⁻¹) ^ n *
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t‖ := by
          gcongr
    _ = Real.sqrt (1 + 1 / a) ^ n *
        ‖L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) t‖ := by
          rw [rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finite
            L (by simpa using ha)]
          rw [norm_mul, norm_polarRealGaussian_explicit_bruhat_factor]
          ring
    _ ≤ L.rationalAdeleRankOneAdelicBruhatStandardBlockConstant a *
        (Real.sqrt (rationalRankOneBruhatHeight t))⁻¹ ^ n := by
      unfold rationalAdeleRankOneAdelicBruhatStandardBlockConstant
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (L.norm_rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_le_height
          ha t) (by positivity)

/-- A single explicit real bound for the entire descended cusp functional. -/
noncomputable def rationalAdeleRankOneEisensteinSiegelAdditiveQuotientBound
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) : ℝ :=
  ‖rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) 0‖ +
    L.rationalAdeleRankOneAdelicBruhatStandardBlockConstant a *
      ∑' t : ℚ, (Real.sqrt (rationalRankOneBruhatHeight t))⁻¹ ^ n

end PositiveDefiniteIntegralLattice

end
