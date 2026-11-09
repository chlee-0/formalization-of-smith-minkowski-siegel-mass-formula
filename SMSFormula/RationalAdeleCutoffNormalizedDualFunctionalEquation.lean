import SMSFormula.RationalAdeleCovarianceCutoffNormalized
import SMSFormula.RationalAdeleWeylTransformOriginSeparation

/-!
# A functional equation for `I_V` between the standard and the dual-carrier test

`I_V(Phi) = I_V(W Phi)` still names the polar Weyl transform, which is not one of the repository's
concrete tests.  The existing identification removes it: at a real positive width the Weyl
transform of the standard test is an explicit nonnegative constant times the dual-carrier test at
the reciprocal width.  Since the cutoff-normalized functional is homogeneous, the covariance
becomes a functional equation between two concrete tests,

`I_V(Phi_a) = detScale^-1 * (a^(1/2))^-n * I_V(dual_(1/a))`,

with the constant written out.  Both tests are the repository's own, both raw cutoff integrals are
finite, and no transform appears in the statement.

Negative scope: this is a restatement of the covariance, not a new analytic input.  The constant is
not one -- it depends on the discriminant through `detScale` and on the width through `a^(-n/2)` --
so the equation is not a symmetry and gives no self-duality.  Nothing here compares with the
Eisenstein side, supplies the shell agreement, or evaluates a Tamagawa number, and no value of
`t_V` is claimed.
-/

noncomputable section

open Matrix MeasureTheory RationalQuadraticSpaceMatrix
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The existing nonnegative dual-carrier test is measurable. -/
theorem measurable_rationalAdeleVectorPolarGaussianDualTestENNReal
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) :
    Measurable (rationalAdeleVectorPolarGaussianDualTestENNReal L a) := by
  unfold rationalAdeleVectorPolarGaussianDualTestENNReal
  exact ((L.measurable_rationalAdeleVectorPolarGaussianDualTest (a : ℂ)).norm).ennreal_ofReal

/-- The existing constant of the identification, in its real nonnegative form. -/
theorem weylStandardTestENNReal_eq_const_mul_dual
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (y : Fin n → RationalAdele) :
    L.weylStandardTestENNReal a y =
      ENNReal.ofReal ((L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ n) *
        rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹ y := by
  rw [L.weylStandardTestENNReal_eq ha, L.polarRealDeterminantScale_halfPower_ofReal ha,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (L.polarRealDeterminantScale_halfPower_nonneg ha)]

/-- Homogeneity of the cutoff-normalized functional. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_const_mul
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (c : ℝ≥0∞) (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞) (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hP hconv
        (fun y ↦ c * Phi y) f =
      c * L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hP hconv Phi f := by
  unfold cutoffNormalizedFullAdelicCliffordGeneralSpinTheta
  dsimp only
  rw [L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_const_mul c Phi hPhi f,
    div_eq_mul_inv, div_eq_mul_inv, mul_left_comm, mul_assoc]

/-- The dual-carrier test is one at the origin, exactly as the standard test is: the origin lies
in the polar dual lattice and the Gaussian is one there. -/
@[simp]
theorem rationalAdeleVectorPolarGaussianDualTest_zero (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    rationalAdeleVectorPolarGaussianDualTest L b 0 = 1 := by
  have hreal : rationalAdeleVectorRealPart n (0 : Fin n → RationalAdele) = 0 := by
    funext i
    change rationalInfiniteAdeleContinuousAddEquivReal (0 : RationalInfiniteAdele) = 0
    exact map_zero _
  have hfin : rationalAdeleVectorFinitePart n (0 : Fin n → RationalAdele) = 0 := rfl
  show polarRealGaussian L b (rationalAdeleVectorRealPart n 0) *
      L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator
        (rationalAdeleVectorFinitePart n 0) = 1
  rw [hreal, hfin, L.finitePolarDualLatticeIndicator_zero, polarRealGaussian]
  simp [realCoordinateGaussian]

/-- Its nonnegative version is one at the origin too. -/
@[simp]
theorem rationalAdeleVectorPolarGaussianDualTestENNReal_zero
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) :
    rationalAdeleVectorPolarGaussianDualTestENNReal L a 0 = 1 := by
  rw [rationalAdeleVectorPolarGaussianDualTestENNReal,
    L.rationalAdeleVectorPolarGaussianDualTest_zero ((a : ℝ) : ℂ)]
  simp

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The cutoff-normalized functional at the Weyl transform, written through the dual-carrier test
at the reciprocal width with the explicit constant. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_weylStandard_eq_const_mul_dual
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hP hconv
        (L.weylStandardTestENNReal a) rationalIdeleClassUnitLogCutoff =
      ENNReal.ofReal
          ((L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2)) *
        L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hP hconv
          (rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹)
          rationalIdeleClassUnitLogCutoff := by
  have hpt : L.weylStandardTestENNReal a =
      fun y ↦ ENNReal.ofReal
            ((L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2)) *
          rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹ y := by
    funext y
    exact L.weylStandardTestENNReal_eq_const_mul_dual ha y
  rw [hpt]
  exact L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_const_mul hr inst hP hconv _ _
    (L.measurable_rationalAdeleVectorPolarGaussianDualTestENNReal a⁻¹) _

/-- The functional equation, between two concrete tests and with the constant written out: the
cutoff-normalized functional at the standard test of width `a` is the explicit constant
`detScale^-1 * (a^(1/2))^-n` times its value at the dual-carrier test of the reciprocal width. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_standard_eq_const_mul_dual
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hP hconv
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
        rationalIdeleClassUnitLogCutoff =
      ENNReal.ofReal
          ((L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2)) *
        L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hP hconv
          (rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹)
          rationalIdeleClassUnitLogCutoff := by
  rw [← L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_weylStandard_eq_standard
      hr inst hP hconv ha]
  exact L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_weylStandard_eq_const_mul_dual
    hr inst hP hconv ha

/-- The expansion at the dual-carrier test: its zero-orbit coefficient is the intrinsic Spin
quantity alone, because it too is one at the origin. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_dual_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (a : ℝ) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hP hconv
        (rationalAdeleVectorPolarGaussianDualTestENNReal L a)
        rationalIdeleClassUnitLogCutoff =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal +
        ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
            hr inst hP hconv b
            (rationalAdeleVectorPolarGaussianDualTestENNReal L a)
            rationalIdeleClassUnitLogCutoff := by
  rw [L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_eq_spinVolume_add_representedNorm
    hr inst hP hconv _
    (L.measurable_rationalAdeleVectorPolarGaussianDualTestENNReal a)
    _ measurable_rationalIdeleClassUnitLogCutoff
    rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
    rationalIdeleClassLogCutoffLIntegral_unit_ne_top,
    L.rationalAdeleVectorPolarGaussianDualTestENNReal_zero a, mul_one]

/-- The functional equation, expanded.  Both tests are one at the origin, so the zero-orbit
coefficient is the intrinsic Spin quantity on both sides and the equation reads

`t_V + sum_b R_b(Phi_a) = C(a) * (t_V + sum_b R_b(dual_(1/a)))`.

This is the precise form in which the shell agreement is still missing: the constant is not one,
so the two shell sums cannot simply cancel, and no value of `t_V` follows from this alone. -/
theorem spinTamagawaNumberENNReal_add_representedNorm_standard_eq_const_mul_dual
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal +
        ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
            hr inst hP hconv b
            (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
            rationalIdeleClassUnitLogCutoff =
      ENNReal.ofReal
          ((L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2)) *
        ((cliffordSpinCandidateRawOnoTamagawaDataOfLattice
            L (by omega) inst hP hconv).spinTamagawaNumberENNReal +
          ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
            L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
              hr inst hP hconv b
              (rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹)
              rationalIdeleClassUnitLogCutoff) := by
  rw [← L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_standard_eq hr inst hP hconv a,
    ← L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_dual_eq hr inst hP hconv a⁻¹]
  exact L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_standard_eq_const_mul_dual
    hr inst hP hconv ha

end PositiveDefiniteIntegralLattice

end
