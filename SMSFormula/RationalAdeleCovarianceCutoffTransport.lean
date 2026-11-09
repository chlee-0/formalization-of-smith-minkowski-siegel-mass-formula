import SMSFormula.RationalAdeleGeometricCovariance
import SMSFormula.RationalCliffordGeneralSpinComplexThetaBound
import SMSFormula.RationalCliffordGeneralSpinComplexCutoffIntegral

/-!
# Transport of the geometric covariance to the cutoff-normalized functional

The geometric covariance is a kernel identity: at every concrete full-adelic special orthogonal
point the rational-diagonal theta of the standard test equals that of its polar Weyl transform.
A kernel identity is not a functional identity, so it has to be pushed through the existing
descent to the left quotient and the existing complex cutoff integral.

The transport is done here in three steps, all of them restatements of the already closed
covariance along already closed identifications:

* at the matrix special orthogonal group, through the existing equivalence with the concrete
  group;
* at the `GSpin` group, through the existing rational-vector action, which is literally the
  matrix group acting at `g.matrixGroup⁻¹`;
* on the left quotient and under the cutoff-weighted quotient measure, where the two integrands
  are pointwise equal, so the difference is the zero function and the integrals agree with no
  further integrability input.

Together with the existing agreement between the complex cutoff integral and the nonnegative one
at the standard test, this identifies the complex cutoff integral of the Weyl transform with the
real value of the existing nonnegative cutoff integral of the standard test.

Negative scope: no new Haar, cutoff, subgroup, chart, section or decomposition is introduced, and
nothing is rescaled.  The four names stay distinct: nothing here compares with the Eisenstein
side, supplies the shell agreement, or evaluates a Tamagawa number, and no separation identity
is drawn -- the origin separation alone does not yield `t_V` without the shell agreement.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators ENNReal FourierTransform

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The covariance at the matrix special orthogonal group, through the existing equivalence with
the concrete group. -/
theorem tsum_polarGaussianLatticeTest_weyl_covariance_matrixGroup
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (k : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    (∑' q : Fin n → ℚ, rationalAdeleVectorPolarGaussianLatticeTest L b
        (k.1.1.1.mulVec (rationalAdeleVectorDiagonal n q))) =
      ∑' y : Fin n → ℚ,
        L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L b)
          (k.1.1.1.mulVec (rationalAdeleVectorDiagonal n y)) := by
  have hmat : (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv k).1.1.1 =
      k.1.1.1 := L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_apply_matrix k
  have hcov := tsum_polarGaussianLatticeTest_weyl_covariance L hb
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv k)
  rwa [hmat] at hcov

/-- The covariance of the complex theta at every actual full-adelic `GSpin` point: the complex
theta of the standard test equals that of its polar Weyl transform.  The `GSpin` rational-vector
action is the matrix special orthogonal action at `g.matrixGroup⁻¹`, so this is the previous
statement at that point. -/
theorem fullAdelicCliffordGeneralSpinComplexTheta_polarGaussianLatticeTest_weyl_covariance
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexTheta
        (rationalAdeleVectorPolarGaussianLatticeTest L b) g =
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexTheta
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L b)) g :=
  tsum_polarGaussianLatticeTest_weyl_covariance_matrixGroup L hb (g.matrixGroup⁻¹)

/-- The transport: the complex cutoff integral of the standard test equals that of its polar
Weyl transform.  The two descended integrands are pointwise equal on the left quotient, so their
difference is the zero function and no further integrability input is needed. -/
theorem complexCutoffIntegral_polarGaussianLatticeTest_weyl_covariance
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (f : ℝ → ℝ≥0∞) :
    L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
        (rationalAdeleVectorPolarGaussianLatticeTest L b) f =
      L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L b)) f := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z ↦ ?_)
  induction Z using Quot.ind with
  | _ g =>
    exact fullAdelicCliffordGeneralSpinComplexTheta_polarGaussianLatticeTest_weyl_covariance L hb g

/-- Non-vacuous: at a real width the complex cutoff integral of the polar Weyl transform of the
standard test is the real value of the existing nonnegative cutoff integral of the standard
test itself.  This is the covariance combined with the existing agreement between the complex
cutoff integral and the nonnegative one. -/
theorem complexCutoffIntegral_weyl_polarGaussianLatticeTest_eq_standard
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))) f =
      (((L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) f).toReal : ℝ) : ℂ) := by
  have hb : 0 < ((a : ℂ)).re := by simpa using ha
  rw [← complexCutoffIntegral_polarGaussianLatticeTest_weyl_covariance L hb f]
  exact L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral_standard hn ha f hf

end PositiveDefiniteIntegralLattice

end
