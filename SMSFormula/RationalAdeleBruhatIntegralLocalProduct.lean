import SMSFormula.RationalAdeleAdditiveQuotientCharacter
import SMSFormula.RationalCliffordGeneralSpinAllRationalShellTonelli
import SMSFormula.RationalAdeleThetaEisensteinDifferenceDecay
import SMSFormula.RationalAdelePolarGaussianScaledLatticeSummability
import SMSFormula.RationalAdeleAdditiveQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain
import SMSFormula.RationalAdeleRankOneAdelicBruhatIntegrable
import SMSFormula.RationalAdeleRankOneAdelicBruhatFactorization

/-!
# The adelic Bruhat integral is a literal product of its two local integrals

The frequency-by-frequency difference is closed, and its cusp term is the integral of the
existing adelic Bruhat coefficient against the global character.  This file derives --
it does not assume -- the local product decomposition of that integral.

Three existing facts combine.  The global character splits as its archimedean factor
times its finite factor; the existing adelic Bruhat coefficient of the standard test
is an explicit real factor depending only on the archimedean component times the existing
finite Gauss integral depending only on the finite component; and the existing adelic Haar
is the product of the fixed infinite and finite Haars.  Hence

```text
int_A psi_t(u) B_A(Phi,u) du = (int_{A_inf} psi_t^inf * realFactor) * (int_{A_fin} psi_t^fin * G).
```

Negative scope: this is a factorization, not an evaluation.  Neither local integral is
computed or bounded here, no Euler product over the finite places is asserted, and nothing
about vanishing of the difference follows.  The factorization uses the existing adelic Haar
normalization and introduces no new measure, section or chart.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The rational-frequency global character is the literal product of its archimedean
and finite factors. -/
theorem rationalAdeleScaledFourierChar_eq_real_mul_finite (t : ℚ) (u : RationalAdele) :
    ((rationalAdeleScaledFourierChar t u : Circle) : ℂ) =
      ((rationalInfiniteAdeleFourierChar
          (algebraMap ℚ RationalInfiniteAdele t * u.1) : Circle) : ℂ) *
        ((rationalFiniteAdeleFourierChar
          (algebraMap ℚ RationalFiniteAdele t * u.2) : Circle) : ℂ) := by
  have hfst : (algebraMap ℚ RationalAdele t * u).1 =
      algebraMap ℚ RationalInfiniteAdele t * u.1 := by
    have h : (algebraMap ℚ RationalAdele t).1 = algebraMap ℚ RationalInfiniteAdele t :=
      DFunLike.congr_fun
        (RingHom.ext_rat
          ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
            (algebraMap ℚ RationalAdele))
          (algebraMap ℚ RationalInfiniteAdele)) t
    rw [← h]
    rfl
  have hsnd : (algebraMap ℚ RationalAdele t * u).2 =
      algebraMap ℚ RationalFiniteAdele t * u.2 := by
    have h : (algebraMap ℚ RationalAdele t).2 = algebraMap ℚ RationalFiniteAdele t :=
      DFunLike.congr_fun
        (RingHom.ext_rat
          ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp
            (algebraMap ℚ RationalAdele))
          (algebraMap ℚ RationalFiniteAdele)) t
    rw [← h]
    rfl
  rw [rationalAdeleScaledFourierChar_apply, rationalAdeleFourierChar_apply,
    rationalAdeleArchimedeanFourierChar_apply, hfst, hsnd, Circle.coe_mul]
  rfl

set_option maxHeartbeats 1000000 in
/-- The existing adelic Bruhat integral against the global character is the literal
product of its archimedean and finite local integrals. -/
theorem integral_scaledChar_mul_adelicBruhat_eq_real_mul_finite
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (t : ℚ) :
    (∫ u, (rationalAdeleScaledFourierChar t u : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
            (rationalAdeleVectorPolarGaussianLatticeTest L b) u
        ∂rationalAdeleAddHaarMeasure) =
      (∫ w : RationalInfiniteAdele,
          ((rationalInfiniteAdeleFourierChar
              (algebraMap ℚ RationalInfiniteAdele t * w) : Circle) : ℂ) *
            ((L.polarRealDeterminantScale : ℂ)⁻¹ *
              (1 / (b - ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
                Complex.I) ^ (1 / 2 : ℂ)) ^ n)
          ∂rationalInfiniteAdeleAddHaarMeasure) *
        (∫ y : RationalFiniteAdele,
          ((rationalFiniteAdeleFourierChar
              (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
            L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
          ∂rationalFiniteAdeleAddHaarMeasure) := by
  have hpoint : ∀ u : RationalAdele,
      (rationalAdeleScaledFourierChar t u : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
            (rationalAdeleVectorPolarGaussianLatticeTest L b) u =
        (((rationalInfiniteAdeleFourierChar
            (algebraMap ℚ RationalInfiniteAdele t * u.1) : Circle) : ℂ) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / (b - ((rationalInfiniteAdeleContinuousAddEquivReal u.1 : ℝ) : ℂ) *
              Complex.I) ^ (1 / 2 : ℂ)) ^ n)) *
          (((rationalFiniteAdeleFourierChar
              (algebraMap ℚ RationalFiniteAdele t * u.2) : Circle) : ℂ) *
            L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt u.2) := by
    intro u
    rw [rationalAdeleScaledFourierChar_eq_real_mul_finite t u,
      rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finiteAt
        L hb u]
    simp only [rationalAdeleRealScalar]
    ring
  rw [rationalAdeleAddHaarMeasure_eq_prod,
    integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact integral_prod_mul
    (fun w : RationalInfiniteAdele =>
      ((rationalInfiniteAdeleFourierChar
          (algebraMap ℚ RationalInfiniteAdele t * w) : Circle) : ℂ) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / (b - ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
            Complex.I) ^ (1 / 2 : ℂ)) ^ n))
    (fun y : RationalFiniteAdele =>
      ((rationalFiniteAdeleFourierChar
          (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y)

end PositiveDefiniteIntegralLattice
