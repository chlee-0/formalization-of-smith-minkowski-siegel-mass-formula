import SMSFormula.RationalAdeleCoordinateElementaryPoisson
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Coordinate elementary Fourier integral and Poisson summation

This file identifies the normalized additive Haar measure on
`Fin d → RationalAdele` with the finite product of the fixed scalar
Haar. It defines the product of the exact scalar additive characters and uses
finite Fubini to identify the Fourier integral of the coordinate Gaussian
with the coordinatewise product.

Consequently the discrete tensor identity becomes Poisson summation
for the coordinate Fourier integral. The scale-four test has unequal zero
values in every positive dimension. No orthogonal action, quadratic-shell
decomposition, dual-lattice comparison, or GSpin quotient is used here.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace PositiveDefiniteIntegralLattice

/-- The existing normalized coordinate Haar is literally the finite product
of the fixed scalar rational-adelic Haar measures. -/
theorem rationalAdeleCoordinateAddHaarMeasure_eq_pi (d : ℕ) :
    rationalAdeleCoordinateAddHaarMeasure d =
      Measure.pi (fun _ : Fin d => rationalAdeleAddHaarMeasure) := by
  letI : SigmaFinite
      (Measure.pi (fun _ : Fin d => rationalAdeleAddHaarMeasure)) :=
    Measure.pi.sigmaFinite _
  letI : (Measure.pi
      (fun _ : Fin d => rationalAdeleAddHaarMeasure)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  apply (Measure.addHaarMeasure_eq_iff
    (rationalAdeleCoordinatePositiveCompacts d) _).2
  change Measure.pi (fun _ : Fin d => rationalAdeleAddHaarMeasure)
      (rationalAdeleCoordinateStandardBlock d) = 1
  rw [rationalAdeleCoordinateStandardBlock, Measure.pi_pi]
  simp only [rationalAdeleAddHaarMeasure_standardBlock,
    Finset.prod_const_one]

/-- Product of the exact scalar global additive characters on a finite
coordinate adelic space. -/
noncomputable def rationalAdeleCoordinateFourierChar (d : ℕ) :
    AddChar (Fin d → RationalAdele) Circle where
  toFun x := ∏ i, rationalAdeleFourierChar (x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, AddChar.map_add_eq_mul]
    exact Finset.prod_mul_distrib

@[simp]
theorem rationalAdeleCoordinateFourierChar_apply
    (d : ℕ) (x : Fin d → RationalAdele) :
    rationalAdeleCoordinateFourierChar d x =
      ∏ i, rationalAdeleFourierChar (x i) :=
  rfl

/-- The coordinate additive character is continuous. -/
theorem continuous_rationalAdeleCoordinateFourierChar (d : ℕ) :
    Continuous (rationalAdeleCoordinateFourierChar d) := by
  simpa [rationalAdeleCoordinateFourierChar] using
    (continuous_finset_prod Finset.univ fun i _ =>
      continuous_rationalAdeleFourierChar.comp (continuous_apply i))

/-- The coordinate additive character is literally trivial on every rational
coordinate diagonal. -/
@[simp]
theorem rationalAdeleCoordinateFourierChar_rationalDiagonal
    (d : ℕ) (q : Fin d → ℚ) :
    rationalAdeleCoordinateFourierChar d
      (fun i => algebraMap ℚ RationalAdele (q i)) = 1 := by
  rw [rationalAdeleCoordinateFourierChar_apply]
  simp only [rationalAdeleFourierChar_algebraMap, Finset.prod_const_one]

/-- The coordinate Gaussian is integrable for the existing normalized
coordinate Haar. -/
theorem integrable_rationalAdeleCoordinateGaussianIntegralTest
    {b : ℂ} (hb : 0 < b.re) (d : ℕ) :
    Integrable (rationalAdeleCoordinateGaussianIntegralTest d b)
      (rationalAdeleCoordinateAddHaarMeasure d) := by
  rw [rationalAdeleCoordinateAddHaarMeasure_eq_pi]
  exact Integrable.fintype_prod (ι := Fin d) fun _ =>
    integrable_rationalAdeleGaussianIntegralTest hb

/-- Finite Fubini identifies the actual coordinate Fourier integral with the
product of the certified scalar Fourier integrals. -/
theorem rationalAdeleCoordinate_fourierIntegral_gaussianIntegralTest
    (b : ℂ) (d : ℕ) (w : Fin d → RationalAdele) :
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar d)
        (rationalAdeleCoordinateAddHaarMeasure d)
        (rationalAdeleCoordinateGaussianIntegralTest d b) w =
      rationalAdeleCoordinateGaussianFourierProductTest d b w := by
  rw [Fourier.fourierIntegral_def]
  have hintegrand :
      (fun v : Fin d → RationalAdele =>
        rationalAdeleCoordinateFourierChar d (-(v * w)) •
          rationalAdeleCoordinateGaussianIntegralTest d b v) =
      (fun v : Fin d → RationalAdele =>
        ∏ i, rationalAdeleFourierChar (-(v i * w i)) •
          rationalAdeleGaussianIntegralTest b (v i)) := by
    funext v
    simp only [rationalAdeleCoordinateFourierChar_apply,
      Pi.neg_apply, Pi.mul_apply,
      rationalAdeleCoordinateGaussianIntegralTest,
      Circle.smul_def, smul_eq_mul]
    change Circle.coeHom
        (∏ i, rationalAdeleFourierChar (-(v i * w i))) *
          ∏ i, rationalAdeleGaussianIntegralTest b (v i) = _
    rw [map_prod]
    change (∏ x, (rationalAdeleFourierChar (-(v x * w x)) : ℂ)) *
        ∏ i, rationalAdeleGaussianIntegralTest b (v i) = _
    rw [Finset.prod_mul_distrib]
  rw [hintegrand, rationalAdeleCoordinateAddHaarMeasure_eq_pi]
  calc
    (∫ v : Fin d → RationalAdele,
        ∏ i, rationalAdeleFourierChar (-(v i * w i)) •
          rationalAdeleGaussianIntegralTest b (v i)
        ∂Measure.pi (fun _ : Fin d => rationalAdeleAddHaarMeasure)) =
      ∏ i, ∫ v : RationalAdele,
        rationalAdeleFourierChar (-(v * w i)) •
          rationalAdeleGaussianIntegralTest b v
        ∂rationalAdeleAddHaarMeasure :=
      integral_fintype_prod_eq_prod
        (μ := fun _ : Fin d => rationalAdeleAddHaarMeasure)
        (fun i (v : RationalAdele) =>
          rationalAdeleFourierChar (-(v * w i)) •
            rationalAdeleGaussianIntegralTest b v)
    _ = rationalAdeleCoordinateGaussianFourierProductTest d b w := by
      simp only [← Fourier.fourierIntegral_def,
        rationalAdeleCoordinateGaussianFourierProductTest]

@[simp]
theorem
    rationalAdeleCoordinate_fourierIntegral_separatingGaussianTest_zero
    (d : ℕ) :
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar d)
        (rationalAdeleCoordinateAddHaarMeasure d)
        (rationalAdeleCoordinateSeparatingGaussianTest d) 0 =
      (1 / 2 : ℂ) ^ d := by
  rw [show rationalAdeleCoordinateSeparatingGaussianTest d =
      rationalAdeleCoordinateGaussianIntegralTest d 4 by rfl,
    rationalAdeleCoordinate_fourierIntegral_gaussianIntegralTest]
  exact rationalAdeleCoordinateSeparatingGaussianFourierProductTest_zero d

/-- The coordinate Fourier integral has unequal zero values in
every positive dimension. -/
theorem
    rationalAdeleCoordinateSeparatingGaussianTest_zero_ne_fourierIntegral_zero
    (d : ℕ) :
    rationalAdeleCoordinateSeparatingGaussianTest (d + 1) 0 ≠
      Fourier.fourierIntegral
        (rationalAdeleCoordinateFourierChar (d + 1))
        (rationalAdeleCoordinateAddHaarMeasure (d + 1))
        (rationalAdeleCoordinateSeparatingGaussianTest (d + 1)) 0 := by
  rw [rationalAdeleCoordinateSeparatingGaussianTest_zero,
    rationalAdeleCoordinate_fourierIntegral_separatingGaussianTest_zero]
  intro h
  have hnorm := congrArg norm h
  have hnorm' : (1 : ℝ) = (1 / 2 : ℝ) ^ (d + 1) := by
    simpa [norm_pow] using hnorm
  have hnonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  have hlt := pow_lt_one₀ hnonneg hhalf (Nat.succ_ne_zero d)
  exact (ne_of_lt hlt) hnorm'.symm

end PositiveDefiniteIntegralLattice
