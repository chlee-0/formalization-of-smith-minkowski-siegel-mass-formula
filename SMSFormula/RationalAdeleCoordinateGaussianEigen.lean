import SMSFormula.RationalAdeleCoordinateElementaryFourier

/-!
# The coordinate Gaussian--lattice test is a Fourier eigenfunction at width one

The overlap argument for adelic Haar invariance needs one test `phi` with `phi^ = kappa phi`,
`kappa > 0`, for the base coordinate
adelic Fourier transform.  The repository already computes that transform on the elementary
adelic Gaussian times the integral indicator, and at width one the computed value is the test
itself: the amplitude `1 / b^(1/2)` is one and the exponent `-pi / b` equals `-pi * b`.  So
`kappa = 1`, and no new normalization, character or Haar is introduced.

The scalar identity tensorizes coordinatewise through the existing finite-Fubini identification
of the coordinate Fourier integral with the product of the scalar ones.

Negative scope: an eigen identity for one test at one width.  No Fourier inversion, no Plancherel,
no overlap integral and no Haar-scalar statement follows.  In particular the polar
Gaussian--lattice test is not an eigenfunction: its transform swaps the carrier to the polar dual
and carries the determinant scale.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

/-- At width one the elementary adelic Gaussian--indicator test is its own Fourier integral. -/
theorem rationalAdele_fourierIntegral_gaussianIntegralTest_one (w : RationalAdele) :
    Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
        (rationalAdeleGaussianIntegralTest 1) w =
      rationalAdeleGaussianIntegralTest 1 w := by
  have hb : (0 : ℝ) < (1 : ℂ).re := by simp
  rw [rationalAdele_fourierIntegral_gaussianIntegralTest hb w,
    rationalAdeleGaussianIntegralTest, rationalInfiniteAdeleGaussian]
  congr 1
  rw [Complex.one_cpow]
  norm_num

/-- Hence the coordinate tensor of the scalar Fourier integrals is the coordinate test itself. -/
theorem rationalAdeleCoordinateGaussianFourierProductTest_one (d : ℕ) :
    rationalAdeleCoordinateGaussianFourierProductTest d 1 =
      rationalAdeleCoordinateGaussianIntegralTest d 1 := by
  funext x
  rw [rationalAdeleCoordinateGaussianFourierProductTest,
    rationalAdeleCoordinateGaussianIntegralTest]
  exact Finset.prod_congr rfl fun i _ ↦
    rationalAdele_fourierIntegral_gaussianIntegralTest_one (x i)

/-- The eigen identity, with `kappa = 1`: the coordinate Gaussian--lattice test at width one is
its own Fourier integral for the existing coordinate character and coordinate Haar. -/
theorem rationalAdeleCoordinate_fourierIntegral_gaussianIntegralTest_one (d : ℕ) :
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar d)
        (rationalAdeleCoordinateAddHaarMeasure d)
        (rationalAdeleCoordinateGaussianIntegralTest d 1) =
      rationalAdeleCoordinateGaussianIntegralTest d 1 := by
  funext w
  rw [rationalAdeleCoordinate_fourierIntegral_gaussianIntegralTest,
    rationalAdeleCoordinateGaussianFourierProductTest_one]

end PositiveDefiniteIntegralLattice

end
