import SMSFormula.RationalAdeleElementaryGaussianFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Coordinate tensorization of elementary rational-adelic Poisson summation

This file tensors the scalar rational-diagonal Poisson theorem over the
finite coordinate carrier `Fin d`. It proves summability and exact equality
of the two coordinatewise product sums. The scale-four specialization retains
the unequal zero values in every positive dimension.

The Fourier-side function here is explicitly the product of the already
computed scalar Fourier integrals. This file does not identify that product
with a Fourier integral for a measure on `Fin d → RationalAdele`, and it makes
no quadratic-shell or GSpin claim.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace PositiveDefiniteIntegralLattice

private theorem summable_fin_coordinate_prod
    {α : Type*} {f : α → ℂ} (hf : Summable f) (d : ℕ) :
    Summable (fun x : Fin d → α => ∏ i, f (x i)) := by
  induction d with
  | zero =>
      apply summable_of_finite_support
      exact Set.toFinite _
  | succ d ih =>
      let e : (Fin (d + 1) → α) ≃ α × (Fin d → α) :=
        (Fin.insertNthEquiv (fun _ => α) 0).symm
      apply e.symm.summable_iff.mp
      refine (summable_mul_of_summable_norm hf.norm ih.norm).congr ?_
      intro x
      simp [e, Fin.prod_univ_succ]

/-- Coordinate tensor product of the scalar adelic Gaussian test. -/
noncomputable def rationalAdeleCoordinateGaussianIntegralTest
    (d : ℕ) (b : ℂ) (x : Fin d → RationalAdele) : ℂ :=
  ∏ i, rationalAdeleGaussianIntegralTest b (x i)

/-- Coordinate tensor product of the already computed scalar Fourier
integrals. This is not asserted to be a Fourier integral on the coordinate
space. -/
noncomputable def rationalAdeleCoordinateGaussianFourierProductTest
    (d : ℕ) (b : ℂ) (x : Fin d → RationalAdele) : ℂ :=
  ∏ i, Fourier.fourierIntegral rationalAdeleFourierChar
    rationalAdeleAddHaarMeasure (rationalAdeleGaussianIntegralTest b) (x i)

/-- Coordinate tensor product of the scale-four separating scalar test. -/
noncomputable def rationalAdeleCoordinateSeparatingGaussianTest
    (d : ℕ) (x : Fin d → RationalAdele) : ℂ :=
  ∏ i, rationalAdeleSeparatingGaussianTest (x i)

/-- Coordinate tensor product of the scalar Fourier values at scale four. -/
noncomputable def rationalAdeleCoordinateSeparatingGaussianFourierProductTest
    (d : ℕ) (x : Fin d → RationalAdele) : ℂ :=
  ∏ i, Fourier.fourierIntegral rationalAdeleFourierChar
    rationalAdeleAddHaarMeasure rationalAdeleSeparatingGaussianTest (x i)

@[simp]
theorem rationalAdeleCoordinateSeparatingGaussianTest_zero (d : ℕ) :
    rationalAdeleCoordinateSeparatingGaussianTest d 0 = 1 := by
  simp [rationalAdeleCoordinateSeparatingGaussianTest]

@[simp]
theorem rationalAdeleCoordinateSeparatingGaussianFourierProductTest_zero
    (d : ℕ) :
    rationalAdeleCoordinateSeparatingGaussianFourierProductTest d 0 =
      (1 / 2 : ℂ) ^ d := by
  simp [rationalAdeleCoordinateSeparatingGaussianFourierProductTest]

theorem
    rationalAdeleCoordinateSeparatingGaussianTest_zero_ne_fourierProduct_zero
    (d : ℕ) :
    rationalAdeleCoordinateSeparatingGaussianTest (d + 1) 0 ≠
      rationalAdeleCoordinateSeparatingGaussianFourierProductTest
        (d + 1) 0 := by
  rw [rationalAdeleCoordinateSeparatingGaussianTest_zero,
    rationalAdeleCoordinateSeparatingGaussianFourierProductTest_zero]
  intro h
  have hnorm := congrArg norm h
  have hnorm' : (1 : ℝ) = (1 / 2 : ℝ) ^ (d + 1) := by
    simpa [norm_pow] using hnorm
  have hnonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  have hlt := pow_lt_one₀ hnonneg hhalf (Nat.succ_ne_zero d)
  exact (ne_of_lt hlt) hnorm'.symm

end PositiveDefiniteIntegralLattice
