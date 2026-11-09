import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductCompositionRelativeDeterminant

/-!
# Scalar cancellation in the identity north-pole product composition

This file cancels the fixed nonzero rational-basis transition scalar from the
absolute relative-determinant identity.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- After cancelling the nonzero fixed transition scalar, the genuine mapped
split determinant is the square-transition determinant times the higher
centered moving determinant. -/
theorem
    abs_det_identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_eq_square_mul_centered
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    |LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
          n p.1
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
            n p.2)).toLinearMap| =
      |LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative
            n p.1).toLinearMap| *
        |LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
            n p).toLinearMap| := by
  have hscalar :
      |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n| ≠ 0 :=
    abs_ne_zero.mpr
      (identitySpecialOrthogonalNorthPoleProductTransitionDetScalar_ne_zero n)
  have hrelative :=
    abs_identitySpecialOrthogonalNorthPoleProduct_transitionDetScalar_mul_mappedSplit_det
      n p
  rw [
    abs_identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar]
    at hrelative
  apply mul_left_cancel₀ hscalar
  calc
    |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n| *
        |LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
            n p.1
            (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
              n p.2)).toLinearMap| =
      (|identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n| *
          |LinearMap.det
            (identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative
              n p.1).toLinearMap|) *
        |LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
            n p).toLinearMap| := hrelative
    _ =
      |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n| *
        (|LinearMap.det
            (identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative
              n p.1).toLinearMap| *
          |LinearMap.det
            (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
              n p).toLinearMap|) := by ring

end PositiveDefiniteIntegralLattice
