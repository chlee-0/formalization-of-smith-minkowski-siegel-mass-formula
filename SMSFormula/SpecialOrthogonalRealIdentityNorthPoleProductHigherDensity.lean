import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductLowerDensity

/-!
# Higher density along the identity north-pole product transition

This file packages the higher identity-chart transition to the chart centered
at the group point represented by an exact product-source coordinate.  Its
derivative determinant is exactly the higher target density pulled back along
the product transition.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- At an exact product-source point, the derivative in the second variable
of the higher joint transition from the identity chart to the chart centered
at the represented group point. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalMappedTangent (n + 1) →L[ℝ]
      identitySpecialOrthogonalMappedTangent (n + 1) :=
  (fderiv ℝ
      (specialFormPreservingSmoothRealJointTransitionCoordinate
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero)
      (identitySpecialOrthogonalNorthPoleProductTransition n p.1,
        identitySpecialOrthogonalNorthPoleProductTransition n p.1)).comp
    (specialFormPreservingSmoothRealSecondFactorInclusion
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))

/-- The absolute determinant of the higher centered moving derivative is the
real-valued higher chart density along the product transition. -/
theorem
    abs_det_identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative_eq_targetDensity
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    |LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
          n p).toLinearMap| =
      specialFormPreservingSmoothRealChartCoordinateDensity
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero 1
        (identitySpecialOrthogonalNorthPoleProductHigherCoordinate n
          (identitySpecialOrthogonalNorthPoleProductTransitionOnSource
            n p)) := by
  rw [
    specialFormPreservingSmoothRealChartCoordinateDensity_eq_diagonalPartialJacobian]
  rfl

/-- `ENNReal` form: the higher centered moving determinant is exactly the
pulled-back target density used by the intrinsic cocycle. -/
theorem
    ofReal_abs_det_identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative_eq_targetDensityAlongTransition
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    ENNReal.ofReal
        |LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
            n p).toLinearMap| =
      identitySpecialOrthogonalNorthPoleProductTargetDensityAlongTransition
        n p := by
  rw [
    identitySpecialOrthogonalNorthPoleProductTargetDensityAlongTransition,
    identitySpecialOrthogonalNorthPoleProductTargetDensity,
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal,
    abs_det_identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative_eq_targetDensity]

end PositiveDefiniteIntegralLattice
