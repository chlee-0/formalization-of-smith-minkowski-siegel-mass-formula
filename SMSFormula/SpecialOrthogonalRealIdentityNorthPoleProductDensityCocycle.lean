import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductCompositionScalarCancellation

/-!
# Intrinsic density cocycle of the identity north-pole product

This file substitutes the three already verified differential determinants
into the scalar-cancelled real identity.  On the full exact source, the lower
chart/sphere product density is the intrinsic square Jacobian times the higher
identity-chart density.

No nonlinear measure equality is composed here, and no differential fiber
identification or rank recurrence is asserted.
-/

open scoped Matrix Matrix.Norms.Operator ENNReal

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The intrinsic source/target density cocycle holds at every point of the
exact higher-chart source. -/
theorem
    identitySpecialOrthogonalNorthPoleProductDensityCocycleAt_full
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalNorthPoleProductDensityCocycleAt n p := by
  rw [identitySpecialOrthogonalNorthPoleProductDensityCocycleAt,
    ←
      ofReal_abs_det_identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
        n p,
    identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian,
    ←
      ofReal_abs_det_identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative_eq_targetDensityAlongTransition
        n p,
    ← ENNReal.ofReal_mul
      (abs_nonneg
        (LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative
            n p.1).toLinearMap))]
  exact congrArg ENNReal.ofReal
    (abs_det_identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_eq_square_mul_centered
      n p)

end PositiveDefiniteIntegralLattice
