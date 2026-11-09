import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductCompositionTangent

/-!
# Basis-level centered composition of the identity north-pole product

This file evaluates the verified centered-composition tangent equality only
on the fixed transition source basis.  The resulting vector family is compared
with the genuine mapped split derivative through an alternating determinant.
No full conjugated carrier endomorphism or application theorem is introduced.

No determinant scalar cancellation, `ENNReal` density cocycle, nonlinear
measure comparison, fiber identification, or rank recurrence is asserted here.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The fixed higher-rank mapped tangent transported to the mapped/plain
lower-tangent and last-column carrier. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv
    (n : ℕ) :
    identitySpecialOrthogonalMappedTangent (n + 1) ≃L[ℝ]
      (identitySpecialOrthogonalMappedTangent n × (Fin n → ℝ)) :=
  (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
      (n + 1)).trans
    ((identitySpecialOrthogonalTangentContinuousLinearEquiv n).trans
      (identitySpecialOrthogonalNorthPoleProductSplitMappedTargetEquiv n))

/-- The fixed transition source basis transported from the native Euclidean
last-column carrier to the mapped/plain split carrier. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductMappedSplitBasis
    (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))))
      ℝ
      (identitySpecialOrthogonalMappedTangent n × (Fin n → ℝ)) :=
  (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n).map
    (identitySpecialOrthogonalNorthPoleProductSplitPlainSourceEquiv
      n).symm.toLinearEquiv

/-- On each fixed source-basis vector, the mapped split derivative is the
higher centered/pointwise composition transported through the fixed higher
tangent split. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_basis_apply
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
    (i : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)))) :
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
        n p.1
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
          n p.2)
        (identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n i) =
      identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv n
        (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
          n p
          (fderiv ℝ
            (identitySpecialOrthogonalNorthPoleProductTransition n) p.1
            (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
              n i))) := by
  have htangent :=
    congrArg (fun D =>
      D (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n i))
      (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative_comp_transition_tangent
        n p)
  change
    identitySpecialOrthogonalNorthPoleProductSplitMappedTargetEquiv n
      (identitySpecialOrthogonalTangentContinuousLinearEquiv n
        (identitySpecialOrthogonalNorthPoleProductLeftTrivializedTangentDerivative
          n p.1
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
            n p.2)
          (identitySpecialOrthogonalNorthPoleProductSplitPlainSourceEquiv n
            ((identitySpecialOrthogonalNorthPoleProductSplitPlainSourceEquiv
              n).symm
              (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
                n i))))) =
      identitySpecialOrthogonalNorthPoleProductSplitMappedTargetEquiv n
        (identitySpecialOrthogonalTangentContinuousLinearEquiv n
          (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
            (n + 1)
            (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
              n p
              (fderiv ℝ
                (identitySpecialOrthogonalNorthPoleProductTransition n) p.1
                (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
                  n i)))))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg
    (fun K : identitySpecialOrthogonalTangent (n + 1) =>
      identitySpecialOrthogonalNorthPoleProductSplitMappedTargetEquiv n
        (identitySpecialOrthogonalTangentContinuousLinearEquiv n K))
    htangent.symm

/-- The mapped split determinant can be evaluated in the transported fixed
source basis. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMappedSplitBasis_det
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    (identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n).det
        (fun i =>
          identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
            n p hp
            (identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n i)) =
      LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
          n p hp).toLinearMap := by
  rw [show (fun i =>
      identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
        n p hp
        (identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n i)) =
      (identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
        n p hp).toLinearMap ∘
        identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n by rfl,
    Module.Basis.det_comp, Module.Basis.det_self, mul_one]

/-- Alternating-determinant form of the basiswise centered-composition
comparison. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMappedSplit_det_eq_composition_basis_det
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
          n p.1
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
            n p.2)).toLinearMap =
      (identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n).det
        (fun i =>
          identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv n
            (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
              n p
              (fderiv ℝ
                (identitySpecialOrthogonalNorthPoleProductTransition n) p.1
                (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
                  n i)))) := by
  rw [←
    identitySpecialOrthogonalNorthPoleProductMappedSplitBasis_det
      n
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
        n p.2)]
  congr 1
  funext i
  exact
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_basis_apply
      n p i

end PositiveDefiniteIntegralLattice
