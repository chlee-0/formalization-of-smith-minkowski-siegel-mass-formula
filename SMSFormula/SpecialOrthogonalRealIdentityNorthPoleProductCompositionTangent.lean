import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductSplitDensity
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductHigherDensity

/-!
# Centered composition tangent of the identity north-pole product

This file compares the higher centered moving derivative, composed
with the pointwise product-transition derivative, with the mapped
split derivative.  The comparison is routed through ambient left
trivialization and the fixed tangent equivalences.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

open Matrix Metric Set

namespace PositiveDefiniteIntegralLattice

/-- The higher centered derivative is the already verified diagonal
partial derivative, regarded as the transported lower moving operator in the
higher rank. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative_eq_lowerMapped
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
        n p =
      identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
        (n + 1)
        (identitySpecialOrthogonalNorthPoleProductTransition n p.1, 0)
        ⟨(identitySpecialOrthogonalNorthPoleProductHigherCoordinate n
            (identitySpecialOrthogonalNorthPoleProductTransitionOnSource
              n p)).2,
          by simp⟩ := by
  exact
    identitySpecialOrthogonalLowerDiagonalPartialDerivative_eq
      (n + 1)
      (identitySpecialOrthogonalNorthPoleProductHigherCoordinate n
        (identitySpecialOrthogonalNorthPoleProductTransitionOnSource n p)).2

/-- After ambient inclusion, the higher centered derivative is the native
higher identity-chart moving derivative. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative_ambient
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    (identitySpecialOrthogonalMappedTangent (n + 1)).subtypeL.comp
        (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
          n p) =
      identitySpecialOrthogonalLowerChartMovingDerivative
        (n + 1)
        (identitySpecialOrthogonalNorthPoleProductTransition n p.1) := by
  rw [
    identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative_eq_lowerMapped]
  have hy :
      identitySpecialOrthogonalNorthPoleProductTransition n p.1 ∈
        identitySpecialOrthogonalLowerChartTargetSet (n + 1) := by
    exact
      (identitySpecialOrthogonalNorthPoleProductHigherCoordinate n
        (identitySpecialOrthogonalNorthPoleProductTransitionOnSource n p)).2
  exact
    identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_ambient
      (n + 1)
      ⟨hy, by simp⟩

/-- On the exact higher-chart source, applying the higher inverse coordinate
to the product-transition coordinate recovers the represented product
matrix. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHigherInverseCoordinate_transition
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp :
      p ∈ identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    specialFormPreservingSmoothRealInverseCoordinateMatrix
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero
        (identitySpecialOrthogonalNorthPoleProductTransition n p) =
      identitySpecialOrthogonalNorthPoleProductMatrix n p := by
  rcases hp with ⟨q, hq, rfl⟩
  let A :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
  let y : identitySpecialOrthogonalLowerChartTargetSet (n + 1) :=
    ⟨identitySpecialOrthogonalNorthPoleProductTransition n q.1, by
      rw [
        identitySpecialOrthogonalNorthPoleProductTransition_eq_identityChart
          n q hq]
      exact A.map_source hq⟩
  have hgroup :
      identitySpecialOrthogonalLowerChartGroup (n + 1) y =
        identitySpecialOrthogonalNorthPoleProductMappedGroup n q := by
    change A.symm y.1 =
      identitySpecialOrthogonalNorthPoleProductMappedGroup n q
    rw [show y.1 =
        A (identitySpecialOrthogonalNorthPoleProductMappedGroup n q) by
      exact
        identitySpecialOrthogonalNorthPoleProductTransition_eq_identityChart
          n q hq]
    exact A.left_inv hq
  calc
    specialFormPreservingSmoothRealInverseCoordinateMatrix
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero
        (identitySpecialOrthogonalNorthPoleProductTransition n q.1) =
        (identitySpecialOrthogonalLowerChartGroup (n + 1) y).1.1.1 := by
      exact (coe_identitySpecialOrthogonalLowerChartGroup (n + 1) y).symm
    _ =
        (identitySpecialOrthogonalNorthPoleProductMappedGroup n q).1.1.1 := by
      rw [hgroup]
    _ = identitySpecialOrthogonalNorthPoleProductMatrix n q.1 :=
      identitySpecialOrthogonalNorthPoleProductMappedGroup_coe n q

/-- The inverse-coordinate/product recovery holds eventually around every
point of the exact open source. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHigherInverseCoordinate_transition_eventuallyEq
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    (fun z =>
      specialFormPreservingSmoothRealInverseCoordinateMatrix
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero
        (identitySpecialOrthogonalNorthPoleProductTransition n z)) =ᶠ[nhds p.1]
      identitySpecialOrthogonalNorthPoleProductMatrix n := by
  filter_upwards
    [(identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
      ).mem_nhds p.2]
    with z hz
  exact
    identitySpecialOrthogonalNorthPoleProductHigherInverseCoordinate_transition
      n hz

/-- Differentiating the inverse-coordinate/product recovery gives the exact
pointwise product derivative. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHigherInverseCoordinateDerivative_comp_transition
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    (fderiv ℝ
        (specialFormPreservingSmoothRealInverseCoordinateMatrix
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero)
        (identitySpecialOrthogonalNorthPoleProductTransition n p.1)).comp
      (fderiv ℝ
        (identitySpecialOrthogonalNorthPoleProductTransition n) p.1) =
      identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p.1 := by
  let A :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
  have htarget :
      identitySpecialOrthogonalNorthPoleProductTransition n p.1 ∈ A.target :=
    (identitySpecialOrthogonalNorthPoleProductHigherCoordinate n
      (identitySpecialOrthogonalNorthPoleProductTransitionOnSource n p)).2
  have hinverse :
      HasFDerivAt
        (specialFormPreservingSmoothRealInverseCoordinateMatrix
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero)
        (fderiv ℝ
          (specialFormPreservingSmoothRealInverseCoordinateMatrix
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
            identityRationalForm_isSymm identityRationalForm_det_ne_zero)
          (identitySpecialOrthogonalNorthPoleProductTransition n p.1))
        (identitySpecialOrthogonalNorthPoleProductTransition n p.1) :=
    hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
      1 _ htarget
  have htransition :
      HasFDerivAt
        (identitySpecialOrthogonalNorthPoleProductTransition n)
        (fderiv ℝ
          (identitySpecialOrthogonalNorthPoleProductTransition n) p.1)
        p.1 :=
    (((contDiffOn_identitySpecialOrthogonalNorthPoleProductTransition_higherChartSource
      n).contDiffAt
        ((identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
          ).mem_nhds p.2)).differentiableAt (by simp)).hasFDerivAt
  have hchain := (hinverse.comp p.1 htransition).fderiv
  have heventually :
      fderiv ℝ
          (fun z =>
            specialFormPreservingSmoothRealInverseCoordinateMatrix
              (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
              identityRationalForm_isSymm identityRationalForm_det_ne_zero
              (identitySpecialOrthogonalNorthPoleProductTransition n z))
          p.1 =
        fderiv ℝ
          (identitySpecialOrthogonalNorthPoleProductMatrix n) p.1 :=
    (identitySpecialOrthogonalNorthPoleProductHigherInverseCoordinate_transition_eventuallyEq
      n p).fderiv_eq
  rw [
    fderiv_identitySpecialOrthogonalNorthPoleProductMatrix_pointwise
      n
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
        n p.2)] at heventually
  exact hchain.symm.trans heventually

/-- The higher identity-chart moving derivative composed with the pointwise
transition is the genuine ambient left-trivialized product derivative. -/
theorem
    identitySpecialOrthogonalHigherMovingDerivative_comp_transition_eq_leftTrivialized
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    (identitySpecialOrthogonalLowerChartMovingDerivative
        (n + 1)
        (identitySpecialOrthogonalNorthPoleProductTransition n p.1)).comp
      (fderiv ℝ
        (identitySpecialOrthogonalNorthPoleProductTransition n) p.1) =
      identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
        n p.1 := by
  apply ContinuousLinearMap.ext
  intro q
  rw [
    ContinuousLinearMap.comp_apply,
    identitySpecialOrthogonalLowerChartMovingDerivative_apply,
    identitySpecialOrthogonalLowerInverseCoordinateMatrix,
    identitySpecialOrthogonalNorthPoleProductHigherInverseCoordinate_transition
      n p.2,
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_apply]
  exact congrArg
    (fun D => (identitySpecialOrthogonalNorthPoleProductMatrix n p.1)⁻¹ * D q)
    (identitySpecialOrthogonalNorthPoleProductHigherInverseCoordinateDerivative_comp_transition
      n p)

/-- After the identity-on-ambient tangent equivalence, the centered
moving composition is exactly the tangent-valued left-trivialized
derivative. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative_comp_transition_tangent
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
        (n + 1)).toContinuousLinearMap.comp
      ((identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
        n p).comp
        (fderiv ℝ
          (identitySpecialOrthogonalNorthPoleProductTransition n) p.1)) =
      identitySpecialOrthogonalNorthPoleProductLeftTrivializedTangentDerivative
        n p.1
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
          n p.2) := by
  apply ContinuousLinearMap.ext
  intro q
  apply Subtype.ext
  have hambient :=
    congrArg (fun D => D q)
      (show
        (identitySpecialOrthogonalMappedTangent (n + 1)).subtypeL.comp
            ((identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
              n p).comp
              (fderiv ℝ
                (identitySpecialOrthogonalNorthPoleProductTransition n) p.1)) =
          identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
            n p.1 by
        rw [← ContinuousLinearMap.comp_assoc,
          identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative_ambient,
          identitySpecialOrthogonalHigherMovingDerivative_comp_transition_eq_leftTrivialized])
  simpa using hambient

end PositiveDefiniteIntegralLattice
