import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductTransverseDeterminant
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductJacobianNormalization
import SMSFormula.LinearMapUpperBlockDeterminant

/-!
# Lower density of the identity north-pole product

This file transports the lower component of the split tangent
derivative directly to the scalar-extended rational identity tangent.  Its
ambient value is the lower inverse-chart moving derivative, whose
determinant is then identified with the lower identity-chart differential
density.

The direct transported definition avoids expanding the full carrier-change
map in an application theorem.  No full product-density cocycle, measure
comparison, fiber disintegration, or rank recurrence is asserted here.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The genuine lower split component, transported directly back to the
scalar-extended rational identity tangent carrier. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n))
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    identitySpecialOrthogonalMappedTangent n →L[ℝ]
      identitySpecialOrthogonalMappedTangent n :=
  (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
      n).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ
      (identitySpecialOrthogonalTangent n) (Fin n → ℝ)).comp
      ((identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
        n p hp).comp
        (ContinuousLinearMap.inl ℝ
          (identitySpecialOrthogonalMappedTangent n)
          (EuclideanSpace ℝ (Fin n)))))

/-- After ambient inclusion, the transported lower component is exactly the
lower inverse-chart moving derivative. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_ambient
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    (identitySpecialOrthogonalMappedTangent n).subtypeL.comp
        (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
          n p hp) =
      identitySpecialOrthogonalLowerChartMovingDerivative n p.1 := by
  apply ContinuousLinearMap.ext
  intro H
  have hblock :=
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative_block_decomposition
      n hp H 0
  change
    (((identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv n).symm
      ((identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
        n p hp (H, 0)).1) :
      identitySpecialOrthogonalMappedTangent n) :
        Matrix (Fin n) (Fin n) ℝ) =
      identitySpecialOrthogonalLowerChartMovingDerivative n p.1 H
  have heq :
      (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv n)
          ((identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv n).symm
            ((identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
              n p hp (H, 0)).1)) =
        (identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
          n p hp (H, 0)).1 :=
    (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv n
      ).apply_symm_apply _
  calc
    _ =
        (((identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
          n p hp (H, 0)).1 : identitySpecialOrthogonalTangent n) :
            Matrix (Fin n) (Fin n) ℝ) := by
      exact congrArg
        (fun K : identitySpecialOrthogonalTangent n =>
          (K : Matrix (Fin n) (Fin n) ℝ)) heq
    _ = identitySpecialOrthogonalLowerChartMovingDerivative n p.1 H := by
      simpa using congrArg Prod.fst hblock

/-- The fixed-first-coordinate joint transition has the transported genuine
lower component as its derivative at the diagonal point. -/
theorem
    hasFDerivAt_identitySpecialOrthogonalLowerJointTransitionSlice
    (n : ℕ)
    {X : identitySpecialOrthogonalMappedTangent n}
    (hX : X ∈ identitySpecialOrthogonalLowerChartTargetSet n) :
    HasFDerivAt
      (fun Z =>
        specialFormPreservingSmoothRealJointTransitionCoordinate
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero
          (X, Z))
      (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
        n (X, 0) ⟨hX, by simp⟩) X := by
  let q := identitySpecialOrthogonalLowerInverseCoordinateMatrix n X
  let dQ :=
    fderiv ℝ (identitySpecialOrthogonalLowerInverseCoordinateMatrix n) X
  let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ :=
    ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ)
      q⁻¹ 1
  have hdetq : q.det = 1 := by
    simpa [q, identitySpecialOrthogonalLowerInverseCoordinateMatrix] using
      det_specialFormPreservingSmoothRealInverseCoordinateMatrix
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero
        (1 : specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)))
        ⟨X, hX⟩
  have hunit : IsUnit q.det := by
    rw [hdetq]
    exact isUnit_one
  have hqadj : q.adjugate = q⁻¹ := by
    calc
      q.adjugate = 1 * q.adjugate := (Matrix.one_mul _).symm
      _ = (q⁻¹ * q) * q.adjugate := by
        rw [Matrix.nonsing_inv_mul q hunit]
      _ = q⁻¹ * (q * q.adjugate) := by
        rw [Matrix.mul_assoc]
      _ = q⁻¹ := by
        rw [Matrix.mul_adjugate, hdetq, one_smul, Matrix.mul_one]
  have hinv :
      HasFDerivAt
        (identitySpecialOrthogonalLowerInverseCoordinateMatrix n) dQ X := by
    simpa [identitySpecialOrthogonalLowerInverseCoordinateMatrix, dQ] using
      hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero
        (1 : specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)))
        X hX
  have hinner :
      HasFDerivAt
        (fun Z => q⁻¹ *
          identitySpecialOrthogonalLowerInverseCoordinateMatrix n Z)
        (identitySpecialOrthogonalLowerChartMovingDerivative n X) X := by
    convert L.hasFDerivAt.comp X hinv using 1
    · funext Z
      change q⁻¹ * identitySpecialOrthogonalLowerInverseCoordinateMatrix n Z =
        (q⁻¹ * identitySpecialOrthogonalLowerInverseCoordinateMatrix n Z) * 1
      exact (mul_one _).symm
  have hinnerAt :
      q⁻¹ * identitySpecialOrthogonalLowerInverseCoordinateMatrix n X = 1 := by
    change q⁻¹ * q = 1
    exact Matrix.nonsing_inv_mul q hunit
  have hfwd :
      HasFDerivAt
        (specialFormPreservingSmoothRealForwardCoordinate
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero)
        (fderiv ℝ
          (specialFormPreservingSmoothRealForwardCoordinate
            (1 : Matrix (Fin n) (Fin n) ℚ)
            identityRationalForm_isSymm identityRationalForm_det_ne_zero)
          (q⁻¹ * identitySpecialOrthogonalLowerInverseCoordinateMatrix n X))
        (q⁻¹ *
          identitySpecialOrthogonalLowerInverseCoordinateMatrix n X) :=
    ((contDiff_specialFormPreservingSmoothRealForwardCoordinate
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
      ).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hmoving :=
    identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_ambient
      n (p := (X, 0)) ⟨hX, by simp⟩
  have hderiv :
      (fderiv ℝ
        (specialFormPreservingSmoothRealForwardCoordinate
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero) 1).comp
          (identitySpecialOrthogonalLowerChartMovingDerivative n X) =
        identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
          n (X, 0) ⟨hX, by simp⟩ := by
    rw [← hmoving, ← ContinuousLinearMap.comp_assoc,
      fderiv_specialFormPreservingSmoothRealForwardCoordinate_one_comp_subtypeL]
    simp
  have hcomp :=
    hfwd.comp X hinner
  rw [hinnerAt] at hcomp
  convert hcomp using 1
  · funext Z
    change
      specialFormPreservingSmoothRealForwardCoordinate
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero
          (q.adjugate *
            identitySpecialOrthogonalLowerInverseCoordinateMatrix n Z) =
        specialFormPreservingSmoothRealForwardCoordinate
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero
          (q⁻¹ *
            identitySpecialOrthogonalLowerInverseCoordinateMatrix n Z)
    rw [hqadj]
  · exact hderiv.symm

/-- The diagonal partial derivative is the transported lower component. -/
theorem
    identitySpecialOrthogonalLowerDiagonalPartialDerivative_eq
    (n : ℕ)
    {X : identitySpecialOrthogonalMappedTangent n}
    (hX : X ∈ identitySpecialOrthogonalLowerChartTargetSet n) :
    (fderiv ℝ
        (specialFormPreservingSmoothRealJointTransitionCoordinate
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero)
        (X, X)).comp
      (specialFormPreservingSmoothRealSecondFactorInclusion
        (1 : Matrix (Fin n) (Fin n) ℚ)) =
      identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
        n (X, 0) ⟨hX, by simp⟩ := by
  have hJ :
      DifferentiableAt ℝ
        (specialFormPreservingSmoothRealJointTransitionCoordinate
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero)
        (X, X) := by
    exact
      ((contDiffOn_specialFormPreservingSmoothRealJointTransitionCoordinate
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero
        (1 : specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)))
        ).differentiableOn (by simp)).differentiableAt
          ((isOpen_identitySpecialOrthogonalLowerChartTargetSet n).prod
            (isOpen_identitySpecialOrthogonalLowerChartTargetSet n)
            |>.mem_nhds ⟨hX, hX⟩)
  have hi :
      HasFDerivAt (fun Z => (X, Z))
        (specialFormPreservingSmoothRealSecondFactorInclusion
          (1 : Matrix (Fin n) (Fin n) ℚ)) X :=
    hasFDerivAt_prodMk_right X X
  have hslice :=
    (hJ.hasFDerivAt.comp X hi).fderiv
  calc
    _ = fderiv ℝ
        (fun Z => specialFormPreservingSmoothRealJointTransitionCoordinate
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero (X, Z)) X :=
      hslice.symm
    _ = _ :=
      (hasFDerivAt_identitySpecialOrthogonalLowerJointTransitionSlice
        n hX).fderiv

/-- The determinant of the transported genuine lower component is exactly the
lower identity-chart differential density. -/
theorem
    abs_det_identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_eq_density
    (n : ℕ)
    {X : identitySpecialOrthogonalMappedTangent n}
    (hX : X ∈ identitySpecialOrthogonalLowerChartTargetSet n) :
    |LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
          n (X, 0) ⟨hX, by simp⟩).toLinearMap| =
      specialFormPreservingSmoothRealChartCoordinateDensity
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero 1
        ⟨X, hX⟩ := by
  rw [
    specialFormPreservingSmoothRealChartCoordinateDensity_eq_diagonalPartialJacobian]
  change
    |LinearMap.det
      (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
        n (X, 0) ⟨hX, by simp⟩).toLinearMap| =
      |LinearMap.det
        ((fderiv ℝ
          (specialFormPreservingSmoothRealJointTransitionCoordinate
            (1 : Matrix (Fin n) (Fin n) ℚ)
            identityRationalForm_isSymm identityRationalForm_det_ne_zero)
          (X, X)).comp
            (specialFormPreservingSmoothRealSecondFactorInclusion
              (1 : Matrix (Fin n) (Fin n) ℚ))).toLinearMap|
  rw [identitySpecialOrthogonalLowerDiagonalPartialDerivative_eq n hX]

/-- `ENNReal` form of the lower transported determinant identity. -/
theorem
    ofReal_abs_det_identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_eq_density
    (n : ℕ)
    {X : identitySpecialOrthogonalMappedTangent n}
    (hX : X ∈ identitySpecialOrthogonalLowerChartTargetSet n) :
    ENNReal.ofReal
      |LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
          n (X, 0) ⟨hX, by simp⟩).toLinearMap| =
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero 1
        ⟨X, hX⟩ := by
  rw [specialFormPreservingSmoothRealChartCoordinateDensityENNReal,
    abs_det_identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_eq_density
      n hX]

end PositiveDefiniteIntegralLattice
