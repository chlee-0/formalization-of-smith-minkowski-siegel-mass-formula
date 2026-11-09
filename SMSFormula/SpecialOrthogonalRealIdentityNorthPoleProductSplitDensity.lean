import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductLowerDensity

/-!
# Split-carrier density of the identity north-pole product

This file packages the left-trivialized split derivative as a square
endomorphism of the scalar-extended rational lower tangent times the plain
last-column tangent.  Its determinant is the product of the directly
transported lower determinant and the transverse determinant, hence is
exactly the source-product density.

The construction uses only the opaque split block decomposition.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Replace the Euclidean last-column input carrier by the plain function
carrier, leaving the mapped rational tangent unchanged. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductSplitPlainSourceEquiv
    (n : ℕ) :
    (identitySpecialOrthogonalMappedTangent n × (Fin n → ℝ)) ≃L[ℝ]
      (identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n)) :=
  (ContinuousLinearEquiv.refl ℝ
      (identitySpecialOrthogonalMappedTangent n)).prodCongr
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

/-- Transport the lower output of the genuine split derivative back to the
scalar-extended rational tangent, leaving the transverse output unchanged. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductSplitMappedTargetEquiv
    (n : ℕ) :
    (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) ≃L[ℝ]
      (identitySpecialOrthogonalMappedTangent n × (Fin n → ℝ)) :=
  (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
      n).symm.prodCongr
    (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))

/-- The genuine split derivative, made square on the mapped lower tangent and
plain last-column tangent carriers. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n))
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    (identitySpecialOrthogonalMappedTangent n × (Fin n → ℝ)) →L[ℝ]
      (identitySpecialOrthogonalMappedTangent n × (Fin n → ℝ)) :=
  (identitySpecialOrthogonalNorthPoleProductSplitMappedTargetEquiv
      n).toContinuousLinearMap.comp
    ((identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative
      n p hp).comp
      (identitySpecialOrthogonalNorthPoleProductSplitPlainSourceEquiv
        n).toContinuousLinearMap)

/-- The mixed block of the mapped square split derivative. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductMappedSplitMixedDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n))
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    (Fin n → ℝ) →L[ℝ] identitySpecialOrthogonalMappedTangent n :=
  (ContinuousLinearMap.fst ℝ
      (identitySpecialOrthogonalMappedTangent n) (Fin n → ℝ)).comp
    ((identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
      n p hp).comp
      (ContinuousLinearMap.inr ℝ
        (identitySpecialOrthogonalMappedTangent n) (Fin n → ℝ)))

@[simp]
theorem
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_fst
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (H : identitySpecialOrthogonalMappedTangent n) :
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
        n p hp (H, 0) =
      (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
          n p hp H,
        0) := by
  apply Prod.ext
  · rfl
  · have hblock :=
      identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative_block_decomposition
        n hp H 0
    simpa [identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative,
      identitySpecialOrthogonalNorthPoleProductSplitMappedTargetEquiv,
      identitySpecialOrthogonalNorthPoleProductSplitPlainSourceEquiv] using
        congrArg Prod.snd hblock

@[simp]
theorem
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_snd
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (h : Fin n → ℝ) :
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
        n p hp (0, h) =
      (identitySpecialOrthogonalNorthPoleProductMappedSplitMixedDerivative
          n p hp h,
        identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
          n p h) := by
  apply Prod.ext
  · rfl
  · have hblock :=
      identitySpecialOrthogonalNorthPoleProductLeftTrivializedSplitDerivative_block_decomposition
        n hp 0 (WithLp.toLp 2 h)
    simpa [identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative,
      identitySpecialOrthogonalNorthPoleProductSplitMappedTargetEquiv,
      identitySpecialOrthogonalNorthPoleProductSplitPlainSourceEquiv,
      identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative_apply]
      using congrArg Prod.snd hblock

/-- Upper block form of the square mapped split derivative. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_block
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (H : identitySpecialOrthogonalMappedTangent n) (h : Fin n → ℝ) :
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
        n p hp (H, h) =
      (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
          n p hp H +
        identitySpecialOrthogonalNorthPoleProductMappedSplitMixedDerivative
          n p hp h,
        identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
          n p h) := by
  rw [show (H, h) = (H, 0) + (0, h) by ext <;> simp, map_add,
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_fst,
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_snd]
  simp

/-- The determinant of the mapped square split derivative factors through its
lower and transverse diagonal blocks. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_det
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
          n p hp).toLinearMap =
      LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
            n p hp).toLinearMap *
        LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
            n p) := by
  apply LinearMap.det_eq_mul_of_apply_eq_upperBlocks
      (Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ)
        (1 : Matrix (Fin n) (Fin n) ℚ))
      (Pi.basisFun ℝ (Fin n))
      (identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
        n p hp).toLinearMap
      (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
        n p hp).toLinearMap
      (identitySpecialOrthogonalNorthPoleProductMappedSplitMixedDerivative
        n p hp).toLinearMap
      (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
        n p)
  exact identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_block
    n hp

/-- The transported lower diagonal block depends only on the lower-chart
coordinate, not on the last-column coordinate. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_eq_zero_snd
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
        n p hp =
      identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
        n (p.1, 0) ⟨hp.1, by simp⟩ := by
  apply ContinuousLinearMap.ext
  intro H
  apply Subtype.ext
  have hp_ambient :=
    congrArg (fun D => D H)
      (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_ambient
        n hp)
  have hzero_ambient :=
    congrArg (fun D => D H)
      (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_ambient
        n (p := (p.1, 0)) ⟨hp.1, by simp⟩)
  exact hp_ambient.trans hzero_ambient.symm

/-- At every product-domain point, the lower diagonal determinant is the
lower identity-chart density. -/
theorem
    ofReal_abs_det_identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    ENNReal.ofReal
      |LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
          n p hp).toLinearMap| =
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero 1
        ⟨p.1, hp.1⟩ := by
  rw [
    identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_eq_zero_snd
      n hp]
  exact
    ofReal_abs_det_identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative_eq_density
      n hp.1

/-- On the exact higher-chart source, the absolute determinant of the
mapped square split derivative is exactly the source-product
density. -/
theorem
    ofReal_abs_det_identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    ENNReal.ofReal
      |LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
          n p.1
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
            n p.2)).toLinearMap| =
      identitySpecialOrthogonalNorthPoleProductSourceDensity n p := by
  have hp :=
    identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset n p.2
  rw [identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative_det,
    abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    ofReal_abs_det_identitySpecialOrthogonalNorthPoleProductLowerMappedTangentDerivative
      n hp,
    abs_identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative_det_eq_inv_sqrt
      n hp]
  simp [identitySpecialOrthogonalNorthPoleProductSourceDensity,
    identitySpecialOrthogonalNorthPoleProductLowerCoordinate,
    identitySpecialOrthogonalNorthPoleCoordinateDensity,
    identitySpecialOrthogonalNorthPoleFinalCoordinate, one_div]

end PositiveDefiniteIntegralLattice
