import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductLiteralSphereFiber

/-!
# The normalized local identity fiber pushforward on the ambient sphere

This module applies the measurable sphere-side fiber parametrization to the
coupled normalized-sphere source.  The coordinate-side and sphere-side
pushforwards are compared only through the opaque restricted product transport
and the global composition identity from the preceding module.

The positive-hemisphere factor two, the sphere-step scalar, and the reciprocal
fixed transition scalar all remain explicit.  No global differential-fiber
kernel, total-mass cancellation, rank recurrence, or Gamma evaluation is used.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductLiteralSphereFiberMeasureGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleProductLiteralSphereFiberMeasureGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductLiteralSphereFiberMeasureMappedGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductLiteralSphereFiberMeasureMappedGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Literal lower differential Haar times normalized full-sphere measure on
the positive hemisphere, restricted to the exact sphere-side coupled source. -/
def
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
    (n : ℕ) :
    Measure
      (identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere (n + 1)) :=
  (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
    n).restrict
      (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
        n)

/-- The restricted coordinate-probability product returns to twice the
restricted normalized-sphere hemisphere product. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure_to_restrictedSphere
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
          n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure
          n) =
      (2 : ℝ≥0∞) •
        identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
          n := by
  exact
    map_identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure_toSphere
      n

/-- The mapped sphere-side fiber map agrees almost everywhere with the
coordinate-side mapped fiber map after the product-to-sphere transport. The
underlying pointwise identity is global; this restricted form is packaged for
`Measure.map_congr` interfaces. -/
theorem
    ae_identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiber_comp_productToSphere_eq_mappedFiber
    (n : ℕ) :
    ∀ᵐ p ∂
      identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure
        n,
      identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
          n
          (identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
            n p) =
        identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
          n p := by
  exact
    Filter.Eventually.of_forall fun p =>
      congrFun
        (identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiber_comp_productToSphere
          n) p

/-- The coordinate-side mapped fiber pushforward is twice the corresponding
sphere-side pushforward on the exact coupled source. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral_restrictedNormalized_eq_two_smul_map_sphereFiber
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
          n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure
          n) =
      (2 : ℝ≥0∞) •
        Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
            n)
          (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
            n) := by
  calc
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
          n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure
          n) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
          n)
        (Measure.map
          (identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
            n)
          (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure
            n)) := by
      rw [
        Measure.map_map
          (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
            n)
          (measurableEmbedding_identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
            n).measurable,
        identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiber_comp_productToSphere]
    _ =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
          n)
        ((2 : ℝ≥0∞) •
          identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
            n) := by
      rw [
        map_identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure_to_restrictedSphere]
    _ =
      (2 : ℝ≥0∞) •
        Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
            n)
          (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
            n) := by
      rw [Measure.map_smul]

/-- The verified normalized local differential comparison restated entirely
on the ambient sphere-side coupled source. All three normalization scalars
remain explicit. -/
theorem
    identitySpecialOrthogonalSphereStep_smul_two_smul_map_restrictedNormalizedSphereFiber_eq_smul_higherDifferential
    (n : ℕ) :
    identitySpecialOrthogonalSphereStep (n + 2) •
        ((2 : ℝ≥0∞) •
          Measure.map
            (identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
              n)
            (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
              n)) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|)⁻¹ •
        (specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
              (n + 1)) := by
  rw [←
    map_identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral_restrictedNormalized_eq_two_smul_map_sphereFiber]
  exact
    identitySpecialOrthogonalSphereStep_smul_map_restrictedNormalizedLiteralFiber_eq_smul_higherDifferential
      n

end PositiveDefiniteIntegralLattice
