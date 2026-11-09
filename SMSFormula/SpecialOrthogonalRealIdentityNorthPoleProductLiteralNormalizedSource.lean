import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductLiteralHemisphereNormalization

/-!
# The coupled normalized literal north-pole product source

This module carries the internally proved positive-hemisphere normalization
through the coupled exact product source and the already verified literal
fiber pushforward.  The sphere-step scalar and reciprocal fixed transition
scalar remain explicit and on opposite sides of the local comparison.

No global fiber kernel, total-mass cancellation, rank recurrence, or Gamma
evaluation is used here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductLiteralNormalizedSourceGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleProductLiteralNormalizedSourceGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductLiteralNormalizedSourceMappedGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductLiteralNormalizedSourceMappedGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The literal lower differential/probability-hemisphere product restricted
to the transported coupled exact source. -/
def
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure
    (n : ℕ) :
    Measure
      (identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedHemisphereMeasure
    n).restrict
      (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
        n)

/-- Restricting the raw literal product to the coupled source preserves the
explicit positive-hemisphere sphere-step factor. -/
theorem
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialSphereMeasure_eq_sphereStep_smul_normalized
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialSphereMeasure
        n =
      identitySpecialOrthogonalSphereStep (n + 2) •
        identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure
          n := by
  rw [
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialSphereMeasure,
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereMeasure_eq_sphereStep_smul,
    Measure.restrict_smul,
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure]

/-- The normalized coupled literal product satisfies the verified local
higher-differential comparison with both normalization scalars left
explicit. -/
theorem
    identitySpecialOrthogonalSphereStep_smul_map_restrictedNormalizedLiteralFiber_eq_smul_higherDifferential
    (n : ℕ) :
    identitySpecialOrthogonalSphereStep (n + 2) •
        Measure.map
          (identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
            n)
          (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure
            n) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|)⁻¹ •
        (specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
              (n + 1)) := by
  rw [← Measure.map_smul]
  rw [←
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialSphereMeasure_eq_sphereStep_smul_normalized]
  exact
    map_identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral_eq_smul
      n

end PositiveDefiniteIntegralLattice
