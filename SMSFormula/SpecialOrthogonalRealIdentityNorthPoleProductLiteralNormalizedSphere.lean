import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereProbabilityTransport
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductLiteralNormalizedSource

/-!
# Return the literal normalized hemisphere product to the sphere

This module lifts the coordinate probability-to-sphere transport through the
literal lower differential product.  The factor two remains explicit because
the source uses probability measure on one open hemisphere while the target
uses the restriction of normalized full-sphere measure.

The coupled exact-source restriction, global fiber kernel, total-mass
cancellation, and rank recurrence remain unapplied.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductLiteralNormalizedSphereGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleProductLiteralNormalizedSphereGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- Leave the literal lower group coordinate fixed and return the ball
coordinate to the full last-column sphere. -/
def identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
    (n : ℕ) :
    (identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
      (identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere (n + 1)) :=
  Prod.map id
    (Subtype.val ∘
      (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph (n + 1)).symm)

/-- Literal lower differential Haar restricted to its identity chart, times
normalized full-sphere measure restricted to the positive hemisphere. -/
def
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
    (n : ℕ) :
    Measure
      (identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere (n + 1)) :=
  ((identitySpecialOrthogonalDifferentialMeasure n).restrict
    (identitySpecialOrthogonalLiteralIdentityChartSource n)).prod
      ((identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
        (identitySpecialOrthogonalNorthPoleHemisphere (n + 1)))

/-- The literal lower differential/probability-hemisphere product returns to
twice the corresponding normalized full-sphere hemisphere restriction. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
          n)
        (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedHemisphereMeasure
          n) =
      (2 : ℝ≥0∞) •
        identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
          n := by
  let ν :=
    (identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
      (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))
  let ρ :=
    identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
      (n + 1)
  letI : IsFiniteMeasure ν := inferInstance
  letI : IsFiniteMeasure ρ :=
    ⟨by
      change
        identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
            (n + 1) Set.univ <
          ⊤
      rw [
        identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure_univ]
      simp⟩
  rw [
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedHemisphereMeasure,
    identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere,
    ← Measure.map_prod_map _ _ measurable_id
      ((continuous_subtype_val.comp
        (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
          (n + 1)).symm.continuous).measurable),
    Measure.map_id,
    map_identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure_ambient,
    Measure.prod_smul_right,
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereHemisphereMeasure]

end PositiveDefiniteIntegralLattice
