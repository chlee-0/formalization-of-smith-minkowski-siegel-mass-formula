import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereMass
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductLiteralDifferentialMeasure

/-!
# Normalize the literal lower differential/hemisphere product

This module applies the internally proved positive-hemisphere mass to the
literal lower differential/sphere product.  The unnormalized product is the
explicit sphere-step scalar times the product with probability-normalized
hemisphere measure.  No coupled-source restriction, fiber kernel, total-mass
cancellation, or rank recurrence is used here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductLiteralHemisphereGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleProductLiteralHemisphereGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- Literal lower differential Haar restricted to its identity chart, times
the probability-normalized positive-hemisphere coordinate measure. -/
def
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedHemisphereMeasure
    (n : ℕ) :
    Measure
      (identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ((identitySpecialOrthogonalDifferentialMeasure n).restrict
    (identitySpecialOrthogonalLiteralIdentityChartSource n)).prod
      (identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
        (n + 1))

/-- The literal lower differential/sphere product carries exactly the
positive-hemisphere sphere-step scalar. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereMeasure_eq_sphereStep_smul
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereMeasure
        n =
      identitySpecialOrthogonalSphereStep (n + 2) •
        identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedHemisphereMeasure
          n := by
  let ν :=
    identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
      (n + 1)
  letI : IsFiniteMeasure ν :=
    ⟨by
      change
        identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
            (n + 1) Set.univ <
          ⊤
      rw [
        identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure_univ]
      simp⟩
  rw [
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereMeasure,
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedHemisphereMeasure,
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_eq_sphereStep_smul_probability,
    Measure.prod_smul_right]

end PositiveDefiniteIntegralLattice
