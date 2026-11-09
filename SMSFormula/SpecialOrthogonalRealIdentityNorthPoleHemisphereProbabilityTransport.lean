import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereMass

/-!
# Transport the normalized north-pole hemisphere probability to the sphere

The positive-hemisphere coordinate probability measure is exactly twice the
restriction of the already normalized full-sphere measure, since that
restriction has mass one half.  This module proves the equality first in ball
coordinates, then on the positive-hemisphere subtype, and finally after
inclusion into the full sphere.

No group product, fiber kernel, total-mass cancellation, or rank recurrence is
used here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

/-- The probability normalization of the positive hemisphere is twice the
coordinate restriction of normalized full-sphere measure. -/
theorem
    identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure_eq_two_smul_normalized
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure n =
      (2 : ℝ≥0∞) •
        identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure
          n := by
  rw [
    identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure,
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_eq_smul,
    euclideanVolumeToSphere_univ_eq_two_mul_identitySpecialOrthogonalSphereStep
      (n + 1) (by omega),
    smul_smul]
  have hscalar :
      (2 : ℝ≥0∞) *
          (2 * identitySpecialOrthogonalSphereStep (n + 1))⁻¹ =
        (identitySpecialOrthogonalSphereStep (n + 1))⁻¹ := by
    rw [ENNReal.mul_inv]
    · rw [← mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
        one_mul]
    · exact Or.inl (by norm_num)
    · exact Or.inl (by norm_num)
  rw [hscalar]

/-- Mapping the normalized coordinate restriction back through the north-pole
chart recovers normalized sphere measure on the hemisphere subtype. -/
theorem
    map_identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_symm
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).symm
        (identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure n) =
      identitySpecialOrthogonalNorthPoleHemisphereNormalizedSphereMeasure n := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure]
  exact MeasurableEquiv.map_map_symm
    (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
      n).symm.toMeasurableEquiv

/-- On the hemisphere subtype, the coordinate probability is twice the
restriction of normalized full-sphere measure. -/
theorem
    map_identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure_symm
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).symm
        (identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
          n) =
      (2 : ℝ≥0∞) •
        identitySpecialOrthogonalNorthPoleHemisphereNormalizedSphereMeasure
          n := by
  rw [
    identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure_eq_two_smul_normalized,
    Measure.map_smul,
    map_identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_symm]

/-- After forgetting the hemisphere proof, the coordinate probability is
twice normalized full-sphere measure restricted to the positive hemisphere. -/
theorem
    map_identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure_ambient
    (n : ℕ) :
    Measure.map
        (Subtype.val ∘
          (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).symm)
        (identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
          n) =
      (2 : ℝ≥0∞) •
        (identitySpecialOrthogonalNormalizedSphereMeasure n).restrict
          (identitySpecialOrthogonalNorthPoleHemisphere n) := by
  calc
    Measure.map
        (Subtype.val ∘
          (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).symm)
        (identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
          n) =
        Measure.map Subtype.val
          (Measure.map
            (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).symm
            (identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
              n)) := by
      rw [Measure.map_map
        continuous_subtype_val.measurable
        (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
          n).symm.measurable]
    _ = Measure.map Subtype.val
          ((2 : ℝ≥0∞) •
            identitySpecialOrthogonalNorthPoleHemisphereNormalizedSphereMeasure
              n) := by
      rw [
        map_identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure_symm]
    _ = (2 : ℝ≥0∞) •
          Measure.map Subtype.val
            (identitySpecialOrthogonalNorthPoleHemisphereNormalizedSphereMeasure
              n) := by
      rw [Measure.map_smul]
    _ = (2 : ℝ≥0∞) •
          (identitySpecialOrthogonalNormalizedSphereMeasure n).restrict
            (identitySpecialOrthogonalNorthPoleHemisphere n) := by
      rw [
        identitySpecialOrthogonalNorthPoleHemisphereNormalizedSphereMeasure,
        map_comap_subtype_coe
          (measurableSet_identitySpecialOrthogonalNorthPoleHemisphere n)]

end PositiveDefiniteIntegralLattice
