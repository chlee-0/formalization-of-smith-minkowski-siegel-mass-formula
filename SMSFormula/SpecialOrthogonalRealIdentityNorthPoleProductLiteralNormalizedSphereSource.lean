import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductLiteralNormalizedSphere

/-!
# The coupled literal source on the normalized last-column sphere

This module transports the coupled exact product-source restriction from
north-pole ball coordinates to the ambient last-column sphere.  The
coordinate-to-sphere product map is kept as a measurable embedding, so its
image is measurable and its preimage of that image is exactly the original
coupled source.

The probability-hemisphere factor remains twice normalized full-sphere
measure restricted to the positive hemisphere.  No global fiber kernel,
total-mass cancellation, rank recurrence, or Gamma evaluation is used here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductLiteralNormalizedSphereSourceGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleProductLiteralNormalizedSphereSourceGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- The literal lower-group/ball map into the ambient last-column sphere is a
measurable embedding. -/
theorem
    measurableEmbedding_identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
    (n : ℕ) :
    MeasurableEmbedding
      (identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
        n) := by
  let hBall :
      MeasurableEmbedding
        (Subtype.val ∘
          (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
            (n + 1)).symm) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_identitySpecialOrthogonalNorthPoleHemisphere
        (n + 1))).comp
      (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
        (n + 1)).symm.measurableEmbedding
  exact MeasurableEmbedding.id.prodMap hBall

/-- The exact coupled source after returning the north-pole coordinate to the
ambient last-column sphere. -/
def
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
    (n : ℕ) :
    Set
      (identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere (n + 1)) :=
  identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
      n ''
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
      n

theorem
    measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
    (n : ℕ) :
    MeasurableSet
      (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
        n) := by
  exact
    (measurableEmbedding_identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
      n).measurableSet_image.2
        (measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
          n)

theorem
    identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere_preimage_sphereSourceSet
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
        n ⁻¹'
      identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
        n =
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
      n := by
  exact
    Set.preimage_image_eq _
      (measurableEmbedding_identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
        n).injective

/-- Returning the coupled normalized literal source to the ambient sphere
gives twice normalized full-sphere measure restricted to the corresponding
coupled positive-hemisphere source. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure_toSphere
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
          n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure
          n) =
      (2 : ℝ≥0∞) •
        (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
          n).restrict
            (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
              n) := by
  rw [
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedHemisphereMeasure]
  calc
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
          n)
        ((identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedHemisphereMeasure
          n).restrict
            (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
              n)) =
      (Measure.map
        (identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
          n)
        (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedHemisphereMeasure
          n)).restrict
            (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
              n) := by
      rw [
        Measure.restrict_map
          (f :=
            identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
              n)
          (measurableEmbedding_identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
            n).measurable
          (measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
            n),
        identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere_preimage_sphereSourceSet]
    _ =
      (2 : ℝ≥0∞) •
        (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
          n).restrict
            (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
              n) := by
      rw [
        map_identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere,
        Measure.restrict_smul]

end PositiveDefiniteIntegralLattice
