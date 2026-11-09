import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductGroupTransitionMeasure

/-!
# Reassociate the measurable transition with the differential source map

This layer uses the opaque coupled source-restriction bridge and
`Measure.map_map` to move the measurable product transition onto the lower
differential/sphere carrier. No group-coordinate comparison is performed.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductGroupSourceMapMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductGroupSourceMapMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductGroupSourceMapGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductGroupSourceMapGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The measurable transition of the weighted source is the image of the
restricted lower differential/sphere product under transition after ambient
source coordinates. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductMeasurableTransition_sourceWithDensity_eq_map_comp_lowerSourceAmbient
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableTransition n)
        (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransitionOnLowerSource n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          n) := by
  rw [
    identitySpecialOrthogonalNorthPoleProductTransitionOnLowerSource,
    identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure]
  rw [
    identitySpecialOrthogonalNorthPoleProductSourceWithDensity_eq_map_restrict_lowerDifferentialSphere,
    Measure.map_map
      (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableTransition
        n)
      (measurable_identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
        n)]

end PositiveDefiniteIntegralLattice
