import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductGroupCoordinateMeasure
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductGroupSourceMapMeasure

/-!
# Group-product coordinate image of the weighted source

This final small layer composes three opaque measure equalities: raw-to-
measurable transition replacement, reassociation through the lower source
coordinate, and comparison with the higher chart coordinate of the actual
group product.

The higher target differential theorem, chart injectivity, fiber
identification, and rank recurrence remain unapplied.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductGroupMeasureFinalMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductGroupMeasureFinalMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductGroupMeasureFinalGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductGroupMeasureFinalGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Mapping the weighted coordinate source through the product transition is
the higher identity-chart coordinate image of the actual lower
differential/sphere group-product pushforward. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductTransition_sourceWithDensity_eq_map_higherCoordinate_map_lowerGroup
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransition n)
        (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n)
        (Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n)
          (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
            n)) := by
  calc
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransition n)
        (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableTransition n)
        (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) :=
      map_identitySpecialOrthogonalNorthPoleProductTransition_sourceWithDensity_eq_measurableTransition
        n
    _ = Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransitionOnLowerSource n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          n) :=
      map_identitySpecialOrthogonalNorthPoleProductMeasurableTransition_sourceWithDensity_eq_map_comp_lowerSourceAmbient
        n
    _ = Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n)
        (Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n)
          (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
            n)) :=
      map_comp_identitySpecialOrthogonalNorthPoleProductMeasurableTransition_lowerSourceAmbient_eq_map_higherCoordinate_map_lowerGroup
        n

end PositiveDefiniteIntegralLattice
