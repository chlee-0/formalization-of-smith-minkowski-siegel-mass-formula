import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductGroupCoordinateReassociateMeasure

/-!
# Compare product-transition and group-product coordinates

This layer uses only the exact-source pointwise coordinate theorem to replace
the measurable transition after lower source coordinates by the higher chart
coordinate after the measurable group product.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductGroupCoordinateMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductGroupCoordinateMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductGroupCoordinateGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductGroupCoordinateGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- On the restricted lower differential/sphere product, the measurable
transition coordinate and the higher coordinate of the actual group product
have identical pushforwards. -/
theorem
    map_comp_identitySpecialOrthogonalNorthPoleProductMeasurableTransition_lowerSourceAmbient_eq_map_higherCoordinate_map_lowerGroup
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransitionOnLowerSource n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          n) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n)
        (Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n)
          (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
            n)) := by
  change
    Measure.map
        (fun p =>
          identitySpecialOrthogonalNorthPoleProductMeasurableTransition n
            (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
              n p))
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          n) =
      _
  calc
    _ = Measure.map
        (fun p =>
          identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
            n
            (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n p))
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          n) :=
      map_comp_identitySpecialOrthogonalNorthPoleProductMeasurableTransition_lowerSourceAmbient_eq_map_comp_higherCoordinate_lowerGroup
        n
    _ = _ :=
      map_comp_identitySpecialOrthogonalNorthPoleProductHigherCoordinate_lowerGroup_eq_map_higherCoordinate_map_lowerGroup
        n

end PositiveDefiniteIntegralLattice
