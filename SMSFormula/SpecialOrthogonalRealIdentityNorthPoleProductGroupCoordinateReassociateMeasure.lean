import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductGroupCoordinateCongrMeasure

/-!
# Reassociate the higher coordinate and actual group-product maps

This layer contains only the measurable `Measure.map_map` reassociation.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductGroupCoordinateReassociateMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductGroupCoordinateReassociateMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductGroupCoordinateReassociateGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductGroupCoordinateReassociateGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

theorem
    map_comp_identitySpecialOrthogonalNorthPoleProductHigherCoordinate_lowerGroup_eq_map_higherCoordinate_map_lowerGroup
    (n : ℕ) :
    Measure.map
        (fun p =>
          identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
            n
            (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n p))
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
        (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
            n ∘
          identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          n) =
      _
  rw [Measure.map_map
    (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
      n)
    (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
      n)]

end PositiveDefiniteIntegralLattice
