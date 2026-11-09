import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductGroupCoordinateRestrictedAE

/-!
# Push forward the product-group coordinate comparison

This layer applies only `Measure.map_congr` to the opaque almost-everywhere
coordinate identity.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductGroupCoordinateCongrMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductGroupCoordinateCongrMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductGroupCoordinateCongrGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductGroupCoordinateCongrGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

theorem
    map_comp_identitySpecialOrthogonalNorthPoleProductMeasurableTransition_lowerSourceAmbient_eq_map_comp_higherCoordinate_lowerGroup
    (n : ℕ) :
    Measure.map
        (fun p =>
          identitySpecialOrthogonalNorthPoleProductMeasurableTransition n
            (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
              n p))
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          n) =
      Measure.map
        (fun p =>
          identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
            n
            (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n p))
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          n) :=
  Measure.map_congr
    (identitySpecialOrthogonalNorthPoleProductMeasurableTransition_lowerSourceAmbient_ae_eq_higherCoordinate_lowerGroup
      n)

end PositiveDefiniteIntegralLattice
