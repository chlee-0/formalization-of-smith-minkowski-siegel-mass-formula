import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductGroupMeasure

/-!
# Higher-coordinate comparison with differential Haar

This module composes only the opaque weighted product-transition equality,
the actual product-group coordinate equality, and the higher-target
differential bridge. It deliberately remains after applying the measurable
higher identity-chart coordinate: no chart injectivity, group-measure
equality, fiber identification, or rank recurrence is asserted.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductHigherDifferentialCoordinateMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductHigherDifferentialCoordinateMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductHigherDifferentialCoordinateGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductHigherDifferentialCoordinateGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The actual lower differential/sphere group product and the restricted
higher differential measure have proportional images under the same
measurable higher identity-chart coordinate. -/
theorem
    map_higherCoordinate_map_identitySpecialOrthogonalNorthPoleProductLowerGroup_eq_smul_map_restrict_higherDifferential
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n)
        (Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n)
          (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
            n)) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|
          )⁻¹ •
        Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
            n)
          ((specialFormPreservingSmoothRealDifferentialMeasure
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
            identityRationalForm_isSymm
            identityRationalForm_det_ne_zero).restrict
              (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
                n)) := by
  calc
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n)
        (Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n)
          (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
            n)) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransition n)
        (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) := by
      symm
      exact
        map_identitySpecialOrthogonalNorthPoleProductTransition_sourceWithDensity_eq_map_higherCoordinate_map_lowerGroup
          n
    _ =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|
          )⁻¹ •
        (((identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity
              n)) :=
      map_withDensity_identitySpecialOrthogonalNorthPoleProductTransition_sourceDensity
        n
    _ =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|
          )⁻¹ •
        Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
            n)
          ((specialFormPreservingSmoothRealDifferentialMeasure
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
            identityRationalForm_isSymm
            identityRationalForm_det_ne_zero).restrict
              (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
                n)) := by
      rw [
        identitySpecialOrthogonalNorthPoleProductHigherTargetWeightedMeasure_eq_map_restrict_differential]

end PositiveDefiniteIntegralLattice
