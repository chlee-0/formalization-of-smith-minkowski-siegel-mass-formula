import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductGroup

/-!
# Measurable product-transition replacement

This small layer replaces the raw identity north-pole product transition by
its measurable extension under the exact source-density-weighted coordinate
measure. No source-coordinate reassociation or group-product comparison is
performed here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductGroupTransitionMeasureMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductGroupTransitionMeasureBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

/-- Under the exact weighted source, the raw product transition and its
globally measurable extension have the same pushforward. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductTransition_sourceWithDensity_eq_measurableTransition
    (n : ℕ) :
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
            (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity
              n)) := by
  let S := identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n
  let μ :=
    (identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n).restrict S
  let W :=
    μ.withDensity
      (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)
  have heq :
      identitySpecialOrthogonalNorthPoleProductMeasurableTransition n =ᵐ[W]
        identitySpecialOrthogonalNorthPoleProductTransition n := by
    apply
      (withDensity_absolutelyContinuous μ
        (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)).ae_eq
    filter_upwards [
      MeasureTheory.ae_restrict_mem
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
          ).measurableSet] with x hx
    exact
      identitySpecialOrthogonalNorthPoleProductMeasurableTransition_eq n x hx
  exact Measure.map_congr heq.symm

end PositiveDefiniteIntegralLattice
