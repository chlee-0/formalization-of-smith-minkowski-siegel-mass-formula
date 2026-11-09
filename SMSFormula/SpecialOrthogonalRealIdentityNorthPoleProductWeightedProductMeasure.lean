import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductWeightedTargetTransport

/-!
# Weighted product-transition measure for the identity north-pole product

This module composes the two opaque measure equalities for the square
transition and the fixed product-to-higher tangent equivalence.  The raw
square transition is replaced by its globally measurable extension only under
the exact source-density-weighted measure.

The result is the target-chart measure equality for the original product
transition, with the reciprocal absolute rational-basis determinant.
No differential fiber comparison or rank recurrence is asserted.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductWeightedProductMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductWeightedProductBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

/-- Applying the fixed product-to-higher equivalence after the square
transition recovers the original product transition. -/
theorem
    identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv_squareMap
    (n : ℕ)
    (x : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
        (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n x) =
      identitySpecialOrthogonalNorthPoleProductTransition n x := by
  simp [
    identitySpecialOrthogonalNorthPoleProductTransitionSquareMap]

/-- The original product transition sends the exact source-density-weighted
product coordinate measure to the higher target-density-weighted coordinate
measure with the explicit reciprocal absolute transition determinant. -/
theorem
    map_withDensity_identitySpecialOrthogonalNorthPoleProductTransition_sourceDensity
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransition n)
        (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|
          )⁻¹ •
        (((identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity
              n)) := by
  let e :=
    identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
  let Ψ :=
    identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n
  let Ψm :=
    identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition n
  let μ :=
    (identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n).restrict
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
  let source :=
    identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n
  have hU :
      MeasurableSet
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :=
    (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
      ).measurableSet
  have hΨeq : Ψm =ᵐ[μ] Ψ := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    exact
      identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition_eq
        n x hx
  have hΨeq_source : Ψm =ᵐ[μ.withDensity source] Ψ :=
    (withDensity_absolutelyContinuous μ source).ae_eq hΨeq
  calc
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransition n)
        (μ.withDensity source) =
      Measure.map (fun x => e (Ψ x)) (μ.withDensity source) := by
        apply Measure.map_congr
        filter_upwards [] with x
        exact
          (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv_squareMap
            n x).symm
    _ = Measure.map (fun x => e (Ψm x)) (μ.withDensity source) := by
      apply Measure.map_congr
      filter_upwards [hΨeq_source] with x hx
      rw [hx]
    _ = Measure.map e (Measure.map Ψm (μ.withDensity source)) := by
      rw [Measure.map_map e.continuous.measurable
        (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition
          n)]
      rfl
    _ = Measure.map e (Measure.map Ψ (μ.withDensity source)) := by
      rw [Measure.map_congr hΨeq_source]
    _ = Measure.map e
        (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          ((identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
            ).symm ''
            identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity
              n)) := by
      rw [
        map_withDensity_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap_sourceDensity]
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
      map_withDensity_identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv_target
        n

end PositiveDefiniteIntegralLattice
