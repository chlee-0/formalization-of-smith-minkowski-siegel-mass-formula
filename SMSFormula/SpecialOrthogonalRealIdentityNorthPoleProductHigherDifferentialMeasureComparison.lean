import SMSFormula.MeasureMapAeLeftInverse
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductHigherChartMeasureSupport

/-!
# Restricted higher differential measure comparison

The two group measures already have equal images under the higher chart
coordinate up to the explicit reciprocal transition scalar. Both are
supported in the exact higher chart group set, where the measurable inverse
chart extension is a left inverse. The generic almost-everywhere left-inverse
cancellation lemma therefore removes the shared coordinate map.

No last-column fiber identification or rank recurrence is asserted.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory Set

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductHigherDifferentialComparisonMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductHigherDifferentialComparisonMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductHigherDifferentialComparisonGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductHigherDifferentialComparisonGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The actual lower differential/sphere group-product measure is the
explicit reciprocal transition-scalar multiple of the rank-`n+1`
differential measure restricted to the exact higher chart group set. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductLowerGroup_eq_smul_restrict_higherDifferential
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          n) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|
          )⁻¹ •
        (specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
              n) := by
  let S :=
    identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n
  let f :=
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate n
  let g :=
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse n
  let μ :=
    identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure n
  let ν :=
    identitySpecialOrthogonalNorthPoleProductScaledHigherDifferentialMeasure n
  have hS : MeasurableSet S :=
    (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet_isOpen n
      ).measurableSet
  have hμrestrict : μ.restrict S = μ :=
    restrict_identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure_higherChartGroupSet
      n
  have hνrestrict : ν.restrict S = ν :=
    restrict_identitySpecialOrthogonalNorthPoleProductScaledHigherDifferentialMeasure_higherChartGroupSet
      n
  have hμleft : g ∘ f =ᵐ[μ] id := by
    rw [← hμrestrict]
    refine (MeasureTheory.ae_restrict_mem hS).mono ?_
    intro q hq
    exact
      identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse_comp_coordinate
        n q hq
  have hνleft : g ∘ f =ᵐ[ν] id := by
    rw [← hνrestrict]
    refine (MeasureTheory.ae_restrict_mem hS).mono ?_
    intro q hq
    exact
      identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse_comp_coordinate
        n q hq
  have hmap : Measure.map f μ = Measure.map f ν := by
    change
      Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
            n)
          (identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure n) =
        Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
            n)
          (identitySpecialOrthogonalNorthPoleProductScaledHigherDifferentialMeasure
            n)
    rw [
      identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure,
      identitySpecialOrthogonalNorthPoleProductScaledHigherDifferentialMeasure,
      Measure.map_smul]
    exact
      map_higherCoordinate_map_identitySpecialOrthogonalNorthPoleProductLowerGroup_eq_smul_map_restrict_higherDifferential
        n
  have hμν : μ = ν :=
    Measure.eq_of_map_eq_of_ae_leftInverse
      (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
        n)
      (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse
        n)
      hμleft hνleft hmap
  change
    identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure n =
      identitySpecialOrthogonalNorthPoleProductScaledHigherDifferentialMeasure n
  exact hμν

end PositiveDefiniteIntegralLattice
