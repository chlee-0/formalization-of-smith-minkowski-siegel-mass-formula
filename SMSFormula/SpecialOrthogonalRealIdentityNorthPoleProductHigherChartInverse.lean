import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductHigherDifferentialCoordinateComparison

/-!
# Higher identity-chart inverse on the exact product set

The globally measurable higher chart coordinate is not injective off its
chart source. This module restricts it to the exact higher product group set,
where it agrees with the genuine identity-chart local homeomorphism, and
constructs a globally measurable extension of the inverse chart for
measure-map cancellation.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory Set

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductHigherChartInverseMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductHigherChartInverseMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductHigherChartInverseGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductHigherChartInverseGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

theorem
    continuousOn_identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
    (n : ℕ) :
    ContinuousOn
      (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
        n)
      (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n) := by
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  apply (I.continuousOn.mono inter_subset_right).congr
  intro q hq
  exact
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate_eq
      n q hq.2

theorem
    injOn_identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
    (n : ℕ) :
    Set.InjOn
      (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
        n)
      (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n) := by
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  intro q₁ hq₁ q₂ hq₂ hq
  rw [
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate_eq
      n q₁ hq₁.2,
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate_eq
      n q₂ hq₂.2] at hq
  exact I.injOn hq₁.2 hq₂.2 hq

/-- A globally measurable extension of the inverse higher identity-chart
coordinate. Its value off the chart target is irrelevant. -/
def identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse
    (n : ℕ)
    (y : identitySpecialOrthogonalMappedTangent (n + 1)) :
    specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
        (algebraMap ℚ ℝ)) :=
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  Function.extend
    (Subtype.val : I.target → identitySpecialOrthogonalMappedTangent (n + 1))
    (fun z => (I.toHomeomorphSourceTarget.symm z).1)
    (fun _ => 1) y

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse
        n) := by
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  exact
    (MeasurableEmbedding.subtype_coe I.open_target.measurableSet
      ).measurable_extend
        (continuous_subtype_val.measurable.comp
          I.toHomeomorphSourceTarget.symm.continuous.measurable)
        measurable_const

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse_eq
    (n : ℕ)
    (y : identitySpecialOrthogonalMappedTangent (n + 1))
    (hy :
      y ∈
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).target) :
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse
        n y =
      ((specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).toHomeomorphSourceTarget.symm
          ⟨y, hy⟩).1 := by
  rw [
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse]
  exact
    Function.Injective.extend_apply Subtype.val_injective _ _ ⟨y, hy⟩

/-- On the exact higher product group set, the measurable inverse is a left
inverse to the measurable higher chart coordinate. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse_comp_coordinate
    (n : ℕ)
    (q :
      specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ)))
    (hq :
      q ∈
        identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n) :
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse n
        (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n q) =
      q := by
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  rw [
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate_eq
      n q hq.2,
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartInverse_eq
      n (I q) (I.map_source hq.2)]
  exact congrArg Subtype.val
    (I.toHomeomorphSourceTarget.symm_apply_apply ⟨q, hq.2⟩)

end PositiveDefiniteIntegralLattice
