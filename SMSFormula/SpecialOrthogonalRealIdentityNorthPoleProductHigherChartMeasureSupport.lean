import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductHigherChartInverse

/-!
# Exact higher-chart support for the two product measures

This module names the actual lower product-group measure and the scaled higher
differential measure, then proves that both are supported on the exact higher
identity-chart group set.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory Set

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductHigherChartSupportMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductHigherChartSupportMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductHigherChartSupportGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductHigherChartSupportGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The actual group-valued image of the restricted lower
differential/sphere product measure. -/
def identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure
    (n : ℕ) :
    Measure
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ))) :=
  Measure.map
    (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n)
    (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
      n)

/-- The restricted higher differential measure with the explicit reciprocal
fixed-basis transition scalar. -/
def identitySpecialOrthogonalNorthPoleProductScaledHigherDifferentialMeasure
    (n : ℕ) :
    Measure
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ))) :=
  (Real.toNNReal
    |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|
      )⁻¹ •
    (specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n)

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_mem_higherChartGroupSet
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hp :
      p ∈
        identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
          n) :
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n p ∈
      identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n := by
  rw [
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq n p hp]
  exact
    identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource_mem_higherChartGroupSet
      n ⟨p, hp⟩

theorem
    ae_identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure_mem_higherChartGroupSet
    (n : ℕ) :
    ∀ᵐ q ∂identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure n,
      q ∈ identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n := by
  rw [identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure]
  apply
    (ae_map_iff
      (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
        n).aemeasurable
      (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet_isOpen n
        ).measurableSet).2
  rw [
    identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure]
  exact
    (MeasureTheory.ae_restrict_mem
      (measurableSet_identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n)).mono
      (fun p hp =>
        identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_mem_higherChartGroupSet
          n p hp)

theorem
    restrict_identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure_higherChartGroupSet
    (n : ℕ) :
    (identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure n).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n) =
      identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure n :=
  Measure.restrict_eq_self_of_ae_mem
    (ae_identitySpecialOrthogonalNorthPoleProductLowerGroupMeasure_mem_higherChartGroupSet
      n)

theorem
    restrict_identitySpecialOrthogonalNorthPoleProductScaledHigherDifferentialMeasure_higherChartGroupSet
    (n : ℕ) :
    (identitySpecialOrthogonalNorthPoleProductScaledHigherDifferentialMeasure
      n).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n) =
      identitySpecialOrthogonalNorthPoleProductScaledHigherDifferentialMeasure
        n := by
  simp [
    identitySpecialOrthogonalNorthPoleProductScaledHigherDifferentialMeasure,
    Measure.restrict_restrict
      (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet_isOpen n
        ).measurableSet]

end PositiveDefiniteIntegralLattice
