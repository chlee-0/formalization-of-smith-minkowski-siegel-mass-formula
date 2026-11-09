import SMSFormula.SpecialOrthogonalRealIdentityChartDifferentialCoordinate

/-!
# Differential source product for the identity north-pole transition

This module takes the product of rank-`n` differential Haar restricted to the
identity-chart source with the intrinsic north-pole coordinate sphere measure.
The measurable lower chart coordinate maps this product to the intrinsic
source subtype product measure. After restricting by the preimage of the exact
higher-chart source, its ambient image is exactly the source-density-weighted
coordinate restriction used by the product transition.

The actual group-valued product map is not used here. No higher differential
comparison, fiber identification, or rank recurrence is asserted.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductSourceDifferentialMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductSourceDifferentialMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductSourceDifferentialGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductSourceDifferentialGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Rank-`n` differential Haar on the identity-chart source, times the
intrinsic positive-hemisphere measure in north-pole coordinates. -/
def identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure
    (n : ℕ) :
    Measure
      (specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  ((specialFormPreservingSmoothRealDifferentialMeasure
    (1 : Matrix (Fin n) (Fin n) ℚ)
    identityRationalForm_isSymm
    identityRationalForm_det_ne_zero).restrict
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).source).prod
    (identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n)

/-- Forward lower identity-chart coordinates on the first factor, retaining
the intrinsic north-pole coordinate on the second factor. -/
def identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate
    (n : ℕ) :
    (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) →
      ((specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).target ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  fun p =>
    (identitySpecialOrthogonalMeasurableIdentityChartCoordinate n p.1, p.2)

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate
        n) :=
  (measurable_identitySpecialOrthogonalMeasurableIdentityChartCoordinate n
    ).prodMap measurable_id

/-- Forgetting the target and ball subtype proofs after taking lower chart
coordinates gives the ambient product-transition source coordinate. -/
def identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
    (n : ℕ) :
    (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) →
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n) :=
  identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient n ∘
    identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate n

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
        n) :=
  (measurable_identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient
    n).comp
      (measurable_identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate
        n)

/-- The exact higher-chart transition source pulled back to the lower
differential/sphere product carrier. -/
def identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
    (n : ℕ) :
    Set
      (specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate n ⁻¹'
    identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n

theorem
    measurableSet_identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
    (n : ℕ) :
    MeasurableSet
      (identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n) :=
  (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
    ).measurableSet.preimage
      (measurable_identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
        n)

/-- The lower differential/sphere product maps to the intrinsic source
subtype product measure before imposing the coupled higher-chart source
restriction. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate
          n)
        (identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure
          n) =
      identitySpecialOrthogonalNorthPoleProductSourceSubtypeProductMeasure
        n := by
  let μ :=
    specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let ν := identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n
  let Φ := identitySpecialOrthogonalMeasurableIdentityChartCoordinate n
  letI : SigmaFinite μ :=
    specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  letI : IsFiniteMeasure ν :=
    ⟨identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_lt_top n⟩
  rw [
    identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure,
    identitySpecialOrthogonalNorthPoleProductSourceSubtypeProductMeasure]
  change
    Measure.map (Prod.map Φ id) ((μ.restrict I.source).prod ν) = _
  rw [← Measure.map_prod_map _ _
      (measurable_identitySpecialOrthogonalMeasurableIdentityChartCoordinate n)
      measurable_id,
    ←
      identitySpecialOrthogonalIdentityChartTargetDensityMeasure_eq_map_restrict_differential,
    Measure.map_id]

/-- The source-density-weighted exact coordinate restriction is the ambient
image of the lower differential/sphere product restricted by the pulled-back
exact higher-chart source. -/
theorem
    identitySpecialOrthogonalNorthPoleProductSourceWithDensity_eq_map_restrict_lowerDifferentialSphere
    (n : ℕ) :
    (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
        ).withDensity
          (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
          n)
        ((identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure
          n).restrict
            (identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
              n)) := by
  rw [
    identitySpecialOrthogonalNorthPoleProductSourceWithDensity_eq_restrict_map_subtype,
    ←
      map_identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate]
  rw [Measure.map_map
    (measurable_identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient
      n)
    (measurable_identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate
      n)]
  change
    (Measure.map
      (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate n)
      (identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure
        n)).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
          n)
        ((identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure
          n).restrict
            (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
              n ⁻¹'
                identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet
                  n))
  exact
    Measure.restrict_map
      (μ :=
        identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure
          n)
      (measurable_identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
        n)
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
        ).measurableSet

end PositiveDefiniteIntegralLattice
