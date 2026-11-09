import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductSourceProductMeasure

/-!
# Differential Haar in global identity-chart coordinates

This module extends the forward rank-`n` identity chart measurably to the
whole scalar-extended rational identity-form group. Restricting invariant
differential Haar to the exact identity-chart source and applying this
extension recovers the intrinsic chart target-density measure.

The coupled north-pole product-source restriction is not used here. No fiber
identification or rank recurrence is asserted.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityChartDifferentialCoordinateMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityChartDifferentialCoordinateMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityChartDifferentialCoordinateGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityChartDifferentialCoordinateGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- A globally measurable extension of the forward rank-`n` identity chart.
Its value off the exact chart source is the zero target point and is
irrelevant after restriction to that source. -/
def identitySpecialOrthogonalMeasurableIdentityChartCoordinate
    (n : ℕ)
    (q :
      specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).target :=
  Function.extend
    (Subtype.val :
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).source →
      specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)))
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).toHomeomorphSourceTarget
    (fun _ =>
      ⟨0,
        zero_mem_specialFormPreservingSmoothRealIdentityChart_target
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero⟩)
    q

theorem measurable_identitySpecialOrthogonalMeasurableIdentityChartCoordinate
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalMeasurableIdentityChartCoordinate n) := by
  exact
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).open_source.measurableSet
      ).measurable_extend
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero
          ).toHomeomorphSourceTarget.continuous.measurable
        measurable_const

theorem identitySpecialOrthogonalMeasurableIdentityChartCoordinate_eq
    (n : ℕ)
    (q :
      specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)))
    (hq :
      q ∈
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).source) :
    identitySpecialOrthogonalMeasurableIdentityChartCoordinate n q =
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).toHomeomorphSourceTarget
          ⟨q, hq⟩ := by
  exact
    Function.Injective.extend_apply Subtype.val_injective _ _
      ⟨q, hq⟩

/-- The intrinsic rank-`n` identity-chart target-density measure is exactly
the globally measurable forward chart image of invariant differential Haar
restricted to the exact identity-chart source. -/
theorem
    identitySpecialOrthogonalIdentityChartTargetDensityMeasure_eq_map_restrict_differential
    (n : ℕ) :
    specialFormPreservingSmoothRealChartTargetDensityMeasure
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero 1 =
      Measure.map
        (identitySpecialOrthogonalMeasurableIdentityChartCoordinate n)
        ((specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (specialFormPreservingSmoothRealIdentityChart
              (1 : Matrix (Fin n) (Fin n) ℚ)
              identityRationalForm_isSymm
              identityRationalForm_det_ne_zero).source) := by
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let Φ := identitySpecialOrthogonalMeasurableIdentityChartCoordinate n
  let σ :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero 1
  let τ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero 1
  symm
  rw [restrict_specialFormPreservingSmoothRealDifferentialMeasure_source]
  change Measure.map Φ (Measure.map Subtype.val σ) = τ
  calc
    Measure.map Φ (Measure.map Subtype.val σ) =
        Measure.map (Φ ∘ Subtype.val) σ := by
      rw [Measure.map_map
        (measurable_identitySpecialOrthogonalMeasurableIdentityChartCoordinate
          n)
        continuous_subtype_val.measurable]
    _ = Measure.map I.toHomeomorphSourceTarget σ := by
      apply Measure.map_congr
      filter_upwards [] with x
      exact identitySpecialOrthogonalMeasurableIdentityChartCoordinate_eq
        n x.1 x.2
    _ = τ := by
      rw [map_specialFormPreservingSmoothRealChartSourceDensityMeasure]

end PositiveDefiniteIntegralLattice
