import SMSFormula.SpecialOrthogonalRealIdentityLastColumnMeasure

/-!
# Lower identity differential Haar on the literal group

This module transports differential Haar restricted to the scalar-extended
rational identity chart into the literal real identity-form group.  The
transport uses the ambient-matrix-preserving continuous multiplicative
equivalence, so it keeps the rational tangent differential normalization
exactly.

No product measure, sphere measure, fiber parametrization, total mass, or
rank recurrence is used here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory Set

namespace PositiveDefiniteIntegralLattice

local instance identityLowerDifferentialLiteralMappedGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityLowerDifferentialLiteralMappedGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance identityLowerDifferentialLiteralGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityLowerDifferentialLiteralGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- The explicit ambient-matrix-preserving map is the forward map of the
continuous multiplicative equivalence used to define literal differential
Haar. -/
theorem
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_eq_mappedGroupContinuousEquiv
    (n : ℕ)
    (g :
      specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ))) :
    identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 1) g =
      identitySpecialOrthogonalMappedGroupContinuousEquiv n g :=
  rfl

/-- The literal image of the scalar-extended rational identity-chart
source. -/
def identitySpecialOrthogonalLiteralIdentityChartSource
    (n : ℕ) :
    Set (identitySpecialOrthogonalGroup n) :=
  identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 1) ⁻¹'
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).source

theorem identitySpecialOrthogonalLiteralIdentityChartSource_isOpen
    (n : ℕ) :
    IsOpen (identitySpecialOrthogonalLiteralIdentityChartSource n) :=
  (specialFormPreservingSmoothRealIdentityChart
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    identityRationalForm_isSymm
    identityRationalForm_det_ne_zero).open_source.preimage
      (continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped
        (n + 1))

theorem
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_preimage_literalIdentityChartSource
    (n : ℕ) :
    identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 1) ⁻¹'
        identitySpecialOrthogonalLiteralIdentityChartSource n =
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).source := by
  ext g
  simp only [
    identitySpecialOrthogonalLiteralIdentityChartSource,
    Set.mem_preimage]
  rw [identitySpecialOrthogonalMappedIdentityGroupToLiteral_leftInverse]

/-- Restricting mapped differential Haar to the identity chart and applying
the ambient-matrix-preserving equivalence gives literal differential Haar
restricted to the literal image of that chart. -/
theorem
    map_restrict_identitySpecialOrthogonalMappedDifferentialMeasure_toLiteral
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 1))
        ((specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (specialFormPreservingSmoothRealIdentityChart
              (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
              identityRationalForm_isSymm
              identityRationalForm_det_ne_zero).source) =
      (identitySpecialOrthogonalDifferentialMeasure n).restrict
        (identitySpecialOrthogonalLiteralIdentityChartSource n) := by
  let μ :=
    specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let S :=
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).source
  let T := identitySpecialOrthogonalLiteralIdentityChartSource n
  have hfun :
      identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 1) =
        (identitySpecialOrthogonalMappedGroupContinuousEquiv n :
          _ → _) := by
    funext g
    exact
      identitySpecialOrthogonalMappedIdentityGroupToLiteral_eq_mappedGroupContinuousEquiv
        n g
  have hpre :
      (identitySpecialOrthogonalMappedGroupContinuousEquiv n :
        _ → _) ⁻¹' T = S := by
    rw [← hfun]
    exact
      identitySpecialOrthogonalMappedIdentityGroupToLiteral_preimage_literalIdentityChartSource
        n
  calc
    Measure.map
        (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 1))
        (μ.restrict S) =
      Measure.map
        (identitySpecialOrthogonalMappedGroupContinuousEquiv n)
        (μ.restrict S) := by
      rw [hfun]
    _ = (Measure.map
          (identitySpecialOrthogonalMappedGroupContinuousEquiv n) μ
          ).restrict T := by
      rw [Measure.restrict_map
        (f := identitySpecialOrthogonalMappedGroupContinuousEquiv n)
        (identitySpecialOrthogonalMappedGroupContinuousEquiv n
          ).continuous.measurable
        (identitySpecialOrthogonalLiteralIdentityChartSource_isOpen n
          ).measurableSet,
        hpre]
    _ = (identitySpecialOrthogonalDifferentialMeasure n).restrict T := by
      rw [identitySpecialOrthogonalDifferentialMeasure]

end PositiveDefiniteIntegralLattice
