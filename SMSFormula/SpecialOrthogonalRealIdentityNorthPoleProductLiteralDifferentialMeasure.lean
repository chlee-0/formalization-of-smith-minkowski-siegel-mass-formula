import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductFiberParametrization
import SMSFormula.SpecialOrthogonalRealIdentityLowerDifferentialLiteral

/-!
# Literal lower differential product for the identity north-pole chart

This module transports the lower scalar-extended rational differential/sphere
product, including its coupled exact-source restriction, to the literal real
identity-form group. It then restates the verified local higher differential
comparison through the same last-column fiber parametrization on that literal
lower carrier.

The positive-hemisphere measure remains unnormalized. No global fiber kernel,
total-mass cancellation, rank recurrence, or Gamma value is asserted.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory Set

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductLiteralDifferentialMappedGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductLiteralDifferentialMappedGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance identityNorthPoleProductLiteralDifferentialGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleProductLiteralDifferentialGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- Apply the ambient-matrix-preserving mapped-to-literal equivalence to the
lower group factor, leaving the north-pole coordinate fixed. -/
def identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral
    (n : ℕ) :
    (specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
            (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
      (identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  Prod.map
    (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 1))
    id

/-- The inverse product transport, rebuilding the mapped lower group while
leaving the north-pole coordinate fixed. -/
def identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped
    (n : ℕ) :
    (identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
      (specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
            (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  Prod.map
    (identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 1))
    id

theorem continuous_identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n) :=
  (continuous_identitySpecialOrthogonalMappedIdentityGroupToLiteral
    (n + 1)).prodMap continuous_id

theorem continuous_identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped n) :=
  (continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped
    (n + 1)).prodMap continuous_id

theorem identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped_lowerProductToLiteral
    (n : ℕ) (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
            (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped n
        (identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n p) =
      p := by
  apply Prod.ext
  · exact
      identitySpecialOrthogonalMappedIdentityGroupToLiteral_leftInverse
        (n + 1) p.1
  · rfl

theorem identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral_literalProductToMapped
    (n : ℕ) (p :
      identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n
        (identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped
          n p) =
      p := by
  apply Prod.ext
  · exact
      identitySpecialOrthogonalMappedIdentityGroupToLiteral_rightInverse
        (n + 1) p.1
  · rfl

/-- Literal differential Haar restricted to the literal identity chart, times
the intrinsic positive-hemisphere coordinate sphere measure. -/
def identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereMeasure
    (n : ℕ) :
    Measure
      (identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ((identitySpecialOrthogonalDifferentialMeasure n).restrict
    (identitySpecialOrthogonalLiteralIdentityChartSource n)).prod
      (identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure (n + 1))

theorem map_identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure_toLiteral
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n)
        (identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure
          (n + 1)) =
      identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereMeasure n := by
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
  let ν :=
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure (n + 1)
  letI : SigmaFinite μ :=
    specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  letI : IsFiniteMeasure ν :=
    ⟨identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_lt_top
      (n + 1)⟩
  rw [
    identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure,
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereMeasure]
  change
    Measure.map
        (Prod.map
          (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 1))
          id)
        ((μ.restrict S).prod ν) =
      ((identitySpecialOrthogonalDifferentialMeasure n).restrict
        (identitySpecialOrthogonalLiteralIdentityChartSource n)).prod ν
  rw [← Measure.map_prod_map _ _
      (continuous_identitySpecialOrthogonalMappedIdentityGroupToLiteral
        (n + 1)).measurable
      measurable_id,
    map_restrict_identitySpecialOrthogonalMappedDifferentialMeasure_toLiteral,
    Measure.map_id]

/-- The coupled exact product source transported to the literal lower group
carrier. -/
def identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
    (n : ℕ) :
    Set
      (identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped n ⁻¹'
    identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
      (n + 1)

theorem measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
    (n : ℕ) :
    MeasurableSet
      (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
        n) :=
  (measurableSet_identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
    (n + 1)).preimage
      (continuous_identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped
        n).measurable

theorem identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral_preimage_literalSourceSet
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n ⁻¹'
        identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet n =
      identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        (n + 1) := by
  ext p
  simp only [
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet,
    Set.mem_preimage]
  rw [
    identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped_lowerProductToLiteral]

/-- The literal lower differential/sphere product restricted to the
transported coupled exact source. -/
def identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialSphereMeasure
    (n : ℕ) :
    Measure
      (identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereMeasure
    n).restrict
      (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
        n)

theorem map_identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure_toLiteral
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          (n + 1)) =
      identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialSphereMeasure
        n := by
  rw [
    identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure,
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialSphereMeasure]
  calc
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n)
        ((identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure
          (n + 1)).restrict
            (identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
              (n + 1))) =
      (Measure.map
        (identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n)
        (identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure
          (n + 1))).restrict
            (identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
              n) := by
      rw [Measure.restrict_map
        (f := identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n)
        (continuous_identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral
          n).measurable
        (measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
          n),
        identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral_preimage_literalSourceSet]
    _ = _ := by
      rw [map_identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure_toLiteral]

/-- The existing last-column fiber parametrization, now taking its lower group
argument directly on the literal carrier. -/
def identitySpecialOrthogonalNorthPoleProductLiteralCarrierFiberParametrization
    (n : ℕ)
    (p :
      identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    identitySpecialOrthogonalGroup (n + 1) :=
  identitySpecialOrthogonalLastColumnFiberParametrization n
    (identitySpecialOrthogonalNorthPoleSection (n + 1) p.2)
    p.1

/-- Return the literal-carrier fiber parametrization to the mapped higher group
used by the current local differential comparison. -/
def identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
    (n : ℕ)
    (p :
      identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ).map
        (algebraMap ℚ ℝ)) :=
  identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2)
    (identitySpecialOrthogonalNorthPoleProductLiteralCarrierFiberParametrization n p)

/-- The literal-carrier fiber parametrization after lower product transport is
exactly the literal fiber parametrization. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLiteralCarrierFiber_comp_lowerProductToLiteral
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductLiteralCarrierFiberParametrization
          n ∘
        identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n =
      identitySpecialOrthogonalNorthPoleProductLiteralFiberParametrization
        n :=
  rfl

theorem identitySpecialOrthogonalNorthPoleProductMappedFiberOnLiteral_comp_lowerProductToLiteral
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
          n ∘
        identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral n =
      identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization
        n :=
  rfl

theorem measurable_identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
        n) := by
  exact
    ((continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped
      (n + 2)).comp
      (((continuous_identitySpecialOrthogonalNorthPoleSection (n + 1)).comp
        continuous_snd).mul
        ((continuous_identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom
          n).comp continuous_fst))).measurable

theorem map_identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral_eq_smul
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
          n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialSphereMeasure
          n) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|)⁻¹ •
        (specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
              (n + 1)) := by
  rw [
    ←
      map_identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure_toLiteral]
  rw [Measure.map_map
    (measurable_identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
      n)
    (continuous_identitySpecialOrthogonalNorthPoleProductLowerProductToLiteral
      n).measurable]
  rw [
    identitySpecialOrthogonalNorthPoleProductMappedFiberOnLiteral_comp_lowerProductToLiteral]
  exact
    map_identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization_eq_smul_restrict_higherDifferential
      n

end PositiveDefiniteIntegralLattice
