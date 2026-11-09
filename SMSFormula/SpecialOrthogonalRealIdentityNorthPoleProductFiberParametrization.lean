import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductHigherDifferentialMeasureComparison
import SMSFormula.SpecialOrthogonalRealIdentityFiberProbability

/-!
# Local identity north-pole product as a last-column fiber parametrization

The actual group product is already compared locally with rank-`n+2`
differential Haar. This module identifies that product, on the support of its
rank-`n+1` differential/sphere source, with the existing last-column fiber
parametrization. It also records its last column.

The lower-chart membership needed for pointwise recovery is supplied almost
everywhere by the already restricted first-factor differential measure. No
global fiber kernel, sphere normalization, total-mass cancellation, rank
recurrence, or Gamma value is asserted.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductFiberParametrizationMappedGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductFiberParametrizationMappedGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance identityNorthPoleProductFiberParametrizationLiteralGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleProductFiberParametrizationLiteralGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

theorem
    identitySpecialOrthogonalLowerChartRankGroup_measurableIdentityChartCoordinate
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
    identitySpecialOrthogonalLowerChartRankGroup n
        (identitySpecialOrthogonalMeasurableIdentityChartCoordinate n q) =
      identitySpecialOrthogonalMappedIdentityGroupToLiteral n q := by
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  have hcoord :=
    identitySpecialOrthogonalMeasurableIdentityChartCoordinate_eq n q hq
  have hinv :
      I.toHomeomorphSourceTarget.symm
          (I.toHomeomorphSourceTarget ⟨q, hq⟩) =
        ⟨q, hq⟩ :=
    I.toHomeomorphSourceTarget.symm_apply_apply ⟨q, hq⟩
  have hgroup :
    (identitySpecialOrthogonalLowerChartGroup n
      (identitySpecialOrthogonalMeasurableIdentityChartCoordinate n q)
      ) = q := by
    rw [identitySpecialOrthogonalLowerChartGroup, hcoord]
    exact congrArg Subtype.val hinv
  rw [identitySpecialOrthogonalLowerChartRankGroup, hgroup]

/-- The existing literal last-column fiber parametrization, with its
representative given by the north-pole section and its lower argument obtained
from the scalar-extended rational identity group. -/
def identitySpecialOrthogonalNorthPoleProductLiteralFiberParametrization
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
            (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    identitySpecialOrthogonalGroup (n + 1) :=
  identitySpecialOrthogonalLastColumnFiberParametrization n
    (identitySpecialOrthogonalNorthPoleSection (n + 1) p.2)
    (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 1) p.1)

theorem
    continuous_identitySpecialOrthogonalNorthPoleProductLiteralFiberParametrization
    (n : ℕ) :
    Continuous
      (identitySpecialOrthogonalNorthPoleProductLiteralFiberParametrization
        n) := by
  exact
    ((continuous_identitySpecialOrthogonalNorthPoleSection (n + 1)).comp
      continuous_snd).mul
      ((continuous_identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom n
        ).comp
        ((continuous_identitySpecialOrthogonalMappedIdentityGroupToLiteral
          (n + 1)).comp continuous_fst))

/-- The literal fiber parametrization returned to the scalar-extended
rational identity group used by the differential measure. -/
def identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
            (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ).map
        (algebraMap ℚ ℝ)) :=
  identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2)
    (identitySpecialOrthogonalNorthPoleProductLiteralFiberParametrization n p)

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization
        n) :=
  ((continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped
      (n + 2)).comp
    (continuous_identitySpecialOrthogonalNorthPoleProductLiteralFiberParametrization
      n)).measurable

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq_mappedFiberParametrization
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
            (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hp :
      p ∈
        identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
          (n + 1))
    (hp₁ :
      p.1 ∈
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).source) :
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
        (n + 1) p =
      identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization
        n p := by
  rw [
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq
      (n + 1) p hp]
  rw [
    identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource,
    identitySpecialOrthogonalNorthPoleProductMappedGroup,
    identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization]
  apply congrArg
    (identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2))
  rw [
    identitySpecialOrthogonalNorthPoleProduct,
    identitySpecialOrthogonalNorthPoleProductLiteralFiberParametrization,
    identitySpecialOrthogonalLastColumnFiberParametrization,
    identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom_apply]
  simp only [
    identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource,
    identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate,
    identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate,
    identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient,
    Function.comp_apply, Subtype.coe_eta]
  rw [
    identitySpecialOrthogonalLowerChartRankGroup_measurableIdentityChartCoordinate
      (n + 1) p.1 hp₁]

theorem
    identitySpecialOrthogonalNorthPoleProductMappedToLiteral_measurableLowerGroup_eq_fiberParametrization
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
            (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hp :
      p ∈
        identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
          (n + 1))
    (hp₁ :
      p.1 ∈
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).source) :
    identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 2)
        (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
          (n + 1) p) =
      identitySpecialOrthogonalNorthPoleProductLiteralFiberParametrization
        n p := by
  rw [
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq_mappedFiberParametrization
      n p hp hp₁,
    identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization,
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_rightInverse]

theorem
    identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization_lastColumn
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
            (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    identitySpecialOrthogonalLastColumn (n + 1)
        (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 2)
          (identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization
            n p)) =
      identitySpecialOrthogonalNorthPoleInverse (n + 1) p.2 := by
  rw [identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization,
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_rightInverse]
  rw [identitySpecialOrthogonalNorthPoleProductLiteralFiberParametrization,
    identitySpecialOrthogonalLastColumnFiberParametrization]
  exact
    identitySpecialOrthogonalLastColumn_mul_of_mem_stabilizer
      (n + 1)
      (identitySpecialOrthogonalNorthPoleSection (n + 1) p.2)
      (identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1)
        (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 1) p.1))
      ((mem_identitySpecialOrthogonalLastColumnStabilizerSubgroup_iff
        (n + 1)
        (identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1)
          (identitySpecialOrthogonalMappedIdentityGroupToLiteral
            (n + 1) p.1))).mpr
        (identitySpecialOrthogonalLastColumnFiberEmbedGroup_mem
          (n + 1)
          (identitySpecialOrthogonalMappedIdentityGroupToLiteral
            (n + 1) p.1))) |>.trans
        (identitySpecialOrthogonalLastColumn_northPoleSection (n + 1) p.2)

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_lastColumn
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
            (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hp :
      p ∈
        identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
          (n + 1))
    (hp₁ :
      p.1 ∈
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).source) :
    identitySpecialOrthogonalLastColumn (n + 1)
        (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 2)
          (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
            (n + 1) p)) =
      identitySpecialOrthogonalNorthPoleInverse (n + 1) p.2 := by
  rw [
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq_mappedFiberParametrization
      n p hp hp₁]
  exact
    identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization_lastColumn
      n p

theorem
    ae_identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure_fst_mem_identityChartSource
    (n : ℕ) :
    ∀ᵐ p
        ∂identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          (n + 1),
      p.1 ∈
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).source := by
  let μ :=
    specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let ν :=
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure (n + 1)
  let S :=
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).source
  letI : SigmaFinite μ :=
    specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  letI : IsFiniteMeasure ν :=
    ⟨identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_lt_top
      (n + 1)⟩
  apply ae_restrict_of_ae
  change ∀ᵐ p ∂(μ.restrict S).prod ν, p.1 ∈ S
  have hν : ν.restrict Set.univ = ν := Measure.restrict_univ
  rw [← hν, Measure.prod_restrict]
  exact
    (ae_restrict_mem
      ((specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).open_source.measurableSet.prod
          MeasurableSet.univ)).mono
      (fun p hp => hp.1)

theorem
    ae_identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq_mappedFiberParametrization
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup (n + 1) =ᵐ[
      identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
        (n + 1)]
      identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization
        n := by
  have hsource :
      ∀ᵐ p
          ∂identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
            (n + 1),
        p ∈
          identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
            (n + 1) := by
    rw [
      identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure]
    exact
      ae_restrict_mem
        (measurableSet_identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
          (n + 1))
  filter_upwards [
    hsource,
    ae_identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure_fst_mem_identityChartSource
      n] with p hp hp₁
  exact
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq_mappedFiberParametrization
      n p hp hp₁

theorem
    ae_identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_lastColumn
    (n : ℕ) :
    (fun p =>
      identitySpecialOrthogonalLastColumn (n + 1)
        (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 2)
          (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
            (n + 1) p))) =ᵐ[
      identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
        (n + 1)]
      (fun p => identitySpecialOrthogonalNorthPoleInverse (n + 1) p.2) := by
  filter_upwards [
    ae_identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq_mappedFiberParametrization
      n] with p hp
  rw [hp]
  exact
    identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization_lastColumn
      n p

theorem
    ae_identitySpecialOrthogonalNorthPoleProductMappedToLiteral_measurableLowerGroup_eq_literalFiberParametrization
    (n : ℕ) :
    (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 2)) ∘
        (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
          (n + 1)) =ᵐ[
      identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
        (n + 1)]
      identitySpecialOrthogonalNorthPoleProductLiteralFiberParametrization
        n := by
  filter_upwards [
    ae_identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq_mappedFiberParametrization
      n] with p hp
  rw [Function.comp_apply, hp,
    identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization,
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_rightInverse]

theorem
    map_identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization_eq_smul_restrict_higherDifferential
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization
          n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          (n + 1)) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|)⁻¹ •
        (specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
              (n + 1)) := by
  calc
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductMappedFiberParametrization
          n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          (n + 1)) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
          (n + 1))
        (identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          (n + 1)) :=
      (Measure.map_congr
        (ae_identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq_mappedFiberParametrization
          n)).symm
    _ = _ :=
      map_identitySpecialOrthogonalNorthPoleProductLowerGroup_eq_smul_restrict_higherDifferential
        (n + 1)

end PositiveDefiniteIntegralLattice
