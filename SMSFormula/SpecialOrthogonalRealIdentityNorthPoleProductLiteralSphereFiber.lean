import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductLiteralNormalizedSphereSource

/-!
# The literal identity north-pole fiber map on the ambient sphere

This module defines the north-pole fiber parametrization from ball
coordinates to the positive last-column hemisphere.  The geometric map is
defined continuously on the positive-hemisphere product and measurably
extended to the whole ambient sphere product.  Its value off the hemisphere
is irrelevant.

The extension composed with the ball-to-sphere product map is exactly
the carrier fiber parametrization.  No measure pushforward,
global fiber kernel, total-mass cancellation, rank recurrence, or Gamma
evaluation is used here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductLiteralSphereFiberGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleProductLiteralSphereFiberGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductLiteralSphereFiberMappedGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductLiteralSphereFiberMappedGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Include the literal lower group times the positive-hemisphere subtype into
the literal lower group times the ambient last-column sphere. -/
def
    identitySpecialOrthogonalNorthPoleProductLiteralLowerHemisphereInclusion
    (n : ℕ) :
    (identitySpecialOrthogonalGroup n ×
        (identitySpecialOrthogonalNorthPoleHemisphere (n + 1) :
          Set (identitySpecialOrthogonalLastColumnSphere (n + 1)))) →
      (identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere (n + 1)) :=
  Prod.map id Subtype.val

theorem
    measurableEmbedding_identitySpecialOrthogonalNorthPoleProductLiteralLowerHemisphereInclusion
    (n : ℕ) :
    MeasurableEmbedding
      (identitySpecialOrthogonalNorthPoleProductLiteralLowerHemisphereInclusion
        n) := by
  exact
    MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe
        (measurableSet_identitySpecialOrthogonalNorthPoleHemisphere
          (n + 1)))

/-- On the positive hemisphere, use the north-pole section at the recovered
ball coordinate as representative and the literal lower group as fiber
argument. -/
def
    identitySpecialOrthogonalNorthPoleProductLiteralHemisphereFiberParametrization
    (n : ℕ)
    (p :
      identitySpecialOrthogonalGroup n ×
        (identitySpecialOrthogonalNorthPoleHemisphere (n + 1) :
          Set (identitySpecialOrthogonalLastColumnSphere (n + 1)))) :
    identitySpecialOrthogonalGroup (n + 1) :=
  identitySpecialOrthogonalLastColumnFiberParametrization n
    (identitySpecialOrthogonalNorthPoleSection (n + 1)
      (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
        (n + 1) p.2))
    p.1

theorem
    continuous_identitySpecialOrthogonalNorthPoleProductLiteralHemisphereFiberParametrization
    (n : ℕ) :
    Continuous
      (identitySpecialOrthogonalNorthPoleProductLiteralHemisphereFiberParametrization
        n) := by
  exact
    ((continuous_identitySpecialOrthogonalNorthPoleSection (n + 1)).comp
      ((identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
        (n + 1)).continuous.comp continuous_snd)).mul
      ((continuous_identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom
        n).comp continuous_fst)

/-- A globally measurable extension of the literal sphere-side fiber map. Its
value outside the positive hemisphere is irrelevant. -/
def
    identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
    (n : ℕ)
    (p :
      identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere (n + 1)) :
    identitySpecialOrthogonalGroup (n + 1) :=
  Function.extend
    (identitySpecialOrthogonalNorthPoleProductLiteralLowerHemisphereInclusion
      n)
    (identitySpecialOrthogonalNorthPoleProductLiteralHemisphereFiberParametrization
      n)
    (fun _ => 1)
    p

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
        n) := by
  exact
    (measurableEmbedding_identitySpecialOrthogonalNorthPoleProductLiteralLowerHemisphereInclusion
      n).measurable_extend
        (continuous_identitySpecialOrthogonalNorthPoleProductLiteralHemisphereFiberParametrization
          n).measurable
        measurable_const

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization_eq_hemisphere
    (n : ℕ)
    (p :
      identitySpecialOrthogonalGroup n ×
        (identitySpecialOrthogonalNorthPoleHemisphere (n + 1) :
          Set (identitySpecialOrthogonalLastColumnSphere (n + 1)))) :
    identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
        n
        (identitySpecialOrthogonalNorthPoleProductLiteralLowerHemisphereInclusion
          n p) =
      identitySpecialOrthogonalNorthPoleProductLiteralHemisphereFiberParametrization
        n p := by
  exact
    Function.Injective.extend_apply
      (measurableEmbedding_identitySpecialOrthogonalNorthPoleProductLiteralLowerHemisphereInclusion
        n).injective _ _ p

/-- Every point of the exact sphere-side coupled source lies in the positive
hemisphere in its last-column component. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet_snd_mem_hemisphere
    (n : ℕ)
    (p :
      identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere (n + 1))
    (hp :
      p ∈
        identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
          n) :
    p.2 ∈
      identitySpecialOrthogonalNorthPoleHemisphere (n + 1) := by
  rcases hp with ⟨q, _hq, rfl⟩
  exact
    ((identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
      (n + 1)).symm q.2).property

/-- On the exact sphere-side source, the measurable extension has the
geometric north-pole-section formula. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization_eq_on_source
    (n : ℕ)
    (p :
      identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere (n + 1))
    (hp :
      p ∈
        identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
          n) :
    identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
        n p =
      identitySpecialOrthogonalLastColumnFiberParametrization n
        (identitySpecialOrthogonalNorthPoleSection (n + 1)
          (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
            (n + 1)
            ⟨p.2,
              identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet_snd_mem_hemisphere
                n p hp⟩))
        p.1 := by
  let q :
      identitySpecialOrthogonalGroup n ×
        (identitySpecialOrthogonalNorthPoleHemisphere (n + 1) :
          Set (identitySpecialOrthogonalLastColumnSphere (n + 1))) :=
    ⟨p.1,
      ⟨p.2,
        identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet_snd_mem_hemisphere
          n p hp⟩⟩
  have hq :=
    identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization_eq_hemisphere
      n q
  simpa [
    q,
    identitySpecialOrthogonalNorthPoleProductLiteralLowerHemisphereInclusion,
    identitySpecialOrthogonalNorthPoleProductLiteralHemisphereFiberParametrization]
    using hq

/-- Returning a ball-coordinate point to the sphere and applying the
measurable sphere-side fiber map recovers the existing literal carrier fiber
parametrization. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiber_comp_productToSphere
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
          n ∘
        identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
          n =
      identitySpecialOrthogonalNorthPoleProductLiteralCarrierFiberParametrization
        n := by
  funext p
  let q :
      identitySpecialOrthogonalGroup n ×
        (identitySpecialOrthogonalNorthPoleHemisphere (n + 1) :
          Set (identitySpecialOrthogonalLastColumnSphere (n + 1))) :=
    ⟨p.1,
      (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
        (n + 1)).symm p.2⟩
  have hq :=
    identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization_eq_hemisphere
      n q
  simpa [
    q,
    Function.comp_apply,
    identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere,
    identitySpecialOrthogonalNorthPoleProductLiteralLowerHemisphereInclusion,
    identitySpecialOrthogonalNorthPoleProductLiteralHemisphereFiberParametrization,
    identitySpecialOrthogonalNorthPoleProductLiteralCarrierFiberParametrization]
    using hq

/-- Return the measurable literal sphere-side fiber map to the scalar-extended
rational higher group used by the local differential comparison. -/
def
    identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
    (n : ℕ)
    (p :
      identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere (n + 1)) :
    specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ).map
        (algebraMap ℚ ℝ)) :=
  identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2)
    (identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
      n p)

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
        n) :=
  (continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped
    (n + 2)).measurable.comp
      (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
        n)

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiber_comp_productToSphere
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
          n ∘
        identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
          n =
      identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
        n := by
  funext p
  change
    identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2)
        (identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
          n
          (identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
            n p)) =
      identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2)
        (identitySpecialOrthogonalNorthPoleProductLiteralCarrierFiberParametrization
          n p)
  exact
    congrArg (identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2))
      (congrFun
        (identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiber_comp_productToSphere
          n) p)

end PositiveDefiniteIntegralLattice
