import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereCoupledProduct

/-!
# The higher-chart target as a hemisphere-fiber preimage

This module expresses the mapped higher-chart target in the identity
group.  On the positive hemisphere, the sphere-first joint fiber lands in
this target exactly when its recovered lower group/ball coordinate belongs to
the coupled product source.  The lower identity-chart condition is kept
explicit.

Only setwise and restricted almost-everywhere statements are proved here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleHemisphereTargetPreimageGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleHemisphereTargetPreimageGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- The exact higher product-chart target on the literal identity group. -/
def
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
    (n : ℕ) :
    Set (identitySpecialOrthogonalGroup (n + 1)) :=
  identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2) ⁻¹'
    identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet (n + 1)

theorem
    isOpen_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
    (n : ℕ) :
    IsOpen
      (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
        n) :=
  (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet_isOpen
    (n + 1)).preimage
      (continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped
        (n + 2))

theorem
    measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
    (n : ℕ) :
    MeasurableSet
      (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
        n) :=
  (isOpen_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
    n).measurableSet

/-- On the lower literal identity chart, the literal carrier fiber is exactly
the mapped product associated with its lower identity-chart coordinate and
north-pole ball coordinate. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMappedFiberOnLiteral_eq_mappedGroup
    (n : ℕ)
    (p :
      identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hp₁ :
      p.1 ∈ identitySpecialOrthogonalLiteralIdentityChartSource n) :
    let q :=
      identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped n p
    let s :=
      identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate
        (n + 1) q
    let d : identitySpecialOrthogonalNorthPoleProductDomain (n + 1) :=
      ⟨identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient
          (n + 1) s,
        ⟨s.1.2, s.2.2⟩⟩
    identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
        n p =
      identitySpecialOrthogonalNorthPoleProductMappedGroup (n + 1) d := by
  dsimp only
  apply congrArg
    (identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2))
  rw [
    identitySpecialOrthogonalNorthPoleProduct,
    identitySpecialOrthogonalNorthPoleProductLiteralCarrierFiberParametrization,
    identitySpecialOrthogonalLastColumnFiberParametrization,
    identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom_apply]
  simp only [
    identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped,
    identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate,
    identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient,
    Subtype.coe_eta]
  rw [
    identitySpecialOrthogonalLowerChartRankGroup_measurableIdentityChartCoordinate
      (n + 1)
      (Prod.map
        (identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 1))
        id p).1
      (by
        simpa [
          identitySpecialOrthogonalLiteralIdentityChartSource] using hp₁),
    ]
  change
    identitySpecialOrthogonalNorthPoleSection (n + 1) p.2 *
        identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1) p.1 =
      identitySpecialOrthogonalNorthPoleSection (n + 1) p.2 *
        identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1)
          (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 1)
            (identitySpecialOrthogonalLiteralIdentityGroupToMapped
              (n + 1) p.1))
  rw [identitySpecialOrthogonalMappedIdentityGroupToLiteral_rightInverse]

/-- On the lower literal identity chart, the coupled ball-coordinate source is
exactly the preimage of the literal higher-chart target under the literal
fiber parametrization. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLiteralLowerSource_iff_fiber_mem_higherTarget
    (n : ℕ)
    (p :
      identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hp₁ :
      p.1 ∈ identitySpecialOrthogonalLiteralIdentityChartSource n) :
    p ∈
        identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
          n ↔
      identitySpecialOrthogonalNorthPoleProductLiteralCarrierFiberParametrization
          n p ∈
        identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n := by
  let q :=
    identitySpecialOrthogonalNorthPoleProductLiteralProductToMapped n p
  let s :=
    identitySpecialOrthogonalNorthPoleProductLowerSourceSubtypeCoordinate
      (n + 1) q
  let d : identitySpecialOrthogonalNorthPoleProductDomain (n + 1) :=
    ⟨identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient
        (n + 1) s,
      ⟨s.1.2, s.2.2⟩⟩
  have hfiber :
      identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
          n p =
        identitySpecialOrthogonalNorthPoleProductMappedGroup (n + 1) d :=
    identitySpecialOrthogonalNorthPoleProductMappedFiberOnLiteral_eq_mappedGroup
      n p hp₁
  constructor
  · intro hp
    have hsource :
        d ∈
          identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet
            (n + 1) := by
      rcases hp with ⟨e, he, heq⟩
      have hdeq : d = e := by
        apply Subtype.ext
        exact heq.symm
      exact hdeq.symm ▸ he
    change
      identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
          n p ∈
        identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet (n + 1)
    rw [hfiber]
    exact
      ⟨identitySpecialOrthogonalNorthPoleProductMappedGroup_mem_commonMappedGroupSet
          (n + 1) d,
        hsource⟩
  · intro hp
    change
      identitySpecialOrthogonalNorthPoleProductMappedFiberParametrizationOnLiteral
          n p ∈
        identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet (n + 1)
      at hp
    have hsource :
        d ∈
          identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet
            (n + 1) := by
      rw [hfiber] at hp
      exact hp.2
    exact ⟨d, hsource, rfl⟩

/-- On the positive hemisphere and lower literal identity chart, the
sphere-first coupled source is exactly detected by the literal higher-chart
target. -/
theorem
    identitySpecialOrthogonalNorthPoleHemisphereJoint_mem_coupledSource_iff_fiber_mem_higherTarget
    (n : ℕ)
    (p :
      identitySpecialOrthogonalLastColumnSphere (n + 1) ×
        identitySpecialOrthogonalGroup n)
    (hp₀ :
      p.1 ∈ identitySpecialOrthogonalNorthPoleHemisphere (n + 1))
    (hp₁ :
      p.2 ∈ identitySpecialOrthogonalLiteralIdentityChartSource n) :
    p ∈
        identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet n ↔
      identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n p ∈
        identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n := by
  let q :
      identitySpecialOrthogonalGroup n ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    (p.2,
      identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
        (n + 1) ⟨p.1, hp₀⟩)
  have htoSphere :
      identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
          n q =
        (p.2, p.1) := by
    apply Prod.ext
    · rfl
    · exact
        congrArg Subtype.val
          ((identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
            (n + 1)).symm_apply_apply ⟨p.1, hp₀⟩)
  have hfiber :
      identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n p =
        identitySpecialOrthogonalNorthPoleProductLiteralCarrierFiberParametrization
          n q := by
    have hcomp :=
      congrFun
        (identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiber_comp_productToSphere
          n) q
    rw [Function.comp_apply, htoSphere] at hcomp
    exact hcomp
  have hsource :
      p ∈
          identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet n ↔
        q ∈
          identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialSphereSourceSet
            n := by
    constructor
    · rintro ⟨⟨r, hr, hrp⟩, _⟩
      rcases hr with ⟨s, hs, hsr⟩
      have hsq : s = q := by
        apply
          (measurableEmbedding_identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
            n).injective
        rw [hsr, htoSphere]
        apply Prod.swap_injective
        rw [hrp]
        rfl
      exact hsq ▸ hs
    · intro hq
      refine ⟨?_, ⟨Set.mem_univ _, hp₁⟩⟩
      refine
        ⟨identitySpecialOrthogonalNorthPoleProductLiteralLowerNormalizedProductToSphere
            n q,
          ⟨q, hq, rfl⟩,
          ?_⟩
      rw [htoSphere]
      rfl
  rw [hsource, hfiber]
  exact
    identitySpecialOrthogonalNorthPoleProductLiteralLowerSource_iff_fiber_mem_higherTarget
      n q hp₁

/-- On the positive hemisphere, membership of the literal joint fiber in the
higher product-chart target forces the lower group into the lower identity
chart. -/
theorem
    identitySpecialOrthogonalNorthPoleHemisphereJointFiber_mem_higherTarget_imp_snd_mem_identityChart
    (n : ℕ)
    (p :
      identitySpecialOrthogonalLastColumnSphere (n + 1) ×
        identitySpecialOrthogonalGroup n)
    (hp₀ :
      p.1 ∈ identitySpecialOrthogonalNorthPoleHemisphere (n + 1))
    (hp :
      identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n p ∈
        identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n) :
    p.2 ∈ identitySpecialOrthogonalLiteralIdentityChartSource n := by
  change
    identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2)
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n p) ∈
      identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet (n + 1)
    at hp
  rcases
      exists_identitySpecialOrthogonalNorthPoleProductMappedGroup_eq_of_mem_commonMappedGroupSet
        (n + 1) _ hp.1 with
    ⟨d, hd⟩
  have hdlit :
      identitySpecialOrthogonalNorthPoleProduct (n + 1) d =
        identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n p := by
    apply
      (identitySpecialOrthogonalLiteralMappedIdentityGroupHomeomorph
        (n + 2)).injective
    exact hd
  let v :
      Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
      (n + 1) ⟨p.1, hp₀⟩
  have hjoint :
      identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n p =
        identitySpecialOrthogonalLastColumnFiberParametrization n
          (identitySpecialOrthogonalNorthPoleSection (n + 1) v) p.2 := by
    exact
      identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization_eq_northPoleSection
        n p.1 hp₀ p.2
  have hcol :
      identitySpecialOrthogonalNorthPoleInverse (n + 1)
          ⟨d.1.2, d.2.2⟩ =
        identitySpecialOrthogonalNorthPoleInverse (n + 1) v := by
    calc
      identitySpecialOrthogonalNorthPoleInverse (n + 1)
          ⟨d.1.2, d.2.2⟩ =
          identitySpecialOrthogonalLastColumn (n + 1)
            (identitySpecialOrthogonalNorthPoleProduct (n + 1) d) := by
        rw [identitySpecialOrthogonalLastColumn_northPoleProduct]
      _ =
          identitySpecialOrthogonalLastColumn (n + 1)
            (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
              n p) :=
        congrArg (identitySpecialOrthogonalLastColumn (n + 1)) hdlit
      _ =
          identitySpecialOrthogonalLastColumn (n + 1)
            (identitySpecialOrthogonalNorthPoleSection (n + 1) v) := by
        rw [hjoint]
        exact
          identitySpecialOrthogonalLastColumnFiberParametrization_mem
            n (identitySpecialOrthogonalNorthPoleSection (n + 1) v) p.2
      _ =
          identitySpecialOrthogonalNorthPoleInverse (n + 1) v := by
        exact
          identitySpecialOrthogonalLastColumn_northPoleSection
            (n + 1) v
  have hv : (⟨d.1.2, d.2.2⟩ :
      Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) = v := by
    apply Subtype.ext
    have hcoordinate :=
      congrArg
        (identitySpecialOrthogonalNorthPoleCoordinate (n + 1)) hcol
    simpa only [
      identitySpecialOrthogonalNorthPoleCoordinate_inverse] using hcoordinate
  have hembed :
      identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1)
          (identitySpecialOrthogonalLowerChartRankGroup (n + 1)
            ⟨d.1.1, d.2.1⟩) =
        identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1) p.2 := by
    have hproduct := hdlit
    rw [
      identitySpecialOrthogonalNorthPoleProduct,
      hjoint,
      identitySpecialOrthogonalLastColumnFiberParametrization,
      identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom_apply,
      hv] at hproduct
    exact mul_left_cancel hproduct
  have hlower :
      identitySpecialOrthogonalLowerChartRankGroup (n + 1)
          ⟨d.1.1, d.2.1⟩ =
        p.2 :=
    identitySpecialOrthogonalLastColumnFiberEmbedHom_injective
      (n + 1) hembed
  change
    identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 1) p.2 ∈
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).source
  rw [← hlower, identitySpecialOrthogonalLowerChartRankGroup,
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_leftInverse]
  exact
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).map_target d.2.1

/-- The positive-hemisphere cylinder on the sphere-first joint carrier. -/
def
    identitySpecialOrthogonalNorthPoleHemisphereJointHemisphereCylinder
    (n : ℕ) :
    Set
      (identitySpecialOrthogonalLastColumnSphere (n + 1) ×
        identitySpecialOrthogonalGroup n) :=
  identitySpecialOrthogonalNorthPoleHemisphere (n + 1) ×ˢ Set.univ

theorem
    measurableSet_identitySpecialOrthogonalNorthPoleHemisphereJointHemisphereCylinder
    (n : ℕ) :
    MeasurableSet
      (identitySpecialOrthogonalNorthPoleHemisphereJointHemisphereCylinder
        n) :=
  (measurableSet_identitySpecialOrthogonalNorthPoleHemisphere
    (n + 1)).prod MeasurableSet.univ

/-- On the positive hemisphere, higher-target membership already forces the
lower chart condition, so the coupled source is the exact higher-target
preimage inside the hemisphere cylinder. -/
theorem
    identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet_eq_hemisphere_inter_preimage_higherTarget
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet n =
      identitySpecialOrthogonalNorthPoleHemisphereJointHemisphereCylinder n ∩
        identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
            n ⁻¹'
          identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n := by
  ext p
  constructor
  · intro hp
    have hp₀ :
        p.1 ∈ identitySpecialOrthogonalNorthPoleHemisphere (n + 1) := by
      rcases hp.1 with ⟨q, hq, rfl⟩
      exact
        identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet_snd_mem_hemisphere
          n q hq
    refine
      ⟨⟨hp₀, Set.mem_univ p.2⟩,
        (identitySpecialOrthogonalNorthPoleHemisphereJoint_mem_coupledSource_iff_fiber_mem_higherTarget
          n p hp₀ hp.2.2).mp hp⟩
  · rintro ⟨⟨hp₀, _⟩, hp⟩
    have hp₁ :
        p.2 ∈ identitySpecialOrthogonalLiteralIdentityChartSource n :=
      identitySpecialOrthogonalNorthPoleHemisphereJointFiber_mem_higherTarget_imp_snd_mem_identityChart
        n p hp₀ hp
    exact
      (identitySpecialOrthogonalNorthPoleHemisphereJoint_mem_coupledSource_iff_fiber_mem_higherTarget
        n p hp₀ hp₁).mpr hp

/-- The positive-hemisphere/lower-chart cylinder on which the target-preimage
identity is intrinsic rather than dependent on the irrelevant measurable
extension. -/
def
    identitySpecialOrthogonalNorthPoleHemisphereJointChartCylinder
    (n : ℕ) :
    Set
      (identitySpecialOrthogonalLastColumnSphere (n + 1) ×
        identitySpecialOrthogonalGroup n) :=
  identitySpecialOrthogonalNorthPoleHemisphere (n + 1) ×ˢ
    identitySpecialOrthogonalLiteralIdentityChartSource n

theorem
    measurableSet_identitySpecialOrthogonalNorthPoleHemisphereJointChartCylinder
    (n : ℕ) :
    MeasurableSet
      (identitySpecialOrthogonalNorthPoleHemisphereJointChartCylinder n) :=
  (measurableSet_identitySpecialOrthogonalNorthPoleHemisphere
    (n + 1)).prod
      (identitySpecialOrthogonalLiteralIdentityChartSource_isOpen n
        ).measurableSet

/-- The coupled source is the literal target preimage inside the intrinsic
positive-hemisphere/lower-chart cylinder. -/
theorem
    identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet_eq_inter_preimage_higherTarget
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet n =
      identitySpecialOrthogonalNorthPoleHemisphereJointChartCylinder n ∩
        identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
            n ⁻¹'
          identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n := by
  ext p
  constructor
  · intro hp
    have hp₀ :
        p.1 ∈ identitySpecialOrthogonalNorthPoleHemisphere (n + 1) := by
      rcases hp.1 with ⟨q, hq, rfl⟩
      exact
        identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet_snd_mem_hemisphere
          n q hq
    refine
      ⟨⟨hp₀, hp.2.2⟩,
        (identitySpecialOrthogonalNorthPoleHemisphereJoint_mem_coupledSource_iff_fiber_mem_higherTarget
          n p hp₀ hp.2.2).mp hp⟩
  · rintro ⟨⟨hp₀, hp₁⟩, hp⟩
    exact
      (identitySpecialOrthogonalNorthPoleHemisphereJoint_mem_coupledSource_iff_fiber_mem_higherTarget
        n p hp₀ hp₁).mpr hp

/-- Almost everywhere on the intrinsic cylinder, membership in the coupled
source is equivalent to membership of the literal joint fiber in the higher
chart target. -/
theorem
    ae_identitySpecialOrthogonalNorthPoleHemisphereJoint_mem_coupledSource_iff_fiber_mem_higherTarget
    (n : ℕ)
    (μ :
      Measure
        (identitySpecialOrthogonalLastColumnSphere (n + 1) ×
          identitySpecialOrthogonalGroup n)) :
    ∀ᵐ p ∂μ.restrict
        (identitySpecialOrthogonalNorthPoleHemisphereJointChartCylinder n),
      p ∈
          identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet
            n ↔
        identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
            n p ∈
          identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n := by
  filter_upwards [
    MeasureTheory.ae_restrict_mem
      (measurableSet_identitySpecialOrthogonalNorthPoleHemisphereJointChartCylinder
        n)] with p hp
  exact
    identitySpecialOrthogonalNorthPoleHemisphereJoint_mem_coupledSource_iff_fiber_mem_higherTarget
      n p hp.1 hp.2

/-- Restricting first to the intrinsic cylinder and then pulling back the
higher target recovers exactly the coupled product measure.
This is the form needed by `Measure.restrict_map`. -/
theorem
    restrict_preimage_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
    (n : ℕ) :
    let μ :=
      ((identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
          (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))).prod
        (identitySpecialOrthogonalDifferentialMeasure n)
    (μ.restrict
        (identitySpecialOrthogonalNorthPoleHemisphereJointChartCylinder n)
      ).restrict
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
            n ⁻¹'
          identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n) =
      identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure
        n := by
  dsimp only
  rw [
    Measure.restrict_restrict
      ((measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
        n).preimage
          (measurable_identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
            n)),
    identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure,
    identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet_eq_inter_preimage_higherTarget,
    inter_comm]

end PositiveDefiniteIntegralLattice
