import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereTargetPreimage

/-!
# Restricting the positive-hemisphere differential-fiber bind

The target-preimage interface is applied only at measure level.  Because
the sphere factor is already restricted to the positive hemisphere, pulling
the higher-chart target back through the joint fiber map gives
exactly the coupled product.  `Measure.restrict_map` then identifies
the local joint-fiber pushforward with the corresponding restriction of the
unrestricted positive-hemisphere differential-fiber bind.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleHemisphereTargetRestrictionGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleHemisphereTargetRestrictionGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- Pulling the higher target back through the positive-hemisphere
joint fiber map restricts the unrestricted hemisphere product to exactly the
coupled product measure. -/
theorem
    restrict_preimage_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet_eq_coupledProduct
    (n : ℕ) :
    let μ :=
      ((identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
          (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))).prod
        (identitySpecialOrthogonalDifferentialMeasure n)
    μ.restrict
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
            n ⁻¹'
          identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n) =
      identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure
        n := by
  let σ :=
    identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)
  let H :=
    identitySpecialOrthogonalNorthPoleHemisphere (n + 1)
  let ν :=
    identitySpecialOrthogonalDifferentialMeasure n
  let μ := (σ.restrict H).prod ν
  let C :=
    identitySpecialOrthogonalNorthPoleHemisphereJointHemisphereCylinder n
  let f :=
    identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization n
  let T :=
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet n
  have hH : MeasurableSet H :=
    measurableSet_identitySpecialOrthogonalNorthPoleHemisphere (n + 1)
  have hT : MeasurableSet T :=
    measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
      n
  have hpre : MeasurableSet (f ⁻¹' T) :=
    hT.preimage
      (measurable_identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
        n)
  have hμC : μ.restrict C = μ := by
    change
      ((σ.restrict H).prod ν).restrict (H ×ˢ Set.univ) =
        (σ.restrict H).prod ν
    rw [← Measure.prod_restrict,
      Measure.restrict_restrict hH,
      inter_self,
      Measure.restrict_univ]
  change μ.restrict (f ⁻¹' T) =
    identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure n
  calc
    μ.restrict (f ⁻¹' T) =
        (μ.restrict C).restrict (f ⁻¹' T) := by
      rw [hμC]
    _ = μ.restrict ((f ⁻¹' T) ∩ C) := by
      rw [Measure.restrict_restrict hpre]
    _ = μ.restrict
        (identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet
          n) := by
      rw [
        identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet_eq_hemisphere_inter_preimage_higherTarget,
        inter_comm]
    _ =
        identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure
          n := by
      rfl

/-- The local sphere-first joint-fiber pushforward is the literal
higher-target restriction of the unrestricted positive-hemisphere
differential-fiber bind. -/
theorem
    map_identitySpecialOrthogonalNorthPoleHemisphereJointFiber_coupledProduct_eq_restrict_fiberKernel_comp
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n)
        (identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure
          n) =
      (identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
          ((identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
            (identitySpecialOrthogonalNorthPoleHemisphere (n + 1)))
        ).restrict
          (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n) := by
  let μ :=
    ((identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
        (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))).prod
      (identitySpecialOrthogonalDifferentialMeasure n)
  let f :=
    identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization n
  let T :=
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet n
  have hf : Measurable f :=
    measurable_identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
      n
  have hT : MeasurableSet T :=
    measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
      n
  calc
    Measure.map f
        (identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure
          n) =
      Measure.map f (μ.restrict (f ⁻¹' T)) := by
        rw [
          restrict_preimage_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet_eq_coupledProduct]
    _ = (Measure.map f μ).restrict T := by
      rw [Measure.restrict_map hf hT]
    _ =
      (identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
          ((identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
            (identitySpecialOrthogonalNorthPoleHemisphere (n + 1)))
        ).restrict T := by
      rw [
        identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_comp_restrict_northPoleHemisphere]

end PositiveDefiniteIntegralLattice
