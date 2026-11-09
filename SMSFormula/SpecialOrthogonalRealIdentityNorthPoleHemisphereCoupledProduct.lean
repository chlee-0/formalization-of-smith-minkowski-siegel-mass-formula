import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereFiberKernelProduct
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductLiteralSphereFiberMeasure

/-!
# The coupled positive-hemisphere product in sphere-first coordinates

This module swaps the existing group-first local normalized-sphere product
into the sphere-first coordinates used by the unrestricted differential-fiber
kernel bind.  The exact source records both the coupled product condition and
the lower literal identity-chart condition.

The resulting restricted product is also pushed through the literal joint
fiber map.  No higher-chart target restriction, mapped/literal higher-group
transport, global-bind restriction, total-mass cancellation, rank recurrence,
or Gamma evaluation is used here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleHemisphereCoupledProductGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleHemisphereCoupledProductGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- The exact local source in sphere-first coordinates.  Besides the swapped
coupled source, it explicitly retains lower identity-chart membership because
that membership belongs to the source measure rather than the coupled set
alone. -/
def
    identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet
    (n : ℕ) :
    Set
      (identitySpecialOrthogonalLastColumnSphere (n + 1) ×
        identitySpecialOrthogonalGroup n) :=
  (Prod.swap ''
      identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
        n) ∩
    (Set.univ ×ˢ identitySpecialOrthogonalLiteralIdentityChartSource n)

theorem
    measurableSet_identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet
    (n : ℕ) :
    MeasurableSet
      (identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet
        n) := by
  refine
    ((MeasurableEquiv.prodComm :
      (identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere (n + 1)) ≃ᵐ
      (identitySpecialOrthogonalLastColumnSphere (n + 1) ×
        identitySpecialOrthogonalGroup n)).measurableEmbedding.measurableSet_image.2
        (measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
          n)).inter ?_
  exact
    MeasurableSet.univ.prod
      (identitySpecialOrthogonalLiteralIdentityChartSource_isOpen n).measurableSet

/-- Normalized hemisphere measure times full lower differential Haar,
restricted to the exact sphere-first local source. -/
def
    identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure
    (n : ℕ) :
    Measure
      (identitySpecialOrthogonalLastColumnSphere (n + 1) ×
        identitySpecialOrthogonalGroup n) :=
  (((identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
      (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))).prod
    (identitySpecialOrthogonalDifferentialMeasure n)).restrict
      (identitySpecialOrthogonalNorthPoleHemisphereJointCoupledSourceSet n)

/-- Swapping the existing group-first coupled local product gives exactly the
sphere-first unrestricted product restricted to the source above. -/
theorem
    map_swap_identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
    (n : ℕ) :
    Measure.map Prod.swap
        (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
          n) =
      identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure
        n := by
  let A :
      Set
        (identitySpecialOrthogonalGroup n ×
          identitySpecialOrthogonalLastColumnSphere (n + 1)) :=
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
      n
  let C : Set (identitySpecialOrthogonalGroup n) :=
    identitySpecialOrthogonalLiteralIdentityChartSource n
  let μ :
      Measure (identitySpecialOrthogonalLastColumnSphere (n + 1)) :=
    (identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
      (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))
  let ν : Measure (identitySpecialOrthogonalGroup n) :=
    identitySpecialOrthogonalDifferentialMeasure n
  have hA : MeasurableSet A :=
    measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereSourceSet
      n
  have hswapA : MeasurableSet (Prod.swap '' A) := by
    exact
      ((MeasurableEquiv.prodComm :
        (identitySpecialOrthogonalGroup n ×
          identitySpecialOrthogonalLastColumnSphere (n + 1)) ≃ᵐ
        (identitySpecialOrthogonalLastColumnSphere (n + 1) ×
          identitySpecialOrthogonalGroup n)).measurableEmbedding.measurableSet_image.2
          hA)
  have hprod :
      μ.prod (ν.restrict C) =
        (μ.prod ν).restrict (Set.univ ×ˢ C) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := μ) (ν := ν) Set.univ C)
  rw [
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure,
    identitySpecialOrthogonalNorthPoleProductLiteralLowerDifferentialNormalizedSphereHemisphereMeasure]
  change
    Measure.map Prod.swap (((ν.restrict C).prod μ).restrict A) =
      identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure n
  calc
    Measure.map Prod.swap (((ν.restrict C).prod μ).restrict A) =
        (Measure.map Prod.swap ((ν.restrict C).prod μ)).restrict
          (Prod.swap '' A) := by
      rw [Measure.restrict_map measurable_swap hswapA,
        Set.preimage_image_eq _ Prod.swap_injective]
    _ = (μ.prod (ν.restrict C)).restrict (Prod.swap '' A) := by
      rw [Measure.prod_swap]
    _ = ((μ.prod ν).restrict (Set.univ ×ˢ C)).restrict
          (Prod.swap '' A) := by
      rw [hprod]
    _ = (μ.prod ν).restrict
          ((Prod.swap '' A) ∩ (Set.univ ×ˢ C)) := by
      rw [Measure.restrict_restrict hswapA]
    _ =
        identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure
          n := by
      rfl

/-- The literal sphere-side local pushforward is the sphere-first joint fiber
pushforward of the restricted product just constructed. -/
theorem
    map_identitySpecialOrthogonalNorthPoleHemisphereJointFiber_coupledProduct
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n)
        (identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure
          n) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
          n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
          n) := by
  calc
    Measure.map
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n)
        (identitySpecialOrthogonalNorthPoleHemisphereJointCoupledProductMeasure
          n) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n)
        (Measure.map Prod.swap
          (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
            n)) := by
      rw [
        map_swap_identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure]
    _ =
      Measure.map
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
            n ∘ Prod.swap)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
          n) := by
      rw [Measure.map_map
        (measurable_identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n)
        measurable_swap]
    _ =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
          n)
        (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
          n) := by
      rfl

end PositiveDefiniteIntegralLattice
