import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereFiberDifferential

/-!
# The positive-hemisphere differential fiber bind as a product pushforward

This module packages the literal joint fiber map on the ambient last-column
sphere, identifies the differential fiber kernel with the corresponding
mapped constant kernel almost everywhere on the positive hemisphere, and
expands the resulting kernel bind as a product-measure pushforward.

No coupled local source, chart restriction, total-mass cancellation, rank
recurrence, or Gamma evaluation is used here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleHemisphereFiberKernelProductGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleHemisphereFiberKernelProductGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- The sphere-first joint fiber map obtained by swapping into the
lower-group/sphere parametrization. -/
def identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
    (n : ℕ)
    (p :
      identitySpecialOrthogonalLastColumnSphere (n + 1) ×
        identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalGroup (n + 1) :=
  identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
    n (p.2, p.1)

theorem
    measurable_identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
        n) := by
  exact
    (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
      n).comp
        (measurable_snd.prod measurable_fst)

/-- On the positive hemisphere, the measurable joint extension has the
north-pole-section fiber formula. -/
theorem
    identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization_eq_northPoleSection
    (n : ℕ)
    (x : identitySpecialOrthogonalLastColumnSphere (n + 1))
    (hx :
      x ∈ identitySpecialOrthogonalNorthPoleHemisphere (n + 1))
    (h : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
        n (x, h) =
      identitySpecialOrthogonalLastColumnFiberParametrization n
        (identitySpecialOrthogonalNorthPoleSection (n + 1)
          (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
            (n + 1) ⟨x, hx⟩))
        h := by
  let p :
      identitySpecialOrthogonalGroup n ×
        (identitySpecialOrthogonalNorthPoleHemisphere (n + 1) :
          Set (identitySpecialOrthogonalLastColumnSphere (n + 1))) :=
    ⟨h, ⟨x, hx⟩⟩
  have hp :=
    identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization_eq_hemisphere
      n p
  simpa [
    p,
    identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization,
    identitySpecialOrthogonalNorthPoleProductLiteralLowerHemisphereInclusion,
    identitySpecialOrthogonalNorthPoleProductLiteralHemisphereFiberParametrization]
    using hp

/-- Under normalized sphere measure restricted to the positive hemisphere,
the differential fiber kernel is almost everywhere the lower differential
measure pushed through the sphere-first joint fiber map. -/
theorem
    ae_identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply_eq_map_hemisphereJointFiber
    (n : ℕ) :
    ∀ᵐ x ∂
      (identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
        (identitySpecialOrthogonalNorthPoleHemisphere (n + 1)),
      identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n x =
        Measure.map
          (fun h =>
            identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
              n (x, h))
          (identitySpecialOrthogonalDifferentialMeasure n) := by
  filter_upwards [
    MeasureTheory.ae_restrict_mem
      (measurableSet_identitySpecialOrthogonalNorthPoleHemisphere
        (n + 1)),
    ae_identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply_eq_map_northPoleSection
      n] with x hx hkernel
  calc
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n x =
        Measure.map
          (identitySpecialOrthogonalLastColumnFiberParametrization n
            (identitySpecialOrthogonalNorthPoleSection (n + 1)
              (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
                (n + 1) ⟨x, hx⟩)))
          (identitySpecialOrthogonalDifferentialMeasure n) :=
      hkernel hx
    _ =
        Measure.map
          (fun h =>
            identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
              n (x, h))
          (identitySpecialOrthogonalDifferentialMeasure n) := by
      apply Measure.map_congr
      filter_upwards [] with h
      exact
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization_eq_northPoleSection
          n x hx h).symm

/-- Integrating the sphere-indexed differential fiber kernel over the
positive hemisphere is exactly the pushforward of normalized-hemisphere
sphere measure times the full lower-rank differential Haar measure. -/
theorem
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_comp_restrict_northPoleHemisphere
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
        ((identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
          (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n)
        (((identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
            (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))).prod
          (identitySpecialOrthogonalDifferentialMeasure n)) := by
  let μ :
      Measure (identitySpecialOrthogonalLastColumnSphere (n + 1)) :=
    (identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
      (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))
  let κ₀ :
      ProbabilityTheory.Kernel
        (identitySpecialOrthogonalLastColumnSphere (n + 1))
        (identitySpecialOrthogonalLastColumnSphere (n + 1) ×
          identitySpecialOrthogonalGroup n) :=
    ProbabilityTheory.Kernel.id ×ₖ
      ProbabilityTheory.Kernel.const
        (identitySpecialOrthogonalLastColumnSphere (n + 1))
        (identitySpecialOrthogonalDifferentialMeasure n)
  let f :=
    identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization n
  have hf : Measurable f :=
    measurable_identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
      n
  have hkernel :
      ∀ᵐ x ∂μ,
        identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n x =
          (κ₀.map f) x := by
    filter_upwards [
      ae_identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply_eq_map_hemisphereJointFiber
        n] with x hx
    rw [hx, ProbabilityTheory.Kernel.map_apply _ hf]
    change
      Measure.map (fun h => f (x, h))
          (identitySpecialOrthogonalDifferentialMeasure n) =
        Measure.map f
          ((ProbabilityTheory.Kernel.id ×ₖ
            ProbabilityTheory.Kernel.const
              (identitySpecialOrthogonalLastColumnSphere (n + 1))
              (identitySpecialOrthogonalDifferentialMeasure n)) x)
    rw [ProbabilityTheory.Kernel.prod_apply,
      ProbabilityTheory.Kernel.id_apply,
      ProbabilityTheory.Kernel.const_apply,
      Measure.dirac_prod,
      Measure.map_map hf measurable_prodMk_left]
    rfl
  calc
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ μ =
        (κ₀.map f) ∘ₘ μ :=
      Measure.comp_congr hkernel
    _ = Measure.map f (κ₀ ∘ₘ μ) := by
      rw [Measure.map_comp μ κ₀ hf]
    _ = Measure.map f
        (μ.prod (identitySpecialOrthogonalDifferentialMeasure n)) := by
      rw [show κ₀ =
          ProbabilityTheory.Kernel.id ×ₖ
            ProbabilityTheory.Kernel.const
              (identitySpecialOrthogonalLastColumnSphere (n + 1))
              (identitySpecialOrthogonalDifferentialMeasure n) by rfl,
        ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
    _ = Measure.map
        (identitySpecialOrthogonalNorthPoleHemisphereJointFiberParametrization
          n)
        (((identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
            (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))).prod
          (identitySpecialOrthogonalDifferentialMeasure n)) := by
      rfl

end PositiveDefiniteIntegralLattice
