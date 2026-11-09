import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereHigherLiteral

/-!
# Restricting the full sphere differential-fiber bind to the north-pole chart

The higher product-chart target has positive-hemisphere last column.
Since every sphere-indexed differential fiber is supported on its prescribed
last column, fibers indexed outside that hemisphere give zero mass to the
target.  Therefore restricting the full normalized-sphere differential-fiber
bind to the target agrees with restricting the positive-hemisphere bind.

Support, complementary-bind vanishing, and the final restriction identity are
proved as separate lemmas.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleHemisphereFullSphereRestrictionGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleHemisphereFullSphereRestrictionGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- Every literal higher product-chart target point has last column in the
positive north-pole hemisphere. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet_lastColumn_mem_hemisphere
    (n : ℕ)
    (g : identitySpecialOrthogonalGroup (n + 1))
    (hg :
      g ∈
        identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n) :
    identitySpecialOrthogonalLastColumn (n + 1) g ∈
      identitySpecialOrthogonalNorthPoleHemisphere (n + 1) := by
  change
    identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2) g ∈
      identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
        (n + 1) at hg
  rcases
      exists_identitySpecialOrthogonalNorthPoleProductMappedGroup_eq_of_mem_commonMappedGroupSet
        (n + 1)
        (identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2) g)
        hg.1 with
    ⟨p, hp⟩
  have hproduct :
      identitySpecialOrthogonalNorthPoleProduct (n + 1) p = g := by
    apply
      (identitySpecialOrthogonalLiteralMappedIdentityGroupHomeomorph
        (n + 2)).injective
    exact hp
  rw [← hproduct,
    identitySpecialOrthogonalLastColumn_northPoleProduct]
  exact
    identitySpecialOrthogonalNorthPoleInverse_mem_hemisphere
      (n + 1) ⟨p.1.2, p.2.2⟩

/-- A sphere-indexed differential fiber is supported on its prescribed last
column. -/
theorem
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure_compl_fiber_eq_zero
    (n : ℕ)
    (x : identitySpecialOrthogonalLastColumnSphere (n + 1)) :
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure n x
        (identitySpecialOrthogonalLastColumnFiberAt (n + 1) x)ᶜ = 0 := by
  rw [
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure,
    Measure.smul_apply,
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure_compl_fiber_eq_zero]
  simp

/-- A fiber indexed outside the positive hemisphere gives the literal higher
chart target zero mass. -/
theorem
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply_literalHigherTarget_eq_zero_of_not_mem_hemisphere
    (n : ℕ)
    (x : identitySpecialOrthogonalLastColumnSphere (n + 1))
    (hx :
      x ∉ identitySpecialOrthogonalNorthPoleHemisphere (n + 1)) :
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n x
        (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n) = 0 := by
  rw [
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply]
  apply measure_mono_null
    (t :=
      (identitySpecialOrthogonalLastColumnFiberAt (n + 1) x)ᶜ)
  · intro g hg
    change identitySpecialOrthogonalLastColumn (n + 1) g ≠ x
    intro hcol
    apply hx
    rw [← hcol]
    exact
      identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet_lastColumn_mem_hemisphere
        n g hg
  · exact
      identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure_compl_fiber_eq_zero
        n x

/-- The differential-fiber bind over the complementary hemisphere vanishes
after restriction to the literal higher chart target. -/
theorem
    restrict_identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_comp_restrict_compl_northPoleHemisphere_eq_zero
    (n : ℕ) :
    (identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
        ((identitySpecialOrthogonalNormalizedSphereMeasure
          (n + 1)).restrict
          (identitySpecialOrthogonalNorthPoleHemisphere (n + 1))ᶜ)
      ).restrict
        (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n) = 0 := by
  let κ :=
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n
  let σ :=
    identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)
  let H :=
    identitySpecialOrthogonalNorthPoleHemisphere (n + 1)
  let T :=
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet n
  have hH : MeasurableSet H :=
    measurableSet_identitySpecialOrthogonalNorthPoleHemisphere (n + 1)
  have hT : MeasurableSet T :=
    measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
      n
  change (κ ∘ₘ σ.restrict Hᶜ).restrict T = 0
  rw [Measure.restrict_eq_zero,
    Measure.bind_apply hT κ.measurable.aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [MeasureTheory.ae_restrict_mem hH.compl] with x hx
  exact
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply_literalHigherTarget_eq_zero_of_not_mem_hemisphere
      n x hx

/-- Restricting the full normalized-sphere differential-fiber bind to the
literal higher chart target discards exactly the fibers indexed outside the
positive hemisphere. -/
theorem
    restrict_identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_comp_normalizedSphereMeasure_eq_restrict_comp_northPoleHemisphere
    (n : ℕ) :
    (identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
        identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)
      ).restrict
        (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n) =
      (identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
          ((identitySpecialOrthogonalNormalizedSphereMeasure
            (n + 1)).restrict
            (identitySpecialOrthogonalNorthPoleHemisphere (n + 1)))
        ).restrict
          (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n) := by
  let κ :=
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n
  let σ :=
    identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)
  let H :=
    identitySpecialOrthogonalNorthPoleHemisphere (n + 1)
  let T :=
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet n
  have hH : MeasurableSet H :=
    measurableSet_identitySpecialOrthogonalNorthPoleHemisphere (n + 1)
  have hcompl :
      (κ ∘ₘ σ.restrict Hᶜ).restrict T = 0 :=
    restrict_identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_comp_restrict_compl_northPoleHemisphere_eq_zero
      n
  change (κ ∘ₘ σ).restrict T =
    (κ ∘ₘ σ.restrict H).restrict T
  calc
    (κ ∘ₘ σ).restrict T =
        (κ ∘ₘ (σ.restrict H + σ.restrict Hᶜ)).restrict T := by
      rw [Measure.restrict_add_restrict_compl hH]
    _ =
        (κ ∘ₘ σ.restrict H).restrict T +
          (κ ∘ₘ σ.restrict Hᶜ).restrict T := by
      rw [Measure.comp_add, Measure.restrict_add]
    _ = (κ ∘ₘ σ.restrict H).restrict T := by
      rw [hcompl, add_zero]

/-- The target restriction of the full normalized-sphere bind is lower-rank
differential total mass times higher-rank probability Haar, with the
restriction retained. -/
theorem
    restrict_identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_comp_normalizedSphereMeasure_eq_restrict_smul_probabilityHaar
    (n : ℕ) :
    (identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
        identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)
      ).restrict
        (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n) =
      (identitySpecialOrthogonalDifferentialMeasure n Set.univ •
          identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)
        ).restrict
          (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n) := by
  rw [
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_comp_normalizedSphereMeasure]

/-- Substituting the full normalized-sphere bind into the literal local
comparison exposes both differential total mass and higher probability Haar,
but deliberately retains their common higher-chart restriction. -/
theorem
    identitySpecialOrthogonalSphereStep_smul_two_smul_restrict_lowerMass_probabilityHaar_eq_smul_literalHigherDifferential
    (n : ℕ) :
    identitySpecialOrthogonalSphereStep (n + 2) •
        ((2 : ℝ≥0∞) •
          (identitySpecialOrthogonalDifferentialMeasure n Set.univ •
              identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)
            ).restrict
              (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
                n)) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|)⁻¹ •
        (identitySpecialOrthogonalDifferentialMeasure (n + 1)).restrict
          (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n) := by
  calc
    identitySpecialOrthogonalSphereStep (n + 2) •
        ((2 : ℝ≥0∞) •
          (identitySpecialOrthogonalDifferentialMeasure n Set.univ •
              identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)
            ).restrict
              (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
                n)) =
      identitySpecialOrthogonalSphereStep (n + 2) •
        ((2 : ℝ≥0∞) •
          (identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
              identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)
            ).restrict
              (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
                n)) := by
      rw [
        restrict_identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_comp_normalizedSphereMeasure_eq_restrict_smul_probabilityHaar]
    _ =
      identitySpecialOrthogonalSphereStep (n + 2) •
        ((2 : ℝ≥0∞) •
          (identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
              ((identitySpecialOrthogonalNormalizedSphereMeasure
                (n + 1)).restrict
                (identitySpecialOrthogonalNorthPoleHemisphere (n + 1)))
            ).restrict
              (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
                n)) := by
      rw [
        restrict_identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_comp_normalizedSphereMeasure_eq_restrict_comp_northPoleHemisphere]
    _ =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|)⁻¹ •
        (identitySpecialOrthogonalDifferentialMeasure (n + 1)).restrict
          (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n) :=
      identitySpecialOrthogonalSphereStep_smul_two_smul_restrict_hemisphereFiberKernel_eq_smul_literalHigherDifferential
        n

end PositiveDefiniteIntegralLattice
