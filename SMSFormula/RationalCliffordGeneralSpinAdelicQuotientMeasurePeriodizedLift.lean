import SMSFormula.RationalCliffordGeneralSpinAdelicFundamentalDomainSection
import SMSFormula.RationalCliffordGeneralSpinAdelicReferenceQuotientMeasure

/-!
# Periodizing a measure on the rational adelic GSpin quotient

The explicit measurable fundamental-domain section lets us lift an arbitrary
measure on the rational left quotient to the fixed transversal.  Summing all
rational-diagonal translates then gives an ambient measure without choosing
any further representatives.

This module proves the exact nonnegative-integral formula for that
periodization and recovers the original lifted measure on the fundamental
domain.  No Haar proportionality, right invariance, or normalization scalar is
asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## The measure on the fixed transversal -/

/-- Lift a quotient measure to the fixed exact fundamental domain through the
explicit measurable section. -/
def fullAdelicCliffordGeneralSpinFundamentalSectionLift
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Measure V.FullAdelicCliffordGeneralSpinGroup :=
  Measure.map V.fullAdelicCliffordGeneralSpinFundamentalDomainSection μ

/-- Pushing the fundamental-section lift back to the quotient recovers the
original measure exactly. -/
theorem map_fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalSectionLift
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Measure.map V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordGeneralSpinFundamentalSectionLift μ) = μ := by
  rw [fullAdelicCliffordGeneralSpinFundamentalSectionLift,
    Measure.map_map
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap_measurable
      V.measurable_fullAdelicCliffordGeneralSpinFundamentalDomainSection]
  have hfun :
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap ∘
          V.fullAdelicCliffordGeneralSpinFundamentalDomainSection =
        id := by
    funext y
    exact
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalDomainSection y
  rw [hfun, Measure.map_id]

/-! ## Rational-diagonal translates and periodization -/

/-- Translate the chosen representative of a quotient point by one rational
adelic GSpin diagonal element. -/
def fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
    (gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.FullAdelicCliffordGeneralSpinGroup :=
  (gamma : V.FullAdelicCliffordGeneralSpinGroup) *
    V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y

theorem measurable_fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
    (gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
    Measurable
      (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection gamma) :=
  (measurable_const_mul (gamma : V.FullAdelicCliffordGeneralSpinGroup)).comp
    V.measurable_fullAdelicCliffordGeneralSpinFundamentalDomainSection

/-- Periodize a quotient measure over every rational-diagonal translate of
its fixed fundamental-domain lift. -/
def fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Measure V.FullAdelicCliffordGeneralSpinGroup :=
  Measure.sum fun gamma :
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup =>
    Measure.map
      (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection gamma)
      μ

/-- Exact nonnegative-integral formula for the periodized quotient lift. -/
theorem lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ =
      ∑' gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
        ∫⁻ y,
          f (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
            gamma y) ∂μ := by
  rw [fullAdelicCliffordGeneralSpinPeriodizedQuotientLift,
    lintegral_sum_measure]
  congr 1
  funext gamma
  rw [lintegral_map hf
    (V.measurable_fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
      gamma)]

/-! ## Exact recovery on the fundamental domain -/

/-- A rational translate of a chosen section point lies again in the exact
fundamental domain precisely for the identity translate. -/
theorem fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection_mem_iff
    (gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection gamma y ∈
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain ↔
      gamma = 1 := by
  constructor
  · intro hgamma
    rcases
        V.existsUnique_rationalGeneralSpinDiagonal_mul_mem_measurableFundamentalDomain
          (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y) with
      ⟨delta, hdelta, hunique⟩
    have hone :
        ((1 : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
            V.FullAdelicCliffordGeneralSpinGroup) *
            V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y ∈
          V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
      simpa using
        V.fullAdelicCliffordGeneralSpinFundamentalDomainSection_mem y
    exact (hunique gamma hgamma).trans (hunique 1 hone).symm
  · rintro rfl
    simpa [fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection]
      using V.fullAdelicCliffordGeneralSpinFundamentalDomainSection_mem y

/-- The identity-translated section measure restricts to the section lift on
the fundamental domain. -/
theorem restrict_map_rationalTranslateFundamentalSection_one
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    (Measure.map
        (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection 1)
        μ).restrict
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain =
      V.fullAdelicCliffordGeneralSpinFundamentalSectionLift μ := by
  ext A hA
  rw [Measure.restrict_apply hA,
    Measure.map_apply
      (V.measurable_fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
        1)
      (hA.inter
        V.measurableSet_fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain),
    fullAdelicCliffordGeneralSpinFundamentalSectionLift,
    Measure.map_apply
      V.measurable_fullAdelicCliffordGeneralSpinFundamentalDomainSection hA]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff,
    fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection]
  simp [V.fullAdelicCliffordGeneralSpinFundamentalDomainSection_mem]

/-- Every nonidentity-translated section measure restricts to zero on the
fundamental domain. -/
theorem restrict_map_rationalTranslateFundamentalSection_of_ne_one
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (hgamma : gamma ≠ 1) :
    (Measure.map
        (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection gamma)
        μ).restrict
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain = 0 := by
  ext A hA
  rw [Measure.restrict_apply hA]
  change
    (Measure.map
      (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection gamma)
      μ)
        (A ∩ V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain) = 0
  rw [Measure.map_apply
    (V.measurable_fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
      gamma)
    (hA.inter
      V.measurableSet_fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain)]
  have hempty :
      V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection gamma ⁻¹'
          (A ∩ V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain) = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro _ hy
    exact hgamma
      ((V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection_mem_iff
        gamma y).mp hy)
  rw [hempty, measure_empty]

/-- The periodized ambient lift restricts exactly to the original lifted
measure on the fixed fundamental domain. -/
theorem restrict_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ).restrict
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain =
      V.fullAdelicCliffordGeneralSpinFundamentalSectionLift μ := by
  rw [fullAdelicCliffordGeneralSpinPeriodizedQuotientLift,
    Measure.restrict_sum _
      V.measurableSet_fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain]
  ext A hA
  rw [Measure.sum_apply _ hA,
    tsum_eq_single
      (1 : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)]
  · rw [V.restrict_map_rationalTranslateFundamentalSection_one μ]
  · intro gamma hgamma
    rw [V.restrict_map_rationalTranslateFundamentalSection_of_ne_one
      μ gamma hgamma]
    rfl

/-- Periodization cannot annihilate a nonzero quotient measure: its exact
restriction to the fundamental domain still pushes forward to the original
measure. -/
theorem fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_ne_zero
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (hμ : μ ≠ 0) :
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ ≠ 0 := by
  intro hperiodized
  apply hμ
  rw [← V.map_fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalSectionLift μ]
  have hsection :=
    V.restrict_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ
  rw [hperiodized] at hsection
  simpa using congrArg
    (Measure.map V.fullAdelicCliffordGeneralSpinLeftQuotientMap) hsection.symm

end RationalQuadraticSpaceMatrix
