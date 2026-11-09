import SMSFormula.RationalCliffordGeneralSpinAdelicReferenceQuotientMeasure
import SMSFormula.AdelicMeasurableWeilQuotientUniqueness

/-!
# Scalar normalization of the adelic general-Spin quotient

The certified reference-Haar quotient datum can be rescaled simultaneously
on the ambient group and rational quotient.  More importantly, the exact
measurable fundamental domain makes this scaling forced: any measurable-Weil
datum whose ambient `GSpin` measure is `c` times reference Haar has quotient
measure exactly `c` times the certified reference quotient measure.

Thus a future horizontal or vertical differential construction only has to
identify its ambient Haar scalar.  It cannot choose an independent quotient
scalar.  No differential measure, crossed disintegration, or cutoff equality
is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## General measurable-Weil data and common scaling -/

/-- Ambient and quotient measures on adelic intrinsic general Spin satisfying
the sound measurable-integrand left Weil formula. -/
structure CliffordGeneralSpinMeasurableWeilMeasureData where
  adelicMeasure : Measure V.FullAdelicCliffordGeneralSpinGroup
  quotientMeasure : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient
  isMeasurableWeilQuotientMeasure :
    IsLeftMeasurableWeilQuotientMeasure
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      adelicMeasure quotientMeasure

namespace CliffordGeneralSpinMeasurableWeilMeasureData

/-- Package certified reference-Haar quotient data with its ambient measure. -/
def ofReferenceHaar
    {V : RationalQuadraticSpaceMatrix n}
    (D : V.CliffordGeneralSpinReferenceHaarMeasurableWeilMeasureData) :
    V.CliffordGeneralSpinMeasurableWeilMeasureData where
  adelicMeasure := V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure
  quotientMeasure := D.quotientMeasure
  isMeasurableWeilQuotientMeasure :=
    D.isMeasurableWeilQuotientMeasure

/-- A common finite scalar rescaling preserves the measurable left Weil
formula. -/
theorem isMeasurableWeilQuotientMeasure_smul
    {V : RationalQuadraticSpaceMatrix n}
    (D : V.CliffordGeneralSpinMeasurableWeilMeasureData)
    (c : ℝ≥0) :
    IsLeftMeasurableWeilQuotientMeasure
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      (c • D.adelicMeasure) (c • D.quotientMeasure) where
  lintegral_leftPeriodize_eq f hf := by
    rw [lintegral_smul_measure, lintegral_smul_measure,
      D.isMeasurableWeilQuotientMeasure.lintegral_leftPeriodize_eq f hf]

/-- Simultaneously rescale the ambient and quotient measures. -/
def smul
    {V : RationalQuadraticSpaceMatrix n}
    (c : ℝ≥0)
    (D : V.CliffordGeneralSpinMeasurableWeilMeasureData) :
    V.CliffordGeneralSpinMeasurableWeilMeasureData where
  adelicMeasure := c • D.adelicMeasure
  quotientMeasure := c • D.quotientMeasure
  isMeasurableWeilQuotientMeasure :=
    D.isMeasurableWeilQuotientMeasure_smul c

/-- The total mass of a general-Spin measurable-Weil quotient datum. -/
def quotientVolumeENNReal
    {V : RationalQuadraticSpaceMatrix n}
    (D : V.CliffordGeneralSpinMeasurableWeilMeasureData) : ℝ≥0∞ :=
  D.quotientMeasure Set.univ

@[simp]
theorem quotientVolumeENNReal_smul
    {V : RationalQuadraticSpaceMatrix n}
    (D : V.CliffordGeneralSpinMeasurableWeilMeasureData)
    (c : ℝ≥0) :
    (D.smul c).quotientVolumeENNReal =
      (c : ℝ≥0∞) * D.quotientVolumeENNReal := by
  change (c • D.quotientMeasure) Set.univ =
    (c : ℝ≥0∞) * D.quotientMeasure Set.univ
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply]

end CliffordGeneralSpinMeasurableWeilMeasureData

/-! ## The certified reference datum -/

/-- The certified reference-Haar datum packaged together with its ambient
measure. -/
noncomputable def fullAdelicCliffordGeneralSpinReferenceMeasurableWeilData :
    V.CliffordGeneralSpinMeasurableWeilMeasureData :=
  CliffordGeneralSpinMeasurableWeilMeasureData.ofReferenceHaar
    V.fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData

@[simp]
theorem fullAdelicCliffordGeneralSpinReferenceMeasurableWeilData_adelicMeasure :
    V.fullAdelicCliffordGeneralSpinReferenceMeasurableWeilData.adelicMeasure =
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure :=
  rfl

@[simp]
theorem fullAdelicCliffordGeneralSpinReferenceMeasurableWeilData_quotientMeasure :
    V.fullAdelicCliffordGeneralSpinReferenceMeasurableWeilData.quotientMeasure =
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData.quotientMeasure :=
  rfl

/-! ## The ambient scalar forces the quotient scalar -/

/-- Every measurable-Weil quotient measure is the pushforward of its ambient
measure restricted to the fixed exact measurable transversal. -/
theorem CliffordGeneralSpinMeasurableWeilMeasureData.quotientMeasure_eq_fundamentalDomain
    (D : V.CliffordGeneralSpinMeasurableWeilMeasureData) :
    D.quotientMeasure =
      leftQuotientFundamentalDomainMeasure
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        D.adelicMeasure
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
  letI : Countable
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
  exact
    D.isMeasurableWeilQuotientMeasure.eq_leftQuotientFundamentalDomainMeasure
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup rfl
      V.measurableSet_fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
      V.existsUnique_rationalGeneralSpinDiagonal_mul_mem_measurableFundamentalDomain

/-- If the ambient measure of a measurable-Weil datum is `c` times reference
Haar, its quotient measure is forced to be `c` times the certified common
reference quotient measure. -/
theorem CliffordGeneralSpinMeasurableWeilMeasureData.quotientMeasure_eq_smul_reference_of_adelicMeasure_eq
    (D : V.CliffordGeneralSpinMeasurableWeilMeasureData)
    (c : ℝ≥0)
    (hD : D.adelicMeasure =
      c • V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure) :
    D.quotientMeasure =
      c •
        V.fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData.quotientMeasure := by
  rw [D.quotientMeasure_eq_fundamentalDomain V, hD]
  change
    leftQuotientFundamentalDomainMeasure
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        (c • V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure)
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain =
      c •
        leftQuotientFundamentalDomainMeasure
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure
          V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
  simp only [leftQuotientFundamentalDomainMeasure_eq_map_restrict,
    Measure.restrict_smul, Measure.map_smul]

/-- The corresponding total quotient volume has the same forced scalar. -/
theorem CliffordGeneralSpinMeasurableWeilMeasureData.quotientVolumeENNReal_eq_smul_reference_of_adelicMeasure_eq
    (D : V.CliffordGeneralSpinMeasurableWeilMeasureData)
    (c : ℝ≥0)
    (hD : D.adelicMeasure =
      c • V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure) :
    D.quotientVolumeENNReal =
      (c : ℝ≥0∞) *
        V.fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData.referenceQuotientVolumeENNReal := by
  change D.quotientMeasure Set.univ =
    (c : ℝ≥0∞) *
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData.quotientMeasure
        Set.univ
  rw [D.quotientMeasure_eq_smul_reference_of_adelicMeasure_eq V c hD,
    Measure.smul_apply, Measure.nnreal_smul_coe_apply]

end RationalQuadraticSpaceMatrix
