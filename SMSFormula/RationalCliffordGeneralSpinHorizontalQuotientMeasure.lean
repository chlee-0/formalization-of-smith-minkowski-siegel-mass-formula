import SMSFormula.RationalCliffordGeneralSpinHorizontalAdelicHaar
import SMSFormula.RationalCliffordGeneralSpinAdelicQuotientNormalization

/-!
# Horizontal normalization of the common adelic general-Spin quotient

The full horizontal differential measure is a genuine Haar measure on
intrinsic adelic `GSpin`.  Haar uniqueness supplies its exact positive finite
scalar relative to the already certified reference Haar measure.  Scaling the
certified measurable-Weil quotient datum by that same scalar therefore gives a
measurable-Weil datum whose ambient measure is literally the horizontal
differential measure.

This closes the ambient-to-quotient scalar bridge.  It does not identify
the resulting quotient measure with the iterated `SO`/idele-class fiber
measure, compare the vertical kernel, or evaluate a cutoff.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The positive finite scalar carrying reference adelic `GSpin` Haar to the
fixed horizontal differential normalization. -/
noncomputable def
    fullAdelicCliffordGeneralSpinHorizontalToReferenceHaarScalar
    (V : RationalQuadraticSpaceMatrix n) : ℝ≥0 := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  exact Measure.haarScalarFactor
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
    V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure

/-- The horizontal-to-reference Haar scalar is strictly positive. -/
theorem fullAdelicCliffordGeneralSpinHorizontalToReferenceHaarScalar_pos
    (V : RationalQuadraticSpaceMatrix n) :
    0 < V.fullAdelicCliffordGeneralSpinHorizontalToReferenceHaarScalar := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  unfold fullAdelicCliffordGeneralSpinHorizontalToReferenceHaarScalar
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

/-- Haar uniqueness compares the actual horizontal differential measure with
the certified reference Haar measure at the explicit scalar above. -/
theorem fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_eq_smul_referenceHaar
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure =
      V.fullAdelicCliffordGeneralSpinHorizontalToReferenceHaarScalar •
        V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  letI : SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology
  letI : IsFiniteMeasureOnCompacts
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
    infer_instance
  letI : Measure.IsMulLeftInvariant
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
    infer_instance
  exact Measure.isMulLeftInvariant_eq_smul
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
    V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure

/-- The common measurable-Weil quotient datum at the literal horizontal
differential ambient scale. -/
noncomputable def
    fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
    (V : RationalQuadraticSpaceMatrix n) :
    V.CliffordGeneralSpinMeasurableWeilMeasureData where
  adelicMeasure := V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  quotientMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalToReferenceHaarScalar •
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData.quotientMeasure
  isMeasurableWeilQuotientMeasure := by
    rw [V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_eq_smul_referenceHaar]
    exact
      V.fullAdelicCliffordGeneralSpinReferenceMeasurableWeilData
        |>.isMeasurableWeilQuotientMeasure_smul
          V.fullAdelicCliffordGeneralSpinHorizontalToReferenceHaarScalar

@[simp]
theorem fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData_adelicMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.adelicMeasure =
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
  rfl

@[simp]
theorem fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData_quotientMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure =
      V.fullAdelicCliffordGeneralSpinHorizontalToReferenceHaarScalar •
        V.fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData.quotientMeasure :=
  rfl

/-- The horizontally normalized common quotient measure is the pushforward of
the actual horizontal Haar measure restricted to the fixed exact transversal. -/
theorem
    fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData_quotientMeasure_eq_fundamentalDomain
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure =
      leftQuotientFundamentalDomainMeasure
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain :=
  V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
    |>.quotientMeasure_eq_fundamentalDomain V

/-- Consequently the common horizontal quotient volume is literally the
horizontal Haar mass of the fixed exact transversal. -/
theorem fullAdelicCliffordGeneralSpinHorizontalQuotientVolumeENNReal_eq_domainMass
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientVolumeENNReal =
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
  rw [CliffordGeneralSpinMeasurableWeilMeasureData.quotientVolumeENNReal,
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData_quotientMeasure_eq_fundamentalDomain]
  exact leftQuotientFundamentalDomainMeasure_univ_map_mspace
    (Gamma := V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (μG := V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)
    (F := V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain) rfl

/-- The horizontal quotient volume carries exactly the same scalar as its
ambient Haar measure; no independent quotient normalization is available. -/
theorem fullAdelicCliffordGeneralSpinHorizontalQuotientVolumeENNReal_eq
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientVolumeENNReal =
      (V.fullAdelicCliffordGeneralSpinHorizontalToReferenceHaarScalar : ℝ≥0∞) *
        (V.fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData
          ).referenceQuotientVolumeENNReal := by
  exact
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
      |>.quotientVolumeENNReal_eq_smul_reference_of_adelicMeasure_eq V
        V.fullAdelicCliffordGeneralSpinHorizontalToReferenceHaarScalar
        V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_eq_smul_referenceHaar

end RationalQuadraticSpaceMatrix
