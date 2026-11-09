import SMSFormula.RationalCliffordSpinCandidateFullAdelicHaar
import SMSFormula.RationalCliffordSpinCandidateAdelicReferenceQuotientMeasure

/-!
# Coherent quotient scale for the adelic Clifford--Spin candidate

The completed coherent full-adelic Haar measure is a strictly positive finite
scalar multiple of the earlier arbitrary reference Haar measure.  The same
scalar rescales the certified reference quotient measure, preserving the
measurable left Weil identity.

The resulting quotient measure is exactly the pushforward of coherent Haar
restricted to the completed measurable fundamental domain.  Its total mass is
therefore both the scaled reference quotient volume and the coherent Haar mass
of that domain.  The comparison scalar is not evaluated, and no invariant-
differential or Tamagawa normalization is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## General measurable-Weil data and common scaling -/

/-- Ambient and quotient measures on the adelic Spin candidate satisfying the
sound measurable-integrand left Weil formula. -/
structure CliffordSpinCandidateMeasurableWeilMeasureData where
  adelicMeasure : Measure V.FullAdelicCliffordSpinCandidateGroup
  quotientMeasure : Measure V.FullAdelicCliffordSpinCandidateLeftQuotient
  isMeasurableWeilQuotientMeasure :
    IsLeftMeasurableWeilQuotientMeasure
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      adelicMeasure quotientMeasure

namespace CliffordSpinCandidateMeasurableWeilMeasureData

/-- The reference-Haar datum viewed as general adelic Spin measurable-Weil
data. -/
def ofReferenceHaar
    {V : RationalQuadraticSpaceMatrix n}
    (D : V.CliffordSpinCandidateReferenceHaarMeasurableWeilMeasureData) :
    V.CliffordSpinCandidateMeasurableWeilMeasureData where
  adelicMeasure := V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure
  quotientMeasure := D.quotientMeasure
  isMeasurableWeilQuotientMeasure :=
    D.isMeasurableWeilQuotientMeasure

/-- A common finite scalar rescaling preserves the measurable left Weil
formula. -/
theorem isMeasurableWeilQuotientMeasure_smul
    {V : RationalQuadraticSpaceMatrix n}
    (D : V.CliffordSpinCandidateMeasurableWeilMeasureData)
    (c : ℝ≥0) :
    IsLeftMeasurableWeilQuotientMeasure
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      (c • D.adelicMeasure) (c • D.quotientMeasure) where
  lintegral_leftPeriodize_eq f hf := by
    rw [lintegral_smul_measure, lintegral_smul_measure,
      D.isMeasurableWeilQuotientMeasure.lintegral_leftPeriodize_eq f hf]

/-- Simultaneously rescale the ambient and quotient measures by a finite
nonnegative scalar. -/
def smul
    {V : RationalQuadraticSpaceMatrix n}
    (c : ℝ≥0)
    (D : V.CliffordSpinCandidateMeasurableWeilMeasureData) :
    V.CliffordSpinCandidateMeasurableWeilMeasureData where
  adelicMeasure := c • D.adelicMeasure
  quotientMeasure := c • D.quotientMeasure
  isMeasurableWeilQuotientMeasure :=
    D.isMeasurableWeilQuotientMeasure_smul c

/-- The total mass of the measurable-Weil-normalized quotient. -/
def quotientVolumeENNReal
    {V : RationalQuadraticSpaceMatrix n}
    (D : V.CliffordSpinCandidateMeasurableWeilMeasureData) : ℝ≥0∞ :=
  D.quotientMeasure Set.univ

@[simp]
theorem quotientVolumeENNReal_eq
    {V : RationalQuadraticSpaceMatrix n}
    (D : V.CliffordSpinCandidateMeasurableWeilMeasureData) :
    D.quotientVolumeENNReal = D.quotientMeasure Set.univ :=
  rfl

/-- Total quotient mass scales by the same finite scalar as the two measures. -/
@[simp]
theorem quotientVolumeENNReal_smul
    {V : RationalQuadraticSpaceMatrix n}
    (D : V.CliffordSpinCandidateMeasurableWeilMeasureData)
    (c : ℝ≥0) :
    (D.smul c).quotientVolumeENNReal =
      (c : ℝ≥0∞) * D.quotientVolumeENNReal := by
  change (c • D.quotientMeasure) Set.univ =
    (c : ℝ≥0∞) * D.quotientMeasure Set.univ
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply]

end CliffordSpinCandidateMeasurableWeilMeasureData

/-! ## The coherent full-adelic quotient datum -/

/-- The certified reference-Haar datum packaged with its ambient measure. -/
noncomputable def fullAdelicCliffordSpinCandidateReferenceMeasurableWeilData :
    V.CliffordSpinCandidateMeasurableWeilMeasureData :=
  CliffordSpinCandidateMeasurableWeilMeasureData.ofReferenceHaar
    V.fullAdelicCliffordSpinCandidateReferenceHaarMeasurableWeilData

/-- The coherent measurable-Weil datum obtained by applying the exact Haar
comparison scalar simultaneously to the reference ambient and quotient
measures. -/
noncomputable def fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData :
    V.CliffordSpinCandidateMeasurableWeilMeasureData :=
  V.fullAdelicCliffordSpinCandidateReferenceMeasurableWeilData.smul
    V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar

/-- The ambient measure in the rescaled datum is exactly the constructed
coherent full-adelic Haar measure. -/
@[simp]
theorem fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData_adelicMeasure :
    V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.adelicMeasure =
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  change
    V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar •
        V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure =
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure
  exact
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_eq_smul_referenceHaar.symm

/-- The coherent quotient measure is the same scalar multiple of the
certified reference quotient measure. -/
@[simp]
theorem fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData_quotientMeasure :
    V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.quotientMeasure =
      V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar •
        V.fullAdelicCliffordSpinCandidateReferenceHaarMeasurableWeilData.quotientMeasure :=
  rfl

/-- The coherent ambient and quotient measures satisfy the measurable left
Weil formula. -/
theorem fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData_isMeasurableWeil :
    IsLeftMeasurableWeilQuotientMeasure
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure
      V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.quotientMeasure := by
  rw [← V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData_adelicMeasure]
  exact
    V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.isMeasurableWeilQuotientMeasure

/-- The exact periodization identity at the coherent full-adelic Haar scale. -/
theorem lintegral_coherentHaar_leftPeriodize_eq_lintegral
    (f : V.FullAdelicCliffordSpinCandidateGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ X,
        leftPeriodize
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f X
      ∂V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.quotientMeasure =
      ∫⁻ y, f y
        ∂V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
  V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData_isMeasurableWeil
    |>.lintegral_leftPeriodize_eq f hf

/-! ## Fundamental-domain pushforward and total mass -/

/-- The quotient measure obtained by pushing coherent Haar restricted to the
completed measurable fundamental domain. -/
noncomputable def
    fullAdelicCliffordSpinCandidateCoherentFundamentalDomainQuotientMeasure :
    Measure V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  leftQuotientFundamentalDomainMeasure
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure
    V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain

/-- The coherent quotient datum is exactly the fundamental-domain pushforward
of coherent full-adelic Haar. -/
theorem fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData_quotientMeasure_eq_fundamentalDomain :
    V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.quotientMeasure =
      V.fullAdelicCliffordSpinCandidateCoherentFundamentalDomainQuotientMeasure := by
  change
    V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar •
        V.fullAdelicCliffordSpinCandidateReferenceFundamentalDomainQuotientMeasure
          V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain =
      V.fullAdelicCliffordSpinCandidateCoherentFundamentalDomainQuotientMeasure
  unfold
    fullAdelicCliffordSpinCandidateReferenceFundamentalDomainQuotientMeasure
    fullAdelicCliffordSpinCandidateCoherentFundamentalDomainQuotientMeasure
  rw [V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_eq_smul_referenceHaar]
  simp only [leftQuotientFundamentalDomainMeasure_eq_map_restrict,
    Measure.restrict_smul, Measure.map_smul]

/-- The coherent quotient volume is the coherent Haar mass of the completed
measurable fundamental domain. -/
theorem fullAdelicCliffordSpinCandidateCoherentQuotientVolume_eq_domainMass :
    V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.quotientVolumeENNReal =
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain := by
  rw [CliffordSpinCandidateMeasurableWeilMeasureData.quotientVolumeENNReal_eq,
    V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData_quotientMeasure_eq_fundamentalDomain]
  unfold fullAdelicCliffordSpinCandidateCoherentFundamentalDomainQuotientMeasure
  exact
    leftQuotientFundamentalDomainMeasure_univ_map_mspace
      (Gamma := V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup)
      (μG := V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure)
      (F := V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain) rfl

/-- The coherent quotient volume is the explicit comparison scalar times the
reference quotient volume. -/
theorem fullAdelicCliffordSpinCandidateCoherentQuotientVolume_eq_smul_reference :
    V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.quotientVolumeENNReal =
      (V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar : ℝ≥0∞) *
        V.fullAdelicCliffordSpinCandidateReferenceHaarMeasurableWeilData.referenceQuotientVolumeENNReal := by
  change
    (V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar •
        V.fullAdelicCliffordSpinCandidateReferenceHaarMeasurableWeilData.quotientMeasure)
        Set.univ = _
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  rfl

end RationalQuadraticSpaceMatrix
