import SMSFormula.MeasureInversionTransport
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicUnimodular
import SMSFormula.RationalCliffordSpinCandidateFullAdelicHaar

/-!
# Unimodularity of the full-adelic Clifford--Spin candidate measure

The real chart-glued measure and the coherent finite-adelic measure are both
invariant under inversion.  Their product is therefore inversion invariant,
and this property transports through the verified real--finite continuous
multiplicative equivalence defining the full-adelic measure.  Left invariance
then gives right invariance at the same coherent scale.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 300000

local instance fullAdelicSpinUnimodularFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance fullAdelicSpinUnimodularFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

/-- The literal real--finite Spin product is invariant under inversion. -/
instance realFiniteCliffordSpinCandidateCoherentGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsInvInvariant
      V.realFiniteCliffordSpinCandidateCoherentGroupMeasure := by
  letI : IsLocallyFiniteMeasure
      V.realCliffordSpinCandidateChartGluedMeasure :=
    V.realCliffordSpinCandidateChartGluedMeasure_isLocallyFinite
  letI : SigmaFinite V.realCliffordSpinCandidateChartGluedMeasure :=
    sigmaFinite_of_locallyFinite
  letI : SigmaFinite
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isSigmaFinite
  letI : SFinite V.realCliffordSpinCandidateChartGluedMeasure := by
    infer_instance
  letI : SFinite
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
    infer_instance
  unfold realFiniteCliffordSpinCandidateCoherentGroupMeasure
  exact Measure.isInvInvariant_prod
    V.realCliffordSpinCandidateChartGluedMeasure
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure

/-- The coherent full-adelic Spin measure is invariant under inversion. -/
instance fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsInvInvariant
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  unfold fullAdelicCliffordSpinCandidateCoherentGroupMeasure
  exact Measure.isInvInvariant_map_of_commutes
    V.realFiniteCliffordSpinCandidateCoherentGroupMeasure
    V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm
    V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm.continuous.measurable
    (fun x =>
      V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm.map_inv x)

/-- Consequently the coherent full-adelic Spin measure is globally right
invariant. -/
theorem fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isMulRightInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulRightInvariant
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  letI : Measure.IsMulLeftInvariant
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isMulLeftInvariant
  exact Measure.isMulRightInvariant_of_isInvInvariant
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure

end RationalQuadraticSpaceMatrix
