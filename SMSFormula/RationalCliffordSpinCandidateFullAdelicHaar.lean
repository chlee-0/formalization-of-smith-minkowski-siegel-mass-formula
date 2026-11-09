import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicHaar
import SMSFormula.RationalCliffordSpinCandidateAdelicHaarPrecursor
import SMSFormula.RationalCliffordSpinCandidateAdelicProduct
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Full-adelic Haar measure for the Clifford--Spin candidate

The completed real chart-glued Haar measure and coherent finite-adelic Haar
measure have a literal product.  Transport through the verified real/finite
continuous multiplicative equivalence gives a full-adelic Haar measure whose
map back is exactly that product.

Haar uniqueness then compares this constructed scale with the pre-existing
arbitrary reference Haar measure by the explicit positive finite
`haarScalarFactor`.  The scalar is not evaluated and is not identified with
the rational invariant-top-form normalization.  No quotient-volume or
Tamagawa statement is asserted.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 600000

local instance fullAdelicSpinProductFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance fullAdelicSpinProductFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

/-! ## The literal real/finite product -/

/-- The direct product of the real chart-glued Spin Haar measure and the
coherent finite-adelic Spin Haar measure. -/
noncomputable def realFiniteCliffordSpinCandidateCoherentGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure
      (V.RealCliffordSpinCandidateGroup ×
        V.FiniteAdelicCliffordSpinCandidateGroup) :=
  V.realCliffordSpinCandidateChartGluedMeasure.prod
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure

/-- The literal real/finite Spin product is sigma-finite. -/
theorem realFiniteCliffordSpinCandidateCoherentGroupMeasure_sigmaFinite
    (V : RationalQuadraticSpaceMatrix n) :
    SigmaFinite V.realFiniteCliffordSpinCandidateCoherentGroupMeasure := by
  letI : IsLocallyFiniteMeasure
      V.realCliffordSpinCandidateChartGluedMeasure :=
    V.realCliffordSpinCandidateChartGluedMeasure_isLocallyFinite
  letI : SigmaFinite V.realCliffordSpinCandidateChartGluedMeasure :=
    sigmaFinite_of_locallyFinite
  letI : SigmaFinite
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isSigmaFinite
  unfold realFiniteCliffordSpinCandidateCoherentGroupMeasure
  infer_instance

/-- The literal real/finite Spin product is Haar. -/
theorem realFiniteCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsHaarMeasure
      V.realFiniteCliffordSpinCandidateCoherentGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.realCliffordSpinCandidateChartGluedMeasure :=
    V.realCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
  letI : Measure.IsHaarMeasure
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
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
  exact Measure.prod.instIsHaarMeasure
    V.realCliffordSpinCandidateChartGluedMeasure
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure

/-! ## Transport to the full-adelic carrier -/

/-- The coherent full-adelic Spin measure obtained from the exact real/finite
product normalization. -/
noncomputable def fullAdelicCliffordSpinCandidateCoherentGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure V.FullAdelicCliffordSpinCandidateGroup :=
  Measure.map
    V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm.toHomeomorph
    V.realFiniteCliffordSpinCandidateCoherentGroupMeasure

/-- Mapping the coherent full-adelic Spin measure through the real/finite
split recovers the literal product exactly. -/
theorem map_fullAdelicCliffordSpinCandidateCoherentGroupMeasure_realFinite
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.map
        V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph
        V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure =
      V.realCliffordSpinCandidateChartGluedMeasure.prod
        V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  rw [fullAdelicCliffordSpinCandidateCoherentGroupMeasure]
  exact
    MeasurableEquiv.map_map_symm
      V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toMeasurableEquiv

/-- The coherent full-adelic Spin measure is sigma-finite. -/
theorem fullAdelicCliffordSpinCandidateCoherentGroupMeasure_sigmaFinite
    (V : RationalQuadraticSpaceMatrix n) :
    SigmaFinite V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  letI : SigmaFinite
      V.realFiniteCliffordSpinCandidateCoherentGroupMeasure :=
    V.realFiniteCliffordSpinCandidateCoherentGroupMeasure_sigmaFinite
  unfold fullAdelicCliffordSpinCandidateCoherentGroupMeasure
  exact
    V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm.toHomeomorph.toMeasurableEquiv.sigmaFinite_map

/-- The coherent full-adelic Spin measure is Haar. -/
theorem fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsHaarMeasure
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.realFiniteCliffordSpinCandidateCoherentGroupMeasure :=
    V.realFiniteCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
  unfold fullAdelicCliffordSpinCandidateCoherentGroupMeasure
  exact
    V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm.toMulEquiv.isHaarMeasure_map
      V.realFiniteCliffordSpinCandidateCoherentGroupMeasure
      V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm.continuous
      V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.continuous

/-- Haar finiteness on compact sets and local compactness make the coherent
full-adelic Spin measure locally finite. -/
instance fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isLocallyFinite
    (V : RationalQuadraticSpaceMatrix n) :
    IsLocallyFiniteMeasure
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
  infer_instance

/-- Left invariance of the coherent full-adelic Spin measure. -/
theorem fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulLeftInvariant
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
  infer_instance

/-- The coherent full-adelic Spin measure is regular. -/
theorem fullAdelicCliffordSpinCandidateCoherentGroupMeasure_regular
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.Regular V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
  infer_instance

/-! ## Explicit comparison with the arbitrary reference Haar scale -/

/-- The positive finite scalar carrying the arbitrary reference Haar scale to
the coherent real/finite product scale.  It is deliberately left unevaluated. -/
noncomputable def fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar
    (V : RationalQuadraticSpaceMatrix n) : ℝ≥0 := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
  exact Measure.haarScalarFactor
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure
    V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure

/-- The coherent-to-reference Haar comparison scalar is strictly positive. -/
theorem fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar_pos
    (V : RationalQuadraticSpaceMatrix n) :
    0 < V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
  unfold fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

/-- Haar uniqueness identifies the coherent full-adelic measure with the
explicit positive finite scalar multiple of the arbitrary reference Haar
measure. -/
theorem fullAdelicCliffordSpinCandidateCoherentGroupMeasure_eq_smul_referenceHaar
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure =
      V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar •
        V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
  letI : IsFiniteMeasureOnCompacts
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
    infer_instance
  letI : Measure.IsMulLeftInvariant
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isMulLeftInvariant
  exact Measure.isMulLeftInvariant_eq_smul
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure
    V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure

end RationalQuadraticSpaceMatrix
