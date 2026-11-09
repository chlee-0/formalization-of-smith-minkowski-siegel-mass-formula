import SMSFormula.MeasureInversionTransport
import SMSFormula.RationalCliffordGeneralSpinHorizontalAdelicHaar
import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteAdelicUnimodular

/-!
# Unimodularity of horizontal full-adelic intrinsic general Spin Haar

The real horizontal differential measure and the coherent finite-adelic
horizontal measure are both invariant under inversion.  Their literal product
is therefore inversion invariant, and this property transports through the
real--finite continuous multiplicative equivalence defining the full-adelic
measure.  Left invariance then gives right invariance at the same fixed local
differential scale.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance horizontalAdelicUnimodularFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup := borel _

local instance horizontalAdelicUnimodularFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup := ⟨rfl⟩

local instance horizontalAdelicUnimodularFullMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup := borel _

local instance horizontalAdelicUnimodularFullBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FullAdelicCliffordGeneralSpinGroup := ⟨rfl⟩

/-- The literal real--finite horizontal product is invariant under
componentwise inversion. -/
instance realFiniteCliffordGeneralSpinHorizontalGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsInvInvariant
      V.realFiniteCliffordGeneralSpinHorizontalGroupMeasure := by
  letI : IsLocallyFiniteMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isLocallyFinite
  letI : SigmaFinite
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    sigmaFinite_of_locallyFinite
  letI : SigmaFinite
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isSigmaFinite
  letI : SFinite
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure := by
    infer_instance
  letI : SFinite
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
    infer_instance
  unfold realFiniteCliffordGeneralSpinHorizontalGroupMeasure
  exact Measure.isInvInvariant_prod
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure

/-- The fixed horizontal full-adelic `GSpin` measure is inversion invariant. -/
instance fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsInvInvariant
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  unfold fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  exact Measure.isInvInvariant_map_of_commutes
    V.realFiniteCliffordGeneralSpinHorizontalGroupMeasure
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.continuous.measurable
    (fun x ↦
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.map_inv x)

/-- Consequently the fixed horizontal full-adelic measure is globally right
invariant at exactly the same differential scale. -/
theorem fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isMulRightInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulRightInvariant
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  letI : Measure.IsMulLeftInvariant
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    (V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure).toIsMulLeftInvariant
  exact Measure.isMulRightInvariant_of_isInvInvariant
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure

@[simp]
theorem fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_inv
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.inv =
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
  Measure.inv_eq_self _

end RationalQuadraticSpaceMatrix
