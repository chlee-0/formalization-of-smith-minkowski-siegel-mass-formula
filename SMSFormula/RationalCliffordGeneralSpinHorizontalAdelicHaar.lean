import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteAdelicHaarRegularity
import SMSFormula.RationalCliffordGeneralSpinAdelicProduct

/-!
# Horizontal adelic Haar measure on intrinsic general Spin

The literal product of the fixed real horizontal differential Haar measure and
the coherent finite-adelic horizontal Haar measure is transported through the
intrinsic real--finite continuous multiplicative equivalence.  Its map back is
exactly the defining product, so no Haar-uniqueness scalar enters the adelic
normalization.

No quotient disintegration, vertical comparison, or Tamagawa-volume identity
is asserted here.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance horizontalAdelicProductFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalAdelicProductFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalAdelicProductFullMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalAdelicProductFullBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- The direct product of the fixed real horizontal differential Haar measure
and the coherent finite-adelic horizontal Haar measure. -/
def realFiniteCliffordGeneralSpinHorizontalGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure (V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :=
  V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.prod
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure

theorem realFiniteCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsHaarMeasure V.realFiniteCliffordGeneralSpinHorizontalGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
  letI : Measure.IsHaarMeasure
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  letI : IsLocallyFiniteMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isLocallyFinite
  letI : SigmaFinite
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    sigmaFinite_of_locallyFinite
  letI : SFinite
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure := by
    infer_instance
  letI : SFinite
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
    infer_instance
  unfold realFiniteCliffordGeneralSpinHorizontalGroupMeasure
  exact Measure.prod.instIsHaarMeasure
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure

/-- The horizontal full-adelic measure transported from the literal fixed
real--finite product. -/
def fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure V.FullAdelicCliffordGeneralSpinGroup :=
  Measure.map
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.toHomeomorph
    V.realFiniteCliffordGeneralSpinHorizontalGroupMeasure

/-- Splitting the transported horizontal full-adelic measure recovers exactly
the fixed real differential factor times the directed finite factor. -/
theorem map_fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_realFinite
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.map
        V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph
        V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure =
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.prod
        V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  rw [fullAdelicCliffordGeneralSpinHorizontalGroupMeasure]
  exact MeasurableEquiv.map_map_symm
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toMeasurableEquiv

/-- The horizontal full-adelic measure is Haar at the exact transported
placewise differential scale. -/
theorem fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.realFiniteCliffordGeneralSpinHorizontalGroupMeasure :=
    V.realFiniteCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  unfold fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  exact
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.toMulEquiv.isHaarMeasure_map
      V.realFiniteCliffordGeneralSpinHorizontalGroupMeasure
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.continuous
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.continuous

instance fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isLocallyFinite
    (V : RationalQuadraticSpaceMatrix n) :
    IsLocallyFiniteMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  infer_instance

end RationalQuadraticSpaceMatrix
