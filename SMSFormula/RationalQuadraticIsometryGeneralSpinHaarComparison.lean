import SMSFormula.RationalQuadraticIsometryGeneralSpinTopology
import SMSFormula.RationalCliffordGeneralSpinHorizontalAdelicHaar

/-!
# Haar comparison across intrinsic general-Spin presentations

The full-adelic presentation homeomorphism carries the fixed horizontal Haar
measure on the supplied block presentation to a Haar measure on the ambient
presentation.  This file names and certifies the unique positive scalar
relating that pushforward to the ambient fixed horizontal Haar measure.

The scalar is not asserted to be one.  That remaining normalization statement
requires compatibility of the placewise differential measures, not merely
Haar uniqueness or the already proved group homeomorphism.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The pushforward of the block presentation's fixed horizontal full-adelic
measure is itself Haar on the ambient presentation. -/
theorem map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_isHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)) := by
  letI : Measure.IsHaarMeasure
      ((P.blockSpace hx)
        |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) :=
    (P.blockSpace hx)
      |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  exact
    (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).toMulEquiv
      |>.isHaarMeasure_map
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).continuous
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).symm.continuous

/-- The positive finite scalar comparing the transported block horizontal
Haar measure with the fixed ambient horizontal Haar measure. -/
noncomputable def blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar
    (P : V.AnisotropicComplementPresentation x m)
    (hx : V.nativeRationalQuadraticForm x ≠ 0) : ℝ≥0 := by
  letI : Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)) :=
    P.map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_isHaarMeasure hx
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  exact Measure.haarScalarFactor
    (Measure.map
      (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
      ((P.blockSpace hx)
        |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure))
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure

/-- The presentation Haar-comparison scalar is strictly positive. -/
theorem blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_pos
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    0 < P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx := by
  letI : Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)) :=
    P.map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_isHaarMeasure hx
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  unfold blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

/-- Exact Haar comparison under the supplied presentation homeomorphism.
The displayed scalar carries the whole normalization. -/
theorem map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_eq_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx •
        V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  letI : SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology
  letI : Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)) :=
    P.map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_isHaarMeasure hx
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  letI : IsFiniteMeasureOnCompacts
      (Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)) := by
    infer_instance
  letI : Measure.IsMulLeftInvariant
      (Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)) := by
    infer_instance
  exact Measure.isMulLeftInvariant_eq_smul
    (Measure.map
      (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
      ((P.blockSpace hx)
        |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure))
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure

/-- Once the remaining placewise normalization calculation proves the
comparison scalar is one, the fixed full-adelic Haar square commutes
literally. -/
theorem map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_eq_of_scalar_eq_one
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (hscalar :
      P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx = 1) :
    Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  rw [P.map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_eq_smul hx,
    hscalar, one_smul]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
