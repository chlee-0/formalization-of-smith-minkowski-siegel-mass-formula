import SMSFormula.RationalIdeleClassTopology
import SMSFormula.RationalIdeleClassLogSection
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar measure on rational idele classes

The literal rational idele-class quotient is locally compact Hausdorff,
so it carries a genuine Haar measure.  This file fixes Mathlib's reference
Haar scale and defines the one-dimensional logarithmic cutoff integral used
on both sides of the crossed `GSpin` comparison.  No numerical normalization
or Tamagawa assertion is imposed.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

/-- Mathlib's reference Haar measure on the literal rational idele-class
group.  Its scale is intentionally left arbitrary because the same measure
occurs in both crossed evaluations. -/
noncomputable def rationalIdeleClassHaarMeasure :
    Measure RationalIdeleClassGroup :=
  Measure.haar

noncomputable instance rationalIdeleClassHaarMeasureIsHaarMeasure :
    Measure.IsHaarMeasure rationalIdeleClassHaarMeasure := by
  unfold rationalIdeleClassHaarMeasure
  infer_instance

noncomputable instance rationalIdeleClassHaarMeasureIsMulLeftInvariant :
    Measure.IsMulLeftInvariant rationalIdeleClassHaarMeasure := by
  infer_instance

theorem rationalIdeleClassHaarMeasure_ne_zero :
    rationalIdeleClassHaarMeasure ≠ 0 := by
  intro hzero
  have huniv : rationalIdeleClassHaarMeasure Set.univ ≠ 0 :=
    isOpen_univ.measure_ne_zero rationalIdeleClassHaarMeasure Set.univ_nonempty
  rw [hzero] at huniv
  exact huniv rfl

noncomputable instance rationalIdeleClassHaarMeasureSigmaFinite :
    SigmaFinite rationalIdeleClassHaarMeasure := by
  unfold rationalIdeleClassHaarMeasure Measure.haar
  infer_instance

/-- The common nonnegative cutoff integral in the logarithmic idele-class
coordinate. -/
noncomputable def rationalIdeleClassLogCutoffLIntegral
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ c : RationalIdeleClassGroup,
    f (rationalIdeleClassLogModule c) ∂rationalIdeleClassHaarMeasure

end RationalQuadraticSpaceMatrix
