import SMSFormula.RationalCliffordGeneralSpinHorizontalFiberHaarMeasure
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# The measurable horizontal idele-class Haar kernel

The joint central idele-class action on the rational adelic `GSpin`
quotient is continuous.  Mapping the product of the identity kernel and the
constant rational-idele-class Haar kernel through this action therefore gives
a measurable kernel on the quotient.  Its value at `z` is exactly the
Haar measure on the horizontal torsor through `z`, and it
is constant when two origins have the same `SO` quotient image.

This is the section-free measurable kernel needed before descent to an
`SO`-indexed kernel.  No measurable section of the horizontal quotient,
iterated disintegration, or quotient-measure equality is asserted here.
-/

noncomputable section

open MeasureTheory
open scoped ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The central idele-class action with the quotient origin as first
coordinate, matching the product-kernel convention. -/
def horizontalIdeleClassJointOrbitParametrization :
    V.FullAdelicCliffordGeneralSpinLeftQuotient × RationalIdeleClassGroup →
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  fun p =>
    V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
      p.2 p.1

theorem continuous_horizontalIdeleClassJointOrbitParametrization :
    Continuous V.horizontalIdeleClassJointOrbitParametrization := by
  exact
    V.continuous_rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient.comp
      (continuous_snd.prodMk continuous_fst)

/-- The measurable kernel assigning to each quotient origin the Haar measure
on its full horizontal idele-class torsor. -/
noncomputable def horizontalFiberHaarKernel :
    ProbabilityTheory.Kernel
      V.FullAdelicCliffordGeneralSpinLeftQuotient
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  ProbabilityTheory.Kernel.map
    (ProbabilityTheory.Kernel.id ×ₖ
      ProbabilityTheory.Kernel.const
        V.FullAdelicCliffordGeneralSpinLeftQuotient
        rationalIdeleClassHaarMeasure)
    V.horizontalIdeleClassJointOrbitParametrization

@[simp]
theorem horizontalFiberHaarKernel_apply
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.horizontalFiberHaarKernel z = V.horizontalFiberHaarMeasure z := by
  ext A hA
  rw [horizontalFiberHaarKernel,
    ProbabilityTheory.Kernel.map_apply'
      _ V.continuous_horizontalIdeleClassJointOrbitParametrization.measurable
      _ hA,
    ProbabilityTheory.Kernel.id_prod_apply' _ z
      (V.continuous_horizontalIdeleClassJointOrbitParametrization.measurable hA),
    ProbabilityTheory.Kernel.const_apply,
    horizontalFiberHaarMeasure,
    Measure.map_apply
      (V.measurable_rationalIdeleClassOrbitMap z) hA]
  rfl

/-- The quotient-origin-indexed horizontal fiber measures form a measurable
measure-valued map. -/
theorem measurable_horizontalFiberHaarMeasure :
    Measurable V.horizontalFiberHaarMeasure := by
  have hkernel : Measurable (fun z => V.horizontalFiberHaarKernel z) :=
    V.horizontalFiberHaarKernel.measurable
  simpa only [V.horizontalFiberHaarKernel_apply] using hkernel

/-- The measurable kernel is constant on the exact fibers of the horizontal
map to the rational `SO` quotient. -/
theorem horizontalFiberHaarKernel_eq_of_sameSO
    {z w : V.FullAdelicCliffordGeneralSpinLeftQuotient}
    (hzw :
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal w =
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z) :
    V.horizontalFiberHaarKernel w = V.horizontalFiberHaarKernel z := by
  rw [V.horizontalFiberHaarKernel_apply, V.horizontalFiberHaarKernel_apply]
  exact V.horizontalFiberHaarMeasure_eq_of_sameSO hzw

/-- The kernel value vanishes on measurable sets disjoint from its exact
horizontal `SO` fiber. -/
theorem horizontalFiberHaarKernel_apply_eq_zero_of_disjoint_fiber
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient)
    {s : Set V.FullAdelicCliffordGeneralSpinLeftQuotient}
    (hs : MeasurableSet s)
    (hdisj : Disjoint s
      {w | V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal w =
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z}) :
    V.horizontalFiberHaarKernel z s = 0 := by
  rw [V.horizontalFiberHaarKernel_apply]
  exact
    V.horizontalFiberHaarMeasure_apply_eq_zero_of_disjoint_fiber z hs hdisj

/-! ## Exact descent interface -/

/-- A chosen origin above an `SO` quotient point, used only to define the
representative-independent target-indexed fiber measure. -/
noncomputable def horizontalFiberHaarKernelLift
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (q : V.FullAdelicSpecialOrthogonalLeftQuotient) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Classical.choose (hsurj q)

@[simp]
theorem horizontalFiberHaarKernelLift_spec
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (q : V.FullAdelicSpecialOrthogonalLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
        (V.horizontalFiberHaarKernelLift hsurj q) = q :=
  Classical.choose_spec (hsurj q)

/-- The horizontal Haar measure indexed by an `SO` quotient point.  Fiber
translation invariance makes this independent of the chosen origin. -/
noncomputable def horizontalFiberHaarMeasureAtSO
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (q : V.FullAdelicSpecialOrthogonalLeftQuotient) :
    Measure V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  V.horizontalFiberHaarMeasure (V.horizontalFiberHaarKernelLift hsurj q)

/-- Pulling the `SO`-indexed family back to any actual `GSpin` quotient origin
recovers its genuine idele-class orbit Haar measure. -/
theorem horizontalFiberHaarMeasureAtSO_image
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.horizontalFiberHaarMeasureAtSO hsurj
        (V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z) =
      V.horizontalFiberHaarMeasure z := by
  unfold horizontalFiberHaarMeasureAtSO
  exact V.horizontalFiberHaarMeasure_eq_of_sameSO
    (V.horizontalFiberHaarKernelLift_spec hsurj _)

/-- The pullback of the target-indexed family is exactly the measurable
source-indexed family.  Descending this measurability now requires only the
measurable-quotient property of the horizontal map. -/
theorem horizontalFiberHaarMeasureAtSO_comp_horizontalMap
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal) :
    V.horizontalFiberHaarMeasureAtSO hsurj ∘
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal =
      V.horizontalFiberHaarMeasure := by
  funext z
  exact V.horizontalFiberHaarMeasureAtSO_image hsurj z

theorem measurable_horizontalFiberHaarMeasureAtSO_comp_horizontalMap
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal) :
    Measurable
      (V.horizontalFiberHaarMeasureAtSO hsurj ∘
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal) := by
  rw [V.horizontalFiberHaarMeasureAtSO_comp_horizontalMap hsurj]
  exact V.measurable_horizontalFiberHaarMeasure

end RationalQuadraticSpaceMatrix
