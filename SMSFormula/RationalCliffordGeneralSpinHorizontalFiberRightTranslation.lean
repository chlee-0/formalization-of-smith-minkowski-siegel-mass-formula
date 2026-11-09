import SMSFormula.RationalCliffordGeneralSpinHorizontalQuotientBind
import SMSFormula.RationalCliffordGeneralSpinVerticalSpecialOrthogonalProjection

/-!
# Right translation of horizontal general-Spin fiber Haar

Right multiplication on the rational adelic `GSpin` quotient commutes with
the central idele-class action.  Consequently it carries the literal Haar
measure on one horizontal torsor to the Haar measure on the translated
torsor.  After measurable descent, the same identity holds for the genuine
`SO`-indexed fiber kernel.

This is an equivariance theorem for the already fixed independently scaled
idele-class Haar measure.  It neither compares that scale with the horizontal
differential quotient nor asserts a quotient disintegration.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Central idele-class translation commutes with genuine quotient right
multiplication. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientRightMul_scalarAction
    (x : V.FullAdelicCliffordGeneralSpinGroup)
    (c : RationalIdeleClassGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x
        (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          c z) =
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient c
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x z) := by
  induction c using QuotientGroup.induction_on with
  | _ a =>
    induction z using Quot.inductionOn with
    | _ y =>
      change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
          ((CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele a * y) * x) =
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele a * (y * x))
      rw [mul_assoc]

/-- Right multiplication pushes the Haar measure on a horizontal torsor to
the Haar measure on the translated torsor. -/
theorem map_horizontalFiberHaarMeasure_rightMul
    (x : V.FullAdelicCliffordGeneralSpinGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Measure.map (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)
        (V.horizontalFiberHaarMeasure z) =
      V.horizontalFiberHaarMeasure
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x z) := by
  rw [horizontalFiberHaarMeasure, horizontalFiberHaarMeasure]
  rw [Measure.map_map
    (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)
    (V.measurable_rationalIdeleClassOrbitMap z)]
  apply congrArg (fun f : RationalIdeleClassGroup →
      V.FullAdelicCliffordGeneralSpinLeftQuotient =>
    Measure.map f rationalIdeleClassHaarMeasure)
  funext c
  exact V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul_scalarAction x c z

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The descended `SO`-indexed fiber kernel is equivariant for simultaneous
right translation on its base and total quotient. -/
theorem map_horizontalFiberHaarKernelAtSO_rightMul
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    Measure.map
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          x)
        (L.horizontalFiberHaarKernelAtSO inst q) =
      L.horizontalFiberHaarKernelAtSO inst
        (L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientRightMul
          (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
            x) q) := by
  let V := L.rationalQuadraticSpaceMatrix
  let hsurj :=
    fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L
  let z := V.horizontalFiberHaarKernelLift hsurj q
  rw [L.horizontalFiberHaarKernelAtSO_apply,
    L.horizontalFiberHaarKernelAtSO_apply]
  unfold RationalQuadraticSpaceMatrix.horizontalFiberHaarMeasureAtSO
  rw [V.map_horizontalFiberHaarMeasure_rightMul]
  apply V.horizontalFiberHaarMeasure_eq_of_sameSO
    (z := V.horizontalFiberHaarKernelLift hsurj
      (V.fullAdelicSpecialOrthogonalLeftQuotientRightMul
        (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x) q))
    (w := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x
      (V.horizontalFiberHaarKernelLift hsurj q))
  rw [V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_rightMul]
  rw [V.horizontalFiberHaarKernelLift_spec hsurj q,
    V.horizontalFiberHaarKernelLift_spec hsurj]

end PositiveDefiniteIntegralLattice
