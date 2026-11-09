import SMSFormula.RationalCliffordGeneralSpinBlockStabilizerVerticalCoefficient
import SMSFormula.RationalCliffordGeneralSpinVerticalFiberQuotientRightTranslation

/-!
# The rational quotient measure on the nonisotropic block stabilizer

The crossed complement fibers are packaged as one
measure on the block rational `GSpin` quotient.  It is the pushforward
of the lower-rank vertical Spin-fiber bind through the certified
complement quotient map.  Its logarithmic cutoff has exactly the lower Spin
Tamagawa coefficient, and it is invariant under every right translation from
the complement `GSpin` group.

This is the base rational stabilizer fiber needed for the one-shell quotient
kernel.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The complement quotient embedding commutes with the existing right
actions on the lower and block rational adelic `GSpin` quotients. -/
theorem fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap_rightMul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (x : W.FullAdelicCliffordGeneralSpinGroup)
    (z : W.FullAdelicCliffordGeneralSpinLeftQuotient) :
    W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap a ha
        (W.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x z) =
      (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele x)
          (W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
            a ha z) := by
  induction z using Quot.inductionOn with
  | _ z =>
      change
        (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientMap
              (W.nonisotropicLastComplementGeneralSpinPoint
                a ha RationalAdele (z * x)) =
          (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientMap
              (W.nonisotropicLastComplementGeneralSpinPoint
                  a ha RationalAdele z *
                W.nonisotropicLastComplementGeneralSpinPoint
                  a ha RationalAdele x)
      congr 1
      exact (W.nonisotropicLastComplementGeneralSpinPointHom
        a ha RationalAdele).map_mul z x

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- The full crossed lower-rank Spin-fiber measure, embedded in the block
rational adelic `GSpin` quotient. -/
noncomputable def nonisotropicLastComplementVerticalSpinFiberBoundMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Measure
      (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinLeftQuotient :=
  Measure.map
    (L.rationalQuadraticSpaceMatrix.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
      a ha)
    (D.verticalSpinFiberHaarBoundMeasure L hn hsurj)

/-- The embedded crossed measure has the exact expected logarithmic cutoff:
the common idèle-class cutoff times the literal lower Spin quotient mass. -/
theorem lintegral_nonisotropicLastComplementVerticalSpinFiberBoundMeasure_logCutoff_eq
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f
        ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
      ∂D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
        L hn a ha hsurj) =
      rationalIdeleClassLogCutoffLIntegral f *
        D.spinTamagawaNumberENNReal := by
  let W := L.rationalQuadraticSpaceMatrix
  rw [nonisotropicLastComplementVerticalSpinFiberBoundMeasure]
  change
    (∫⁻ z,
      (f ∘
        (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientLogModule) z
        ∂Measure.map
          (W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap a ha)
          (D.verticalSpinFiberHaarBoundMeasure L hn hsurj)) = _
  rw [lintegral_map'
    (hf.comp
      (W.nonisotropicLastExtension a ha
        |>.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable)).aemeasurable
    (W.continuous_fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
      a ha).measurable.aemeasurable]
  simpa only [Function.comp_apply,
    W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap_logModule]
    using D.verticalSpinFiberHaarBoundMeasure_lintegral_logCutoff_eq
      L hn hsurj f hf

/-- The embedded crossed measure is invariant under the right action of every
lower-rank adelic `GSpin` point through the certified complement block map. -/
theorem map_nonisotropicLastComplementVerticalSpinFiberBoundMeasure_rightMul
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map
        (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha
          |>.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
            (L.rationalQuadraticSpaceMatrix
              |>.nonisotropicLastComplementGeneralSpinPoint
                a ha RationalAdele x))
        (D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
          L hn a ha hsurj) =
      D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
        L hn a ha hsurj := by
  let W := L.rationalQuadraticSpaceMatrix
  let B := W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap a ha
  let R := W.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x
  let R' := (W.nonisotropicLastExtension a ha
    |>.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
      (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele x))
  rw [nonisotropicLastComplementVerticalSpinFiberBoundMeasure]
  rw [Measure.map_map
    (W.nonisotropicLastExtension a ha
      |>.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
        (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele x))
    (W.continuous_fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
      a ha).measurable]
  have hcomp : R' ∘ B = B ∘ R := by
    funext z
    exact (W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap_rightMul
      a ha x z).symm
  rw [show R' ∘ B = B ∘ R from hcomp]
  rw [← Measure.map_map
    (W.continuous_fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
      a ha).measurable
    (W.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)]
  rw [D.map_verticalSpinFiberHaarBoundMeasure_rightMul L hn hsurj x]

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
