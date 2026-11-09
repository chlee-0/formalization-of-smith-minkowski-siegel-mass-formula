import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellRationalPeriodization

/-!
# Periodization of rational block-shell fibers

Rational-diagonal periodization is covariant under adelic right translation:
translating a quotient measure and then periodizing is exactly the ambient
right translate of its periodization.  Applying this to the
inverse-translated rational fibers over the block shell identifies their
periodizations with the same inverse translate of the full rational
shell-coset sum of raw orbit fibers.

The inverse orientation and the complete countable shell-coset sum stay
explicit.  In particular, this file neither replaces that sum by one raw
stabilizer fiber nor cancels the vertical periodization scalar.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Rational-diagonal periodization commutes with quotient and ambient right
translation at the same adelic GSpin point. -/
theorem map_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_rightMul
    (mu : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map (fun z : V.FullAdelicCliffordGeneralSpinGroup => z * x)
        (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift mu) =
      V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (Measure.map
          (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) mu) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_mul_const x)]
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    mu (fun z => f (z * x)) (hf.comp (measurable_mul_const x))]
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    (Measure.map
      (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) mu) f hf]
  have hperiodize : Measurable
      (leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f) :=
    V.measurable_fullAdelicCliffordGeneralSpinLeftPeriodize f hf
  calc
    (∫⁻ y,
        leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          (fun z => f (z * x)) y ∂mu) =
      ∫⁻ y,
        leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
          (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x y) ∂mu := by
        apply lintegral_congr
        exact V.fullAdelicCliffordGeneralSpinLeftPeriodize_rightMul f x
    _ = ∫⁻ y,
        leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f y
          ∂Measure.map
            (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) mu := by
        rw [lintegral_map hperiodize
          (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)]

end RationalQuadraticSpaceMatrix

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ}

/-- The periodization of the inverse-translated crossed rational fiber is the
same inverse translate of the vertical scalar times the complete rational
shell-coset sum of raw orbit fibers. -/
theorem periodized_nonisotropicLastShellAmbientRationalFiberKernel_apply
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (g : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    let W := L.rationalQuadraticSpaceMatrix
    let V := W.nonisotropicLastExtension a ha
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel
          L hn a ha hsurj g) =
      D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj •
        Measure.map
          (fun z : V.FullAdelicCliffordGeneralSpinGroup => z * g⁻¹)
          (Measure.sum fun xi :
            V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
              W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha =>
            W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
              a ha xi) := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  dsimp only
  rw [D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel_apply
    L hn a ha hsurj g]
  rw [← V.map_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_rightMul]
  rw [D.periodized_nonisotropicLastComplementVerticalSpinFiberBoundMeasure_eq_rawFibers
    L hn a ha hsurj]
  rw [Measure.map_smul]

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
