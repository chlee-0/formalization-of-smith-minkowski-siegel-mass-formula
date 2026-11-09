import SMSFormula.RationalCliffordGeneralSpinVerticalFiberQuotientRightTranslation
import SMSFormula.RationalCliffordGeneralSpinAdelicQuotientMeasurePeriodizedRightInvariant
import SMSFormula.RationalCliffordGeneralSpinCrossedCutoffExtraction

/-!
# Periodizing the vertical Spin-fiber quotient bind

The class-Haar bind of the descended vertical Spin fibers is nonzero.  Its
exact rational-`GSpin` periodization is therefore nonzero as well, and the
already proved quotient right invariance transports to genuine right
invariance on ambient adelic `GSpin`.

This module does not assert sigma-finiteness or compare the periodized lift
with Haar measure.  In particular, it does not use finiteness of the raw Spin
Tamagawa mass or assign a value to the vertical ambient-Haar scalar.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2000000

/-- The class-Haar bind of translated raw Spin fibers is nonzero.  The unit
logarithmic cutoff has positive finite idele-class integral, while the raw
Spin quotient mass is already known to be nonzero. -/
theorem verticalSpinFiberHaarBoundMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    D.verticalSpinFiberHaarBoundMeasure L hn hsurj ≠ 0 := by
  intro hzero
  have hIntegralZero :
      ∫⁻ z,
          RationalQuadraticSpaceMatrix.rationalIdeleClassUnitLogCutoff
            (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
              z)
        ∂D.verticalSpinFiberHaarBoundMeasure L hn hsurj = 0 := by
    rw [hzero]
    simp
  rw [D.verticalSpinFiberHaarBoundMeasure_lintegral_logCutoff_eq
      L hn hsurj
      RationalQuadraticSpaceMatrix.rationalIdeleClassUnitLogCutoff
      RationalQuadraticSpaceMatrix.measurable_rationalIdeleClassUnitLogCutoff]
    at hIntegralZero
  exact (mul_ne_zero
    RationalQuadraticSpaceMatrix.rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
    D.spinTamagawaNumberENNReal_ne_zero) hIntegralZero

/-- Exact rational-`GSpin` periodization does not annihilate the vertical
quotient bind. -/
theorem periodizedVerticalSpinFiberHaarBoundMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) ≠ 0 :=
  L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_ne_zero
      (D.verticalSpinFiberHaarBoundMeasure L hn hsurj)
      (D.verticalSpinFiberHaarBoundMeasure_ne_zero L hn hsurj)

/-- Quotient right invariance transports through exact periodization to
ambient adelic `GSpin` right invariance. -/
theorem map_periodizedVerticalSpinFiberHaarBoundMeasure_rightMul
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map (fun z => z * x)
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
            (D.verticalSpinFiberHaarBoundMeasure L hn hsurj)) =
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) :=
  L.rationalQuadraticSpaceMatrix.map_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_rightMul_of_map_eq
      (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) x
      (D.map_verticalSpinFiberHaarBoundMeasure_rightMul L hn hsurj x)

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
