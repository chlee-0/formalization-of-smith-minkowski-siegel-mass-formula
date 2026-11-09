import SMSFormula.RationalCliffordSpinCandidateRawGeneralSpinQuotientPushforward

/-!
# The logarithmic cutoff on the adelic general-Spin quotient

The idele-class logarithmic module pulls back along the descended similitude
on `GSpin(Q)\GSpin(A)`.  It is continuous and measurable for the literal
quotient structures.  The represented Spin quotient is its zero fiber, so
integrating any nonnegative measurable cutoff against the pushed raw Spin
measure evaluates to the cutoff value at zero times the existing raw Spin
Tamagawa number.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The logarithmic idele-class module on the rational adelic intrinsic
general-Spin quotient. -/
def fullAdelicCliffordGeneralSpinLeftQuotientLogModule
    (c : V.FullAdelicCliffordGeneralSpinLeftQuotient) : ℝ :=
  rationalIdeleClassLogModule
    (V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass c)

theorem continuous_fullAdelicCliffordGeneralSpinLeftQuotientLogModule :
    Continuous V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule :=
  continuous_rationalIdeleClassLogModule.comp
    V.continuous_fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass

@[simp]
theorem fullAdelicCliffordGeneralSpinLeftQuotientLogModule_mk
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x) =
      rationalIdeleLogModule
        (V.fullAdelicCliffordGeneralSpinSimilitudeHom x) :=
  rfl

/-- Measurability for the map-generated quotient structure, proved before
introducing any general-Spin quotient measure. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable :
    Measurable V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  have hrep : Measurable
      (fun x : V.FullAdelicCliffordGeneralSpinGroup =>
        rationalIdeleClassLogModule
          (QuotientGroup.mk' rationalIdeleDiagonalSubgroup
            (V.fullAdelicCliffordGeneralSpinSimilitudeHom x))) :=
    (continuous_rationalIdeleClassLogModule.comp
      (continuous_quot_mk.comp
        V.continuous_fullAdelicCliffordGeneralSpinSimilitudeHom)).measurable
  simpa [fullAdelicCliffordGeneralSpinLeftQuotientLogModule,
    fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass,
    Function.comp_def] using measurable_iff_comap_le.mp hrep

/-- The represented Spin quotient lies in the zero logarithmic fiber. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_logModule_eq_zero
    (z : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
        (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin z) = 0 := by
  induction z using Quot.inductionOn with
  | _ x =>
    change rationalIdeleLogModule
      (V.fullAdelicCliffordGeneralSpinSimilitudeHom
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x)) = 0
    change rationalIdeleLogModule 1 = 0
    simp [rationalIdeleLogModule, rationalIdeleModuleNNReal,
      finiteIdeleModuleNNReal_one]

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- Every nonnegative measurable logarithmic cutoff on the crossed quotient
evaluates on the pushed raw Spin measure at the neutral value. -/
theorem lintegral_spinGeneralSpinQuotientPushforward_logCutoff
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ c, f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule c)
        ∂spinGeneralSpinQuotientPushforwardMeasure V D) =
      f 0 * D.spinTamagawaNumberENNReal := by
  rw [spinGeneralSpinQuotientPushforwardMeasure,
    fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpinPushforward]
  calc
    (∫⁻ c, f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule c)
        ∂Measure.map V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
          D.spinData.quotientMeasure) =
        ∫⁻ z, f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
          (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin z))
            ∂D.spinData.quotientMeasure := by
      exact lintegral_map'
        (hf.comp
          V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable).aemeasurable
        V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_measurable.aemeasurable
    _ = ∫⁻ _z, f 0 ∂D.spinData.quotientMeasure := by
      apply lintegral_congr
      intro z
      rw [V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_logModule_eq_zero]
    _ = f 0 * D.spinTamagawaNumberENNReal := by
      rw [lintegral_const]
      rfl

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
