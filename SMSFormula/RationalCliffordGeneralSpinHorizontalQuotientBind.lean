import SMSFormula.RationalCliffordGeneralSpinHorizontalMeasurableDescent
import SMSFormula.RationalCliffordGeneralSpinHorizontalQuotientMeasure
import SMSFormula.RationalCliffordGeneralSpinRawHorizontalCrossedCutoff

/-!
# The horizontal `SO`/idele-class bound quotient measure

The descended measurable fiber-Haar kernel can be bound against the
raw `SO` quotient measure.  This module constructs that concrete
measure on the rational adelic `GSpin` quotient and proves its complete
nonnegative measurable-integrand formula.  In particular, integrating a
logarithmic cutoff against it is exactly the horizontal crossed integral.

This names both sides of the horizontal disintegration identity:
the certified common horizontal quotient measure and this bound
measure.  Their equality is not assumed or proved here.
-/

noncomputable section

open MeasureTheory
open RationalQuadraticSpaceMatrix
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- Bind an arbitrary measure on the lattice rational adelic `SO` quotient
against the genuine descended idele-class fiber-Haar kernel. -/
noncomputable def horizontalSOFiberHaarBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (μSO : Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Measure.bind μSO (L.horizontalFiberHaarKernelAtSO inst)

/-- The bound measure of a measurable set is the outer `SO` integral of its
literal fiber-Haar masses. -/
theorem horizontalSOFiberHaarBoundMeasure_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (μSO : Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient)
    {s : Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient}
    (hs : MeasurableSet s) :
    L.horizontalSOFiberHaarBoundMeasure inst μSO s =
      ∫⁻ q, L.horizontalFiberHaarKernelAtSO inst q s ∂μSO := by
  rw [horizontalSOFiberHaarBoundMeasure,
    Measure.bind_apply hs (L.horizontalFiberHaarKernelAtSO inst).aemeasurable]

/-- Full nonnegative measurable-integrand formula for the horizontal bound
measure. -/
theorem lintegral_horizontalSOFiberHaarBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (μSO : Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient)
    (f :
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient →
        ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z, f z ∂L.horizontalSOFiberHaarBoundMeasure inst μSO =
      ∫⁻ q, ∫⁻ z, f z ∂L.horizontalFiberHaarKernelAtSO inst q ∂μSO := by
  rw [horizontalSOFiberHaarBoundMeasure,
    Measure.lintegral_bind
      (L.horizontalFiberHaarKernelAtSO inst).aemeasurable hf.aemeasurable]

/-- The literal raw-`SO` horizontal bound measure attached to an actual raw
Spin--`SO` datum. -/
noncomputable def horizontalRawSOFiberHaarBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient :=
  L.horizontalSOFiberHaarBoundMeasure inst
    D.specialOrthogonalData.quotientMeasure

/-- Full integrand formula at the literal raw `SO` quotient scale. -/
theorem lintegral_horizontalRawSOFiberHaarBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (f :
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient →
        ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z, f z ∂L.horizontalRawSOFiberHaarBoundMeasure inst D =
      ∫⁻ q, ∫⁻ z, f z ∂L.horizontalFiberHaarKernelAtSO inst q
        ∂D.specialOrthogonalData.quotientMeasure := by
  exact L.lintegral_horizontalSOFiberHaarBoundMeasure inst
    D.specialOrthogonalData.quotientMeasure f hf

/-- At each `SO` point, the descended kernel evaluates a logarithmic cutoff
as the horizontal fiber cutoff. -/
theorem lintegral_horizontalFiberHaarKernelAtSO_logCutoff
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (f : ℝ → ℝ≥0∞)
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    ∫⁻ z, f
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
          z)
      ∂L.horizontalFiberHaarKernelAtSO inst q =
      L.rationalQuadraticSpaceMatrix.horizontalFiberLogCutoffAtSO
        (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L)
        f q := by
  let V := L.rationalQuadraticSpaceMatrix
  let hsurj :=
    fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L
  rw [L.horizontalFiberHaarKernelAtSO_apply]
  unfold RationalQuadraticSpaceMatrix.horizontalFiberHaarMeasureAtSO
  unfold RationalQuadraticSpaceMatrix.horizontalFiberLogCutoffAtSO
  unfold RationalQuadraticSpaceMatrix.horizontalFiberLogCutoffLIntegral
  have hmeasure :
      V.horizontalFiberHaarMeasure
          (V.horizontalFiberHaarKernelLift hsurj q) =
        V.horizontalFiberHaarMeasure
          (V.horizontalGeneralSpinLift hsurj q) := by
    exact V.horizontalFiberHaarMeasure_eq_of_sameSO
      ((V.horizontalFiberHaarKernelLift_spec hsurj q).trans
        (V.horizontalGeneralSpinLift_spec hsurj q).symm)
  rw [hmeasure]

/-- The old horizontal crossed logarithmic integral is literally integration
of the logarithmic cutoff against the raw-`SO` fiber-Haar bound measure. -/
theorem horizontalRawSOFiberHaarBoundMeasure_lintegral_logCutoff
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z, f
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
          z)
      ∂L.horizontalRawSOFiberHaarBoundMeasure inst D =
      D.horizontalCrossedLogCutoffLIntegral L.rationalQuadraticSpaceMatrix
        (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L)
        f := by
  change
    ∫⁻ z,
        (f ∘
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule)
          z ∂L.horizontalRawSOFiberHaarBoundMeasure inst D = _
  rw [L.lintegral_horizontalRawSOFiberHaarBoundMeasure inst D _
    (hf.comp
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable)]
  unfold RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData.horizontalCrossedLogCutoffLIntegral
  apply lintegral_congr
  intro q
  exact L.lintegral_horizontalFiberHaarKernelAtSO_logCutoff inst f q

end PositiveDefiniteIntegralLattice
