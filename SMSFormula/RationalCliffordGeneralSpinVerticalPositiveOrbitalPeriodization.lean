import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalDescent
import SMSFormula.RationalIdeleDifferentialPositivePeriodization

/-!
# Ambient periodization of descended Spin orbital integrals

The raw Spin orbital measure is already a measurable kernel on actual positive
idèles.  Combining that descent with the coefficient-one positive-idèle
fundamental-domain formula removes the remaining positive rational diagonal
sum for every measurable nonnegative ambient integrand.

This is section-free: the chosen lift used in the definition of an orbital
measure does not occur in the statement or the periodization argument.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

/-- Integrating a measurable ambient function against the descended raw Spin
orbital kernel gives a measurable function of the positive idèle. -/
theorem measurable_lintegral_positiveSpinOrbitalKernel
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    {f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞}
    (hf : Measurable f) :
    Measurable (fun a :
        RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup =>
      MeasureTheory.lintegral (L.positiveSpinOrbitalKernel hr D a) f) := by
  exact (Measure.measurable_lintegral hf).comp
    (L.measurable_positiveSpinOrbitalMeasure hr D)

/-- The positive rational diagonal periodization of every descended Spin
orbital integral unfolds to the ambient positive-idèle integral, with
coefficient one. -/
theorem lintegral_positiveSpinOrbitalKernel_tsum_diagonal_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞)
    (hf : Measurable f) :
    MeasureTheory.lintegral
      (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure.restrict
        RationalQuadraticSpaceMatrix.positiveRationalIdeleMeasurableFundamentalDomainSubtype)
      (fun a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup =>
        ∑' gamma :
            RationalQuadraticSpaceMatrix.positiveRationalIdeleDiagonalSubgroup,
          MeasureTheory.lintegral
            (L.positiveSpinOrbitalKernel hr D
              ((gamma : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup) * a)) f) =
      MeasureTheory.lintegral
        RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure
        (fun a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup =>
          MeasureTheory.lintegral (L.positiveSpinOrbitalKernel hr D a) f) := by
  exact
    RationalQuadraticSpaceMatrix.lintegral_positiveRationalIdele_tsum_diagonal_eq
      (fun a => MeasureTheory.lintegral (L.positiveSpinOrbitalKernel hr D a) f)
      (L.measurable_lintegral_positiveSpinOrbitalKernel hr D hf)

/-- Carrier form of the descended orbital periodization.  This is the exact
indicator specialization consumed by the remaining vertical cylinder
restriction. -/
theorem lintegral_positiveSpinOrbitalKernel_carrier_tsum_diagonal_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (C : Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (hC : MeasurableSet C) :
    MeasureTheory.lintegral
      (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure.restrict
        RationalQuadraticSpaceMatrix.positiveRationalIdeleMeasurableFundamentalDomainSubtype)
      (fun a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup =>
        ∑' gamma :
            RationalQuadraticSpaceMatrix.positiveRationalIdeleDiagonalSubgroup,
          L.positiveSpinOrbitalKernel hr D
            ((gamma : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup) * a) C) =
      MeasureTheory.lintegral
        RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure
        (fun a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup =>
          L.positiveSpinOrbitalKernel hr D a C) := by
  have hindicator : Measurable
      (C.indicator (fun _ :
        L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup =>
          (1 : ℝ≥0∞))) :=
    measurable_const.indicator hC
  have hperiodized :=
    L.lintegral_positiveSpinOrbitalKernel_tsum_diagonal_eq hr D
      (C.indicator (fun _ => (1 : ℝ≥0∞))) hindicator
  simpa only [lintegral_indicator_const hC, one_mul] using hperiodized

end PositiveDefiniteIntegralLattice

end
