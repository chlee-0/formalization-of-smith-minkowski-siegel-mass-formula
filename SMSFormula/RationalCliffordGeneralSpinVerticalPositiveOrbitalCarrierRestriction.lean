import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalPeriodization
import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderHaarRestriction

/-!
# Restrict descended Spin orbital measures to the identity carrier

The positive-idèle orbital kernel was descended without a measurable choice of
`GSpin(A)` representative.  At an actual ambient point, its pullback is the
literal raw Spin orbit.  This file commutes that pullback with restriction to
an arbitrary measurable carrier and specializes it to the certified
full-adelic identity carrier.

This exposes exactly the raw Spin preimage to which the existing real--finite
and cofinal-block restriction theorems apply.  No representative, chart, or
normalization coefficient is introduced.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

/-- Restriction of the descended orbital kernel at an actual similitude is the
pushforward of raw Spin Haar restricted to the literal orbital preimage. -/
theorem positiveSpinOrbitalKernel_projection_restrict
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (C : Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (hC : MeasurableSet C) :
    (L.positiveSpinOrbitalKernel hr D
        (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g)).restrict C =
      Measure.map
        (fun y : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateGroup =>
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g)
        (D.spinData.adelicMeasure.restrict
    ((fun y :
              L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateGroup =>
            L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g) ⁻¹'
            C)) := by
  let V := L.rationalQuadraticSpaceMatrix
  let orbit := fun y : V.FullAdelicCliffordSpinCandidateGroup =>
    V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g
  have horbit : Measurable orbit :=
    (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
      RationalAdele).mul continuous_const |>.measurable
  rw [L.positiveSpinOrbitalKernel_projection hr D g,
    D.positiveSpinOrbitalKernelAtAmbient_apply]
  change (Measure.map orbit D.spinData.adelicMeasure).restrict C =
    Measure.map orbit (D.spinData.adelicMeasure.restrict (orbit ⁻¹' C))
  exact Measure.restrict_map horbit hC

/-- Carrier mass form of the preceding restriction identity. -/
theorem positiveSpinOrbitalKernel_projection_apply
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (C : Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (hC : MeasurableSet C) :
    L.positiveSpinOrbitalKernel hr D
        (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g) C =
      D.spinData.adelicMeasure
        ((fun y :
            L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateGroup =>
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g) ⁻¹'
          C) := by
  let V := L.rationalQuadraticSpaceMatrix
  let orbit := fun y : V.FullAdelicCliffordSpinCandidateGroup =>
    V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g
  have horbit : Measurable orbit :=
    (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
      RationalAdele).mul continuous_const |>.measurable
  rw [L.positiveSpinOrbitalKernel_projection hr D g,
    D.positiveSpinOrbitalKernelAtAmbient_apply]
  change Measure.map orbit D.spinData.adelicMeasure C =
    D.spinData.adelicMeasure (orbit ⁻¹' C)
  exact Measure.map_apply horbit hC

/-- Representative-free restriction formula: any actual ambient point with
the prescribed positive similitude computes the descended kernel. -/
theorem positiveSpinOrbitalKernel_restrict_of_similitude_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (hg : L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g = a)
    (C : Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (hC : MeasurableSet C) :
    (L.positiveSpinOrbitalKernel hr D a).restrict C =
      Measure.map
        (fun y : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateGroup =>
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g)
        (D.spinData.adelicMeasure.restrict
          ((fun y :
              L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateGroup =>
            L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g) ⁻¹'
            C)) := by
  rw [← hg]
  exact L.positiveSpinOrbitalKernel_projection_restrict hr D g C hC

/-- Representative-free carrier-mass formula at any ambient point with the
prescribed positive similitude. -/
theorem positiveSpinOrbitalKernel_apply_of_similitude_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (hg : L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g = a)
    (C : Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (hC : MeasurableSet C) :
    L.positiveSpinOrbitalKernel hr D a C =
      D.spinData.adelicMeasure
        ((fun y :
            L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateGroup =>
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g) ⁻¹'
          C) := by
  rw [← hg]
  exact L.positiveSpinOrbitalKernel_projection_apply hr D g C hC

/-- Exact evaluation of the descended orbital kernel on the certified
full-adelic identity carrier. -/
theorem positiveSpinOrbitalKernel_projection_apply_identityChart
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.positiveSpinOrbitalKernel hr D
        (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g)
        (L.rationalQuadraticSpaceMatrix
          |>.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S) =
      D.spinData.adelicMeasure
        ((fun y :
            L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateGroup =>
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g) ⁻¹'
          (L.rationalQuadraticSpaceMatrix
            |>.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S)) := by
  exact L.positiveSpinOrbitalKernel_projection_apply hr D g _
    (L.rationalQuadraticSpaceMatrix
      |>.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S)

end PositiveDefiniteIntegralLattice

end
