import SMSFormula.RationalCliffordGeneralSpinHorizontalIntegralSimilitudeMarginal
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedTailScalarReassociation

/-!
# Disintegrate the retained good idelic tail through the SO central fiber

The normalized horizontal integral `GSpin` tail has two exact descriptions:
it is the existing `SO`-indexed central-fiber bind, and its similitude marginal
is normalized integral idelic Haar.  Combining them gives the iterated
good-tail change of variables required by the retained vertical cylinder.

The scalar coordinate appears as a square.  No lift is made
measurable, and no Cartesian presentation of the `SO` tail is asserted.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

local instance retainedTailSimilitudeDisintegrationDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedTailSimilitudeDisintegrationPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Similitude of a componentwise integral scalar translate is the literal
square of that scalar times the original similitude. -/
theorem cliffordGeneralSpinHorizontalIntegralTailSimilitude_scalar_mul
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail
      (S ∪ L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S) :
    L.cliffordGeneralSpinHorizontalIntegralTailSimilitude S
        (fun v =>
          L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralScalarHom
              S v (a v) * g v) =
      fun v => (a v) ^ 2 *
        L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralSimilitude
          S v (g v) := by
  let V := L.rationalQuadraticSpaceMatrix
  funext v
  apply Subtype.ext
  change
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
        V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (a v).1 * (g v).1) =
      ((a v).1 ^ 2) *
        RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
          V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (g v).1
  rw [map_mul,
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom_comp_scalarGroupHom]

/-- The good integral idèle tail is the iterated square-scalar/similitude
coordinate of the retained normalized `SO`-indexed central-fiber bind. -/
theorem lintegral_retainedIntegralTailSimilitude_disintegration
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
    let μScalar :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (∫⁻ q, ∫⁻ a,
        f (fun v => (a v) ^ 2 *
          V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g q v))
      ∂μScalar ∂μSO) =
      ∫⁻ b, f b ∂μScalar := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
  let μScalar :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
  let hA :=
    L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  let hO := L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
    (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E hA hO
  let κ := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO E hA hO
  let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
  let sim := L.cliffordGeneralSpinHorizontalIntegralTailSimilitude E
  have hsim : Measurable sim :=
    L.measurable_cliffordGeneralSpinHorizontalIntegralTailSimilitude E
  have hbind : κ ∘ₘ μSO = μG :=
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_normalizedSO_canonical
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  have hmarginal : Measure.map sim μG = μScalar :=
    L.map_cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_similitude_retained S
  change
    (∫⁻ q, ∫⁻ a,
        f (fun v => (a v) ^ 2 *
          V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g q v))
      ∂μScalar ∂μSO) =
      ∫⁻ b, f b ∂μScalar
  calc
    (∫⁻ q, ∫⁻ a,
        f (fun v => (a v) ^ 2 *
          V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g q v))
      ∂μScalar ∂μSO) =
        ∫⁻ q, ∫⁻ a,
          f (sim (fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) * g q v))
        ∂μScalar ∂μSO := by
      apply lintegral_congr
      intro q
      apply lintegral_congr
      intro a
      change
        f (fun v => (a v) ^ 2 *
          V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g q v)) =
        f (L.cliffordGeneralSpinHorizontalIntegralTailSimilitude E
          (fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) * g q v))
      exact congrArg f
        (L.cliffordGeneralSpinHorizontalIntegralTailSimilitude_scalar_mul
          E a (g q)).symm
    _ = ∫⁻ q, ∫⁻ w, f (sim w) ∂κ q ∂μSO := by
      apply lintegral_congr
      intro q
      let tailMap :
          RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B →
            V.CliffordGeneralSpinHorizontalIntegralTail E :=
        fun a v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) * g q v
      have htailMap : Measurable tailMap :=
        measurable_pi_lambda _ fun v =>
          measurable_mul_const (g q v) |>.comp
            ((V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom E v).measurable.comp
              (measurable_pi_apply v))
      have hfsim : Measurable (fun w => f (sim w)) := hf.comp hsim
      calc
        (∫⁻ a, f (sim (tailMap a)) ∂μScalar) =
            ∫⁻ w, f (sim w) ∂Measure.map tailMap μScalar :=
          (lintegral_map hfsim htailMap).symm
        _ = ∫⁻ w, f (sim w) ∂κ q := by
          rw [L.integralCentralFiberTailKernelAtSO_apply_eq_map_scalarTail E hA hO q]
    _ = ∫⁻ w, f (sim w) ∂(κ ∘ₘ μSO) := by
      simpa only [Function.comp_apply] using
        (Measure.lintegral_bind (m := μSO) (μ := κ) κ.aemeasurable
          ((hf.comp hsim).aemeasurable)).symm
    _ = ∫⁻ w, f (sim w) ∂μG := by rw [hbind]
    _ = ∫⁻ b, f b ∂μScalar := by
      rw [← hmarginal, lintegral_map hf hsim]

end PositiveDefiniteIntegralLattice

end
