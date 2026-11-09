import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedTailBind

/-!
# Insert the differential scalar tail into the retained Spin-tail bind

The coefficient-one retained Spin-tail identity is expanded here through the
literal differential integral scalar source already used by the horizontal
reassociation kernel.  At every good place the scalar is central, so it
commutes past the retained Spin action.  The resulting threefold integral is
exactly normalized horizontal integral `GSpin` Haar.

This is an integral identity, not a Cartesian presentation or a direct
Spin-to-`SO` pushforward.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 900000
set_option maxHeartbeats 3000000

local instance retainedTailScalarDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedTailScalarPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- After exposing the differential integral scalar-tail coordinate, its
central action and the retained normalized Spin-tail action still bind to
normalized horizontal integral `GSpin` Haar with coefficient one. -/
theorem lintegral_retainedIntegralScalarSpinTail_centralFiberBind
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let μSpin :=
      V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B
    let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
    let μScalar :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
    (∫⁻ u, ∫⁻ q, ∫⁻ a,
        f (fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
            L.retainedIntegralSpinTailAction S u v * g q v)
      ∂μScalar ∂μSO ∂μSpin) =
      ∫⁻ w, f w ∂μG := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μSpin :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B
  let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
  let μScalar :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
  let hA :=
    L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  let hO := L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
    (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E hA hO
  let kappa := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO E hA hO
  let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
  have hbind := L.lintegral_retainedIntegralSpinTail_centralFiberBind S f hf
  change
    (∫⁻ u, ∫⁻ q, ∫⁻ a,
        f (fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
            L.retainedIntegralSpinTailAction S u v * g q v)
      ∂μScalar ∂μSO ∂μSpin) =
      ∫⁻ w, f w ∂μG
  calc
    (∫⁻ u, ∫⁻ q, ∫⁻ a,
        f (fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
            L.retainedIntegralSpinTailAction S u v * g q v)
      ∂μScalar ∂μSO ∂μSpin) =
        ∫⁻ u, ∫⁻ q, ∫⁻ w,
          f (L.retainedIntegralSpinTailElement S u * w) ∂kappa q ∂μSO ∂μSpin := by
      apply lintegral_congr
      intro u
      apply lintegral_congr
      intro q
      let tailMap : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B →
          V.CliffordGeneralSpinHorizontalIntegralTail E :=
        fun a v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) * g q v
      have htailMap : Measurable tailMap :=
        measurable_pi_lambda _ fun v =>
          measurable_mul_const (g q v) |>.comp
            ((V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom E v).measurable.comp
              (measurable_pi_apply v))
      have horbit : Measurable
          (fun w => f (L.retainedIntegralSpinTailElement S u * w)) :=
        hf.comp (measurable_const_mul (L.retainedIntegralSpinTailElement S u))
      calc
        (∫⁻ a,
            f (fun v =>
              V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
                L.retainedIntegralSpinTailAction S u v * g q v) ∂μScalar) =
            ∫⁻ a, f (L.retainedIntegralSpinTailElement S u * tailMap a) ∂μScalar := by
          apply lintegral_congr
          intro a
          congr 1
          funext v
          change
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
                L.retainedIntegralSpinTailAction S u v * g q v =
              L.retainedIntegralSpinTailAction S u v *
                (V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) * g q v)
          rw [← mul_assoc,
            ← V.padicCliffordGeneralSpinHorizontalIntegralScalarHom_commutes E v]
        _ = ∫⁻ w, f (L.retainedIntegralSpinTailElement S u * w)
              ∂Measure.map tailMap μScalar := by
          exact (lintegral_map horbit htailMap).symm
        _ = ∫⁻ w, f (L.retainedIntegralSpinTailElement S u * w) ∂kappa q := by
          rw [L.integralCentralFiberTailKernelAtSO_apply_eq_map_scalarTail E hA hO q]
    _ = ∫⁻ w, f w ∂μG := by
      simpa only [V, E, B, μSpin, μSO, kappa, μG] using hbind

end PositiveDefiniteIntegralLattice

end
