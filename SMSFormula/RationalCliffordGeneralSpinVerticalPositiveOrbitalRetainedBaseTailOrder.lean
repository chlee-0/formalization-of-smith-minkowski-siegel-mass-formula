import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedBaseSourceNormalization
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedTailScalarReassociation

/-!
# Reorder the retained base good-tail integral through its kernel

The retained-base disintegration exposes the good coordinates in the order
`SO -> scalar -> Spin`, while the calibrated cylinder formula uses
`Spin -> SO -> scalar`.  The displayed good-tail lift is definition-only and
cannot be used for a direct global Tonelli permutation.

This file first interchanges scalar and Spin for each fixed `SO` point, rewrites
the scalar integral as the existing measurable central-fiber kernel, and only
then interchanges `SO` and Spin.  Thus no measurable section or Cartesian
presentation of the `SO` tail is introduced.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

local instance retainedBaseTailOrderDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedBaseTailOrderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

noncomputable local instance retainedBaseTailOrderPadicSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance retainedBaseTailOrderPadicSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance retainedBaseTailOrderHeightOneSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance retainedBaseTailOrderHeightOneSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance retainedBaseTailOrderHeightOneSOSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    L.rationalQuadraticSpaceMatrix.pairingMatrix
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance retainedBaseTailOrderIntegralSOFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  Subtype.borelSpace _

local instance retainedBaseTailOrderIntegralSOFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedBaseTailOrderIntegralSOTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedBaseTailOrderIntegralSOTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Pi.borelSpace

set_option backward.isDefEq.respectTransparency false in
/-- The good-tail integral in retained-base order is the same normalized
horizontal integral `GSpin` Haar integral as in cylinder order.  Kernelizing
the scalar coordinate is what makes the `SO`/Spin Tonelli exchange valid. -/
theorem lintegral_retainedIntegralScalarSpinTail_centralFiberBind_baseOrder
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
    (∫⁻ q, ∫⁻ a, ∫⁻ u,
        f (fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
            L.retainedIntegralSpinTailAction S u v * g q v)
      ∂μSpin ∂μScalar ∂μSO) =
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
  letI : IsProbabilityMeasure μSpin :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability B
  letI : IsFiniteMeasure μSpin := by infer_instance
  letI : SigmaFinite μSpin := IsFiniteMeasure.toSigmaFinite _
  letI : IsFiniteMeasure μSO := by infer_instance
  letI : SigmaFinite μSO := IsFiniteMeasure.toSigmaFinite _
  letI : IsFiniteMeasure μScalar := by infer_instance
  letI : SigmaFinite μScalar := IsFiniteMeasure.toSigmaFinite _
  have hscalar
      (u : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)
      (q : V.FiniteAdelicSpecialOrthogonalIntegralTail B) :
      (∫⁻ a,
          f (fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v) ∂μScalar) =
        ∫⁻ w, f (L.retainedIntegralSpinTailElement S u * w) ∂kappa q := by
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
  have hswapScalarSpin
      (q : V.FiniteAdelicSpecialOrthogonalIntegralTail B) :
      (∫⁻ a, ∫⁻ u,
          f (fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μSpin ∂μScalar) =
        ∫⁻ u, ∫⁻ a,
          f (fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μScalar ∂μSpin := by
    let F : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B → ENNReal :=
      fun z => f (fun v =>
        V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (z.1 v) *
          L.retainedIntegralSpinTailAction S z.2 v * g q v)
    have hF : Measurable F := by
      apply hf.comp
      exact measurable_pi_lambda _ fun v =>
        Measurable.subtype_mk
          (((continuous_subtype_val.measurable.comp
            ((V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom E v).measurable.comp
              ((measurable_pi_apply v).comp measurable_fst))).mul
            (continuous_subtype_val.measurable.comp
              ((L.measurable_retainedIntegralSpinTailAction S v).comp measurable_snd))).mul_const
                (g q v).1)
    calc
      (∫⁻ a, ∫⁻ u,
          f (fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μSpin ∂μScalar) = ∫⁻ z, F z ∂μScalar.prod μSpin := by
          exact (lintegral_prod F hF.aemeasurable).symm
      _ = ∫⁻ u, ∫⁻ a,
          f (fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μScalar ∂μSpin := lintegral_prod_symm' F hF
  let kappa' : ProbabilityTheory.Kernel
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail B)
      (V.CliffordGeneralSpinHorizontalIntegralTail E) :=
    ProbabilityTheory.Kernel.comap kappa Prod.snd measurable_snd
  have hkernelIntegrand : Measurable (fun z :
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B ×
          V.FiniteAdelicSpecialOrthogonalIntegralTail B) ×
        V.CliffordGeneralSpinHorizontalIntegralTail E =>
      f (L.retainedIntegralSpinTailElement S z.1.1 * z.2)) := by
    apply hf.comp
    exact measurable_pi_lambda _ fun v =>
      Measurable.subtype_mk
        ((continuous_subtype_val.measurable.comp
          ((measurable_pi_apply v).comp
            ((L.measurable_retainedIntegralSpinTailElement S).comp
              (measurable_fst.comp measurable_fst)))).mul
          (continuous_subtype_val.measurable.comp
            ((measurable_pi_apply v).comp measurable_snd)))
  have hkernelIntegral : Measurable (fun z :
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail B =>
      ∫⁻ w, f (L.retainedIntegralSpinTailElement S z.1 * w) ∂kappa z.2) := by
    have h := hkernelIntegrand.lintegral_kernel_prod_right' (κ := kappa')
    simpa only [kappa', ProbabilityTheory.Kernel.comap_apply] using h
  have hswapSpinSO :
      (∫⁻ q, ∫⁻ u, ∫⁻ w,
          f (L.retainedIntegralSpinTailElement S u * w) ∂kappa q ∂μSpin ∂μSO) =
        ∫⁻ u, ∫⁻ q, ∫⁻ w,
          f (L.retainedIntegralSpinTailElement S u * w) ∂kappa q ∂μSO ∂μSpin := by
    let F : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail B → ENNReal :=
      fun z => ∫⁻ w, f (L.retainedIntegralSpinTailElement S z.1 * w) ∂kappa z.2
    calc
      (∫⁻ q, ∫⁻ u, ∫⁻ w,
          f (L.retainedIntegralSpinTailElement S u * w) ∂kappa q ∂μSpin ∂μSO) =
          ∫⁻ z, F z ∂μSpin.prod μSO := by
        exact (lintegral_prod_symm' F hkernelIntegral).symm
      _ = ∫⁻ u, ∫⁻ q, ∫⁻ w,
          f (L.retainedIntegralSpinTailElement S u * w) ∂kappa q ∂μSO ∂μSpin :=
        lintegral_prod F hkernelIntegral.aemeasurable
  have hbind := L.lintegral_retainedIntegralSpinTail_centralFiberBind S f hf
  calc
    (∫⁻ q, ∫⁻ a, ∫⁻ u,
        f (fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
            L.retainedIntegralSpinTailAction S u v * g q v)
      ∂μSpin ∂μScalar ∂μSO) =
        ∫⁻ q, ∫⁻ u, ∫⁻ a,
          f (fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μScalar ∂μSpin ∂μSO := by
      apply lintegral_congr
      exact hswapScalarSpin
    _ = ∫⁻ q, ∫⁻ u, ∫⁻ w,
          f (L.retainedIntegralSpinTailElement S u * w) ∂kappa q ∂μSpin ∂μSO := by
      apply lintegral_congr
      intro q
      apply lintegral_congr
      intro u
      exact hscalar u q
    _ = ∫⁻ u, ∫⁻ q, ∫⁻ w,
          f (L.retainedIntegralSpinTailElement S u * w) ∂kappa q ∂μSO ∂μSpin :=
      hswapSpinSO
    _ = ∫⁻ w, f w ∂μG := by
      simpa only [V, E, B, μSpin, μSO, kappa, μG] using hbind

end PositiveDefiniteIntegralLattice

end
