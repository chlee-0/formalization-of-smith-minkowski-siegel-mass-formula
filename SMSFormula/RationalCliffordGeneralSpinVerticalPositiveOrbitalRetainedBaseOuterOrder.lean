import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedBaseTailOrder

/-!
# Reassociate the outer retained-base normalized source

The good-tail order theorem is extended here by a measurable parameter
measure.  This form is needed for the retained real and exceptional
Spin coordinates, which occur inside the `SO`/scalar integrals after base
disintegration.  The scalar integral is kernelized before the parameter is
moved across the `SO` coordinate, so the definition-only good-tail lift is
never asserted measurable.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 3800000

local instance retainedBaseOuterOrderDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedBaseOuterOrderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

noncomputable local instance retainedBaseOuterOrderPadicSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance retainedBaseOuterOrderPadicSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance retainedBaseOuterOrderHeightOneSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance retainedBaseOuterOrderHeightOneSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance retainedBaseOuterOrderHeightOneSOSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    L.rationalQuadraticSpaceMatrix.pairingMatrix
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance retainedBaseOuterOrderIntegralSOFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  Subtype.borelSpace _

local instance retainedBaseOuterOrderIntegralSOFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedBaseOuterOrderIntegralSOTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedBaseOuterOrderIntegralSOTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Pi.borelSpace

set_option backward.isDefEq.respectTransparency false in
/-- The fixed normalized Spin source is exactly the real chart
source, the retained exceptional identity restriction, and the normalized
integral Spin tail. -/
theorem cliffordGeneralSpinVerticalRetainedSpinSourceMeasure_eq_split
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.cliffordGeneralSpinVerticalRetainedSpinSourceMeasure S =
      V.realCliffordSpinCandidateIdentityChartSourceMeasure.prod
        (((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
            (V.retainedSpinExceptionalIdentityCarrier B)).prod
          (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B)) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μR := V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let μE := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B
  let μT := V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B
  let CE := V.retainedSpinExceptionalIdentityCarrier B
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
    let chart := V.realCliffordSpinCandidateIdentityChart
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe chart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
    let chart := V.realCliffordSpinCandidateIdentityChart
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact chart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite μE :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite B
  letI : IsProbabilityMeasure μT :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability B
  letI : IsFiniteMeasure μT := by infer_instance
  letI : SigmaFinite μT := IsFiniteMeasure.toSigmaFinite _
  unfold cliffordGeneralSpinVerticalRetainedSpinSourceMeasure
    RationalQuadraticSpaceMatrix.retainedSpinExceptionalTailIdentityCylinder
    RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  change (μR.prod (μE.prod μT)).restrict (Set.univ ×ˢ (CE ×ˢ Set.univ)) =
    μR.prod ((μE.restrict CE).prod μT)
  rw [← Measure.prod_restrict (μ := μR) (ν := μE.prod μT), Measure.restrict_univ]
  rw [← Measure.prod_restrict (μ := μE) (ν := μT), Measure.restrict_univ]

set_option backward.isDefEq.respectTransparency false in
/-- A measurable parameter may remain inside the retained-base scalar/Spin
integral.  Kernelization makes it legitimate to move that parameter across
the normalized `SO` coordinate, after which the base-order tail theorem
applies pointwise. -/
theorem lintegral_retainedIntegralScalarSpinTail_centralFiberBind_baseOrder_param
    {P : Type*} [MeasurableSpace P]
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (ρ : Measure P) [SFinite ρ]
    (f : P × L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail
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
    (∫⁻ q, ∫⁻ a, ∫⁻ p, ∫⁻ u,
        f (p, fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
            L.retainedIntegralSpinTailAction S u v * g q v)
      ∂μSpin ∂ρ ∂μScalar ∂μSO) =
      ∫⁻ p, ∫⁻ w, f (p, w) ∂μG ∂ρ := by
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
  have htailJoint
      (q : V.FiniteAdelicSpecialOrthogonalIntegralTail B) :
      Measurable (fun z :
          (RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B × P) ×
            V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B =>
        f (z.1.2, fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (z.1.1 v) *
            L.retainedIntegralSpinTailAction S z.2 v * g q v)) := by
    apply hf.comp
    exact measurable_snd.comp measurable_fst |>.prodMk
      (measurable_pi_lambda _ fun v =>
        Measurable.subtype_mk
          (((continuous_subtype_val.measurable.comp
            ((V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom E v).measurable.comp
              ((measurable_pi_apply v).comp
                (measurable_fst.comp measurable_fst)))).mul
            (continuous_subtype_val.measurable.comp
              ((L.measurable_retainedIntegralSpinTailAction S v).comp measurable_snd))).mul_const
                (g q v).1))
  have hswapScalarParam
      (q : V.FiniteAdelicSpecialOrthogonalIntegralTail B) :
      (∫⁻ a, ∫⁻ p, ∫⁻ u,
          f (p, fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μSpin ∂ρ ∂μScalar) =
        ∫⁻ p, ∫⁻ a, ∫⁻ u,
          f (p, fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μSpin ∂μScalar ∂ρ := by
    let F : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B × P →
        ENNReal := fun z => ∫⁻ u,
      f (z.2, fun v =>
        V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (z.1 v) *
          L.retainedIntegralSpinTailAction S u v * g q v) ∂μSpin
    have hF : Measurable F := (htailJoint q).lintegral_prod_right'
    calc
      (∫⁻ a, ∫⁻ p, ∫⁻ u,
          f (p, fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μSpin ∂ρ ∂μScalar) = ∫⁻ z, F z ∂μScalar.prod ρ := by
          exact (lintegral_prod F hF.aemeasurable).symm
      _ = ∫⁻ p, ∫⁻ a, ∫⁻ u,
          f (p, fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μSpin ∂μScalar ∂ρ := lintegral_prod_symm' F hF
  have hpointKernel
      (p : P) (q : V.FiniteAdelicSpecialOrthogonalIntegralTail B) :
      (∫⁻ a, ∫⁻ u,
          f (p, fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μSpin ∂μScalar) =
        ∫⁻ u, ∫⁻ w, f (p, L.retainedIntegralSpinTailElement S u * w)
          ∂kappa q ∂μSpin := by
    let F : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B → ENNReal :=
      fun z => f (p, fun v =>
        V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (z.1 v) *
          L.retainedIntegralSpinTailAction S z.2 v * g q v)
    have hF : Measurable F := by
      simpa only [Prod.fst, Prod.snd] using
        (htailJoint q).comp
          (((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
    have hswap :
        (∫⁻ a, ∫⁻ u, F (a, u) ∂μSpin ∂μScalar) =
          ∫⁻ u, ∫⁻ a, F (a, u) ∂μScalar ∂μSpin := by
      calc
        _ = ∫⁻ z, F z ∂μScalar.prod μSpin :=
          (lintegral_prod F hF.aemeasurable).symm
        _ = _ := lintegral_prod_symm' F hF
    rw [hswap]
    apply lintegral_congr
    intro u
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
        (fun w => f (p, L.retainedIntegralSpinTailElement S u * w)) :=
      hf.comp (measurable_const.prodMk
        (measurable_const_mul (L.retainedIntegralSpinTailElement S u)))
    calc
      (∫⁻ a, F (a, u) ∂μScalar) =
          ∫⁻ a, f (p, L.retainedIntegralSpinTailElement S u * tailMap a) ∂μScalar := by
        apply lintegral_congr
        intro a
        apply congrArg (fun w => f (p, w))
        funext v
        change
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
                L.retainedIntegralSpinTailAction S u v * g q v =
            L.retainedIntegralSpinTailAction S u v *
              (V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) * g q v)
        rw [← mul_assoc,
          ← V.padicCliffordGeneralSpinHorizontalIntegralScalarHom_commutes E v]
      _ = ∫⁻ w, f (p, L.retainedIntegralSpinTailElement S u * w)
            ∂Measure.map tailMap μScalar := by
        exact (lintegral_map horbit htailMap).symm
      _ = ∫⁻ w, f (p, L.retainedIntegralSpinTailElement S u * w) ∂kappa q := by
        rw [L.integralCentralFiberTailKernelAtSO_apply_eq_map_scalarTail E hA hO q]
  let kappa' : ProbabilityTheory.Kernel
      ((P × V.FiniteAdelicSpecialOrthogonalIntegralTail B) ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)
      (V.CliffordGeneralSpinHorizontalIntegralTail E) :=
    ProbabilityTheory.Kernel.comap kappa (fun z => z.1.2)
      (measurable_snd.comp measurable_fst)
  have hkernelIntegrand : Measurable (fun z :
      (((P × V.FiniteAdelicSpecialOrthogonalIntegralTail B) ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) ×
        V.CliffordGeneralSpinHorizontalIntegralTail E) =>
      f (z.1.1.1, L.retainedIntegralSpinTailElement S z.1.2 * z.2)) := by
    apply hf.comp
    exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_pi_lambda _ fun v =>
        Measurable.subtype_mk
          ((continuous_subtype_val.measurable.comp
            ((measurable_pi_apply v).comp
              ((L.measurable_retainedIntegralSpinTailElement S).comp
                (measurable_snd.comp measurable_fst)))).mul
            (continuous_subtype_val.measurable.comp
              ((measurable_pi_apply v).comp measurable_snd))))
  have hkernelAtSpin : Measurable (fun z :
      (P × V.FiniteAdelicSpecialOrthogonalIntegralTail B) ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B =>
      ∫⁻ w, f (z.1.1, L.retainedIntegralSpinTailElement S z.2 * w)
        ∂kappa z.1.2) := by
    have h := hkernelIntegrand.lintegral_kernel_prod_right' (κ := kappa')
    simpa only [kappa', ProbabilityTheory.Kernel.comap_apply] using h
  have hkernelIntegral : Measurable (fun z :
      P × V.FiniteAdelicSpecialOrthogonalIntegralTail B =>
      ∫⁻ u, ∫⁻ w, f (z.1, L.retainedIntegralSpinTailElement S u * w)
        ∂kappa z.2 ∂μSpin) :=
    hkernelAtSpin.lintegral_prod_right'
  let H : P × V.FiniteAdelicSpecialOrthogonalIntegralTail B → ENNReal :=
    fun z => ∫⁻ a, ∫⁻ u,
      f (z.1, fun v =>
        V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
          L.retainedIntegralSpinTailAction S u v * g z.2 v)
      ∂μSpin ∂μScalar
  have hH : Measurable H := by
    have heq : H = fun z =>
        ∫⁻ u, ∫⁻ w, f (z.1, L.retainedIntegralSpinTailElement S u * w)
          ∂kappa z.2 ∂μSpin := by
      funext z
      exact hpointKernel z.1 z.2
    rw [heq]
    exact hkernelIntegral
  have hswapParamSO :
      (∫⁻ q, ∫⁻ p, H (p, q) ∂ρ ∂μSO) =
        ∫⁻ p, ∫⁻ q, H (p, q) ∂μSO ∂ρ := by
    calc
      _ = ∫⁻ z, H z ∂ρ.prod μSO := (lintegral_prod_symm' H hH).symm
      _ = _ := lintegral_prod H hH.aemeasurable
  calc
    (∫⁻ q, ∫⁻ a, ∫⁻ p, ∫⁻ u,
        f (p, fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
            L.retainedIntegralSpinTailAction S u v * g q v)
      ∂μSpin ∂ρ ∂μScalar ∂μSO) =
        ∫⁻ q, ∫⁻ p, ∫⁻ a, ∫⁻ u,
          f (p, fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μSpin ∂μScalar ∂ρ ∂μSO := by
      apply lintegral_congr
      exact hswapScalarParam
    _ = ∫⁻ q, ∫⁻ p, H (p, q) ∂ρ ∂μSO := rfl
    _ = ∫⁻ p, ∫⁻ q, H (p, q) ∂μSO ∂ρ := hswapParamSO
    _ = ∫⁻ p, ∫⁻ w, f (p, w) ∂μG ∂ρ := by
      apply lintegral_congr
      intro p
      simpa only [H, V, E, B, μSpin, μSO, μScalar, g, μG] using
        L.lintegral_retainedIntegralScalarSpinTail_centralFiberBind_baseOrder S
          (fun w => f (p, w))
          (hf.comp (measurable_const.prodMk measurable_id))

end PositiveDefiniteIntegralLattice

end
