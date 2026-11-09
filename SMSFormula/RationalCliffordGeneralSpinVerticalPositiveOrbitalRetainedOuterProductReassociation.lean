import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedExceptionalDifferentialReassociation
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedTailScalarReassociation

/-!
# Reassociate the outer retained cylinder products

The good-tail lift used by the horizontal central-fiber kernel is not a
measurable section, so the scalar/Spin/`SO` tail identity is stated as an
iterated nonnegative-integral theorem.  This file combines that identity with
the exact exceptional differential pushforward and the real differential
pair.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 900000
set_option maxHeartbeats 3000000

local instance retainedOuterProductDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedOuterProductPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Reassociate all remaining retained real, exceptional, and good-tail
coordinates under an arbitrary measurable nonnegative integrand.  The
exceptional and tail changes of variables both have coefficient one. -/
theorem lintegral_cliffordGeneralSpinVerticalRetainedOuterProductReassociation
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : L.rationalQuadraticSpaceMatrix
        |>.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource
          (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let μR :=
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
        V.realCliffordSpinCandidateIdentityChartSourceMeasure
    let μE :=
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
        (V.retainedSpinExceptionalIdentityCarrier B)
    let μA :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure B
    let μSpin :=
      V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B
    let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
    let μScalar :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
    let μES := V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B
    let κE := L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B
    let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
    let pairE := L.cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (∫⁻ zR, ∫⁻ uE, ∫⁻ aE, ∫⁻ u, ∫⁻ q, ∫⁻ a,
        f (zR, pairE (uE, aE), fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
            L.retainedIntegralSpinTailAction S u v * g q v)
      ∂μScalar ∂μSO ∂μSpin ∂μA ∂μE ∂μR) =
      ∫⁻ zR, ∫⁻ zE, ∫⁻ w, f (zR, zE, w) ∂μG ∂(κE ∘ₘ μES) ∂μR := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μR :=
    RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
      V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let μE :=
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
      (V.retainedSpinExceptionalIdentityCarrier B)
  let μA :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure B
  let μSpin :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B
  let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
  let μScalar :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
  let μES := V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B
  let κE := L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B
  let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
  let pairE := L.cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
  have hpairE : Measurable pairE :=
    L.measurable_cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S
  have hmapE : Measure.map pairE (μE.prod μA) = κE ∘ₘ μES :=
    L.map_retainedExceptionalDifferentialPair_eq_kernel_comp_source S
  apply lintegral_congr
  intro zR
  have hfTail (zE : V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource B) :
      Measurable (fun w => f (zR, zE, w)) :=
    hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have htail (uE : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B)
      (aE : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource B) :
      (∫⁻ u, ∫⁻ q, ∫⁻ a,
          f (zR, pairE (uE, aE), fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μScalar ∂μSO ∂μSpin) =
        ∫⁻ w, f (zR, pairE (uE, aE), w) ∂μG := by
    simpa only [V, E, B, μSpin, μSO, μScalar, μG, g] using
      L.lintegral_retainedIntegralScalarSpinTail_centralFiberBind S
        (fun w => f (zR, pairE (uE, aE), w)) (hfTail (pairE (uE, aE)))
  have htails :
      (∫⁻ uE, ∫⁻ aE, ∫⁻ u, ∫⁻ q, ∫⁻ a,
          f (zR, pairE (uE, aE), fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v)
        ∂μScalar ∂μSO ∂μSpin ∂μA ∂μE) =
        ∫⁻ uE, ∫⁻ aE, ∫⁻ w,
          f (zR, pairE (uE, aE), w) ∂μG ∂μA ∂μE := by
    apply lintegral_congr
    intro uE
    apply lintegral_congr
    intro aE
    exact htail uE aE
  rw [htails]
  let F : V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource B → ENNReal :=
    fun zE => ∫⁻ w, f (zR, zE, w) ∂μG
  have hFE : Measurable (fun z :
      V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource B ×
        V.CliffordGeneralSpinHorizontalIntegralTail E =>
      f (zR, z.1, z.2)) :=
    hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hF : Measurable F := hFE.lintegral_prod_right'
  calc
    (∫⁻ uE, ∫⁻ aE, F (pairE (uE, aE)) ∂μA ∂μE) =
        ∫⁻ z, F (pairE z) ∂μE.prod μA := by
      symm
      exact lintegral_prod _ (hF.comp hpairE).aemeasurable
    _ = ∫⁻ zE, F zE ∂Measure.map pairE (μE.prod μA) := by
      exact (lintegral_map hF hpairE).symm
    _ = ∫⁻ zE, ∫⁻ w, f (zR, zE, w) ∂μG ∂(κE ∘ₘ μES) := by
      rw [hmapE]

end PositiveDefiniteIntegralLattice

end
