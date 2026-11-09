import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedExceptionalSourceReassociation

/-!
# Reassociate the retained exceptional differential source

The retained vertical cylinder presents its exceptional coordinate as a
differential square source paired with the ambient admissible Spin product
restricted to the identity carrier.  The preceding integral-level source
theorem changes variables to the existing horizontal Spin chart source.  This
file pairs those variables and identifies the resulting measure with the
horizontal exceptional reassociation-kernel bind.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 900000
set_option maxHeartbeats 3000000

local instance retainedExceptionalDifferentialDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedExceptionalDifferentialPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Pair a differential exceptional square coordinate with the totalized
retained exceptional Spin coordinate.  On the restricted source the latter
is the existing horizontal chart point. -/
def cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
        RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource B →
      V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource B := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  exact fun z v => (z.2 v, L.retainedExceptionalSpinIdentityChartTotal S z.1 v)

theorem measurable_cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (L.cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S) := by
  unfold cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap
  apply measurable_pi_lambda
  intro v
  exact ((measurable_pi_apply v).comp measurable_snd).prodMk
    ((measurable_pi_apply v).comp
      ((L.measurable_retainedExceptionalSpinIdentityChartTotal S).comp measurable_fst))

/-- After the exceptional-source inclusion, the retained differential pair map
is componentwise the existing horizontal scalar/Spin pairing. -/
theorem cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap_source_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.CliffordGeneralSpinHorizontalExceptionalSOChartSource B)
    (a : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource B) :
    L.cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S
        (L.retainedExceptionalSpinChartSourceToAdmissibleProduct S x, a) =
      fun v => (a v, x v) := by
  funext v
  apply Prod.ext
  · rfl
  · exact L.retainedExceptionalSpinIdentityChartTotal_sourceToAdmissibleProduct_apply S x v

/-- The restricted retained exceptional differential source is exactly the
existing exceptional reassociation-kernel bind.  In particular, this final
exceptional pairing contributes coefficient one. -/
theorem map_retainedExceptionalDifferentialPair_eq_kernel_comp_source
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    Measure.map
        (L.cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S)
        (((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
            (V.retainedSpinExceptionalIdentityCarrier B)).prod
          (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure
            B)) =
      L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B ∘ₘ
        V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μE :=
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
      (V.retainedSpinExceptionalIdentityCarrier B)
  let μA :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure B
  let μS := V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B
  let pairAmbient := L.cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S
  let pairChart := fun z :
      V.CliffordGeneralSpinHorizontalExceptionalSOChartSource B ×
        RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource B =>
      fun v => (z.2 v, z.1 v)
  have hpairAmbient : Measurable pairAmbient :=
    L.measurable_cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S
  have hpairChart : Measurable pairChart := by
    apply measurable_pi_lambda
    intro v
    exact ((measurable_pi_apply v).comp measurable_snd).prodMk
      ((measurable_pi_apply v).comp measurable_fst)
  have hsource : Measure.map pairAmbient (μE.prod μA) =
      Measure.map pairChart (μS.prod μA) := by
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply hpairAmbient hs, Measure.map_apply hpairChart hs]
    let F : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B → ENNReal :=
      fun u => ∫⁻ a, (pairAmbient ⁻¹' s).indicator (fun _ => 1) (u, a) ∂μA
    have hindicatorAmbient : Measurable
        ((pairAmbient ⁻¹' s).indicator (fun _ => (1 : ENNReal))) :=
      measurable_const.indicator (hs.preimage hpairAmbient)
    have hF : Measurable F := hindicatorAmbient.lintegral_prod_right'
    calc
      (μE.prod μA) (pairAmbient ⁻¹' s) =
          ∫⁻ z, (pairAmbient ⁻¹' s).indicator (fun _ => 1) z ∂μE.prod μA := by
        rw [lintegral_indicator_const (hs.preimage hpairAmbient)]
        simp
      _ = ∫⁻ u, F u ∂μE :=
        lintegral_prod _ hindicatorAmbient.aemeasurable
      _ = ∫⁻ x, F (L.retainedExceptionalSpinChartSourceToAdmissibleProduct S x) ∂μS := by
        exact L.lintegral_retainedExceptionalSpinSource_to_horizontalChart S F hF
      _ = ∫⁻ x, ∫⁻ a,
          (pairChart ⁻¹' s).indicator (fun _ => 1) (x, a) ∂μA ∂μS := by
        apply lintegral_congr
        intro x
        apply lintegral_congr
        intro a
        have hp : pairAmbient
            (L.retainedExceptionalSpinChartSourceToAdmissibleProduct S x, a) =
              pairChart (x, a) := by
          exact L.cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap_source_apply
            S x a
        change s.indicator (fun _ => 1) (pairAmbient
            (L.retainedExceptionalSpinChartSourceToAdmissibleProduct S x, a)) =
          s.indicator (fun _ => 1) (pairChart (x, a))
        rw [hp]
      _ = ∫⁻ z, (pairChart ⁻¹' s).indicator (fun _ => 1) z ∂μS.prod μA := by
        symm
        exact lintegral_prod _
          (measurable_const.indicator (hs.preimage hpairChart)).aemeasurable
      _ = (μS.prod μA) (pairChart ⁻¹' s) := by
        rw [lintegral_indicator_const (hs.preimage hpairChart)]
        simp
  calc
    Measure.map pairAmbient (μE.prod μA) = Measure.map pairChart (μS.prod μA) := hsource
    _ = L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B ∘ₘ μS := by
      unfold cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel
      rw [← Measure.map_comp _ _ hpairChart]
      rw [← Measure.compProd_eq_comp_prod, Measure.compProd_const]

end PositiveDefiniteIntegralLattice

end
