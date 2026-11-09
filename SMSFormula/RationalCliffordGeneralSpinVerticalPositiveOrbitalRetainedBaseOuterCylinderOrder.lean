import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedBaseOuterOrder

/-!
# Put the retained base integral into cylinder order

The retained-base integral has a fixed normalized Spin source, and the
good-tail theorem accepts the remaining Spin coordinates as a measurable
parameter.  This file joins those facts to the full-adelic cylinder
identity.  The definition-only good-tail lift stays inside its iterated
integral; no global section or Cartesian `SO` tail is formed.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1400000
set_option maxHeartbeats 4400000

local instance retainedBaseOuterCylinderOrderDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedBaseOuterCylinderOrderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance retainedBaseOuterCylinderOrderRealSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance retainedBaseOuterCylinderOrderRealSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedBaseOuterCylinderOrderFiniteSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedBaseOuterCylinderOrderFiniteSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedBaseOuterCylinderOrderRealGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup :=
  borel _

local instance retainedBaseOuterCylinderOrderRealGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance retainedBaseOuterCylinderOrderFiniteGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance retainedBaseOuterCylinderOrderFiniteGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance retainedBaseOuterCylinderOrderFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance retainedBaseOuterCylinderOrderFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- Rotate two independent product sources from `(A × B) × (C × D)` to
`(A × C) × D × B`.  This is used only after the good-tail lift has been
removed, so every displayed function is genuinely measurable. -/
private theorem lintegral_prod_prod_rotate
    {A B C D W : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace D] [MeasurableSpace W]
    (μA : Measure A) (μB : Measure B) (μC : Measure C)
    (μD : Measure D) (μW : Measure W)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] [SFinite μW]
    (f : (A × B) × ((C × D) × W) → ENNReal)
    (hf : Measurable f) :
    (∫⁻ z, ∫⁻ p, ∫⁻ w, f (z, (p, w)) ∂μW ∂(μC.prod μD) ∂(μA.prod μB)) =
      ∫⁻ z, ∫⁻ d, ∫⁻ b, ∫⁻ w,
        f ((z.1, b), ((z.2, d), w)) ∂μW ∂μB ∂μD ∂(μA.prod μC) := by
  let H : (A × B) × (C × D) → ENNReal := fun z => ∫⁻ w, f (z.1, (z.2, w)) ∂μW
  have hf' : Measurable (fun z : ((A × B) × (C × D)) × W =>
      f (z.1.1, (z.1.2, z.2))) :=
    hf.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hH : Measurable H := hf'.lintegral_prod_right'
  let K : A × B → ENNReal := fun z => ∫⁻ p, H (z, p) ∂(μC.prod μD)
  have hK : Measurable K := hH.lintegral_prod_right'
  have hswap (a : A) :
      (∫⁻ b, ∫⁻ p, H ((a, b), p) ∂(μC.prod μD) ∂μB) =
        ∫⁻ p, ∫⁻ b, H ((a, b), p) ∂μB ∂(μC.prod μD) := by
    let F : B × (C × D) → ENNReal := fun z => H ((a, z.1), z.2)
    have hF : Measurable F := hH.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    calc
      (∫⁻ b, ∫⁻ p, H ((a, b), p) ∂(μC.prod μD) ∂μB) =
          ∫⁻ z, F z ∂μB.prod (μC.prod μD) :=
        (lintegral_prod F hF.aemeasurable).symm
      _ = ∫⁻ p, ∫⁻ b, H ((a, b), p) ∂μB ∂(μC.prod μD) :=
        lintegral_prod_symm' F hF
  have hafterSwap :
      (∫⁻ a, ∫⁻ b, ∫⁻ p, H ((a, b), p) ∂(μC.prod μD) ∂μB ∂μA) =
        ∫⁻ a, ∫⁻ p, ∫⁻ b, H ((a, b), p) ∂μB ∂(μC.prod μD) ∂μA := by
    apply lintegral_congr
    exact hswap
  have hpMeas (a : A) : Measurable (fun p : C × D =>
      ∫⁻ b, H ((a, b), p) ∂μB) := by
    have ha : Measurable (fun _ : (C × D) × B => a) := measurable_const
    have h : Measurable (fun z : (C × D) × B => H ((a, z.2), z.1)) :=
      hH.comp ((ha.prodMk measurable_snd).prodMk measurable_fst)
    exact h.lintegral_prod_right'
  have hacMeas : Measurable (fun z : A × C =>
      ∫⁻ d, ∫⁻ b, H ((z.1, b), (z.2, d)) ∂μB ∂μD) := by
    have h : Measurable (fun z : ((A × C) × D) × B =>
        H ((z.1.1.1, z.2), (z.1.1.2, z.1.2))) :=
      hH.comp
        ((((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
            measurable_snd)).prodMk
          ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
            (measurable_snd.comp measurable_fst)))
    exact (h.lintegral_prod_right').lintegral_prod_right'
  calc
    (∫⁻ z, ∫⁻ p, ∫⁻ w, f (z, (p, w)) ∂μW ∂(μC.prod μD) ∂(μA.prod μB)) =
        ∫⁻ a, ∫⁻ b, ∫⁻ p, H ((a, b), p) ∂(μC.prod μD) ∂μB ∂μA := by
      exact lintegral_prod K hK.aemeasurable
    _ = ∫⁻ a, ∫⁻ p, ∫⁻ b, H ((a, b), p) ∂μB ∂(μC.prod μD) ∂μA :=
      hafterSwap
    _ = ∫⁻ a, ∫⁻ c, ∫⁻ d, ∫⁻ b,
        H ((a, b), (c, d)) ∂μB ∂μD ∂μC ∂μA := by
      apply lintegral_congr
      intro a
      exact lintegral_prod _ (hpMeas a).aemeasurable
    _ = ∫⁻ z, ∫⁻ d, ∫⁻ b, ∫⁻ w,
        f ((z.1, b), ((z.2, d), w)) ∂μW ∂μB ∂μD ∂(μA.prod μC) := by
      exact (lintegral_prod _ hacMeas.aemeasurable).symm

/-- At a retained base point, the literal raw-cylinder orbit is the
horizontal split reconstruction with the displayed real, exceptional, and
good-tail coordinates. -/
theorem cliffordGeneralSpinVerticalRetainedBaseLiteralOrbit_eq_toFull
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : (Rat.unitSquareIdentityChart ℝ).source ×
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (q : L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (a : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (uR : L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChart.source)
    (uE : L.rationalQuadraticSpaceMatrix
      |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (huE : uE ∈ L.rationalQuadraticSpaceMatrix.retainedSpinExceptionalIdentityCarrier
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (u : L.rationalQuadraticSpaceMatrix
      |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q
    let pairE := L.cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) q
    let toFull := V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
    L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S x
        ((z.1, z.2, a), (uR, (uE, u))) =
      toFull ((z.1, uR), pairE (uE, z.2), fun v =>
        V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
          L.retainedIntegralSpinTailAction S u v * g v) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q
  let root : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource B :=
    (z.1, z.2, a)
  let spin : L.CliffordGeneralSpinVerticalRetainedSpinSource S := (uR, (uE, u))
  have hrec :=
    L.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic_retainedCylinder
      S x (root, spin) huE
  symm
  simpa only [x, root, spin,
    L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin_tail,
    cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit,
    cliffordGeneralSpinVerticalRetainedCylinderToSplit,
    cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap] using hrec

set_option backward.isDefEq.respectTransparency false in
/-- The normalized retained-base integral is exactly the calibrated
full-adelic differential cylinder.  This is the final integration-order
comparison before restoring the raw finite block coefficient. -/
theorem lintegral_cliffordGeneralSpinVerticalRetainedBaseNormalizedOrder_fullAdelic
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let μRE :=
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure
          B)
    let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
    let μScalar :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
    let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S
    let ν := L.cliffordGeneralSpinVerticalRetainedSpinSourceMeasure S
    (∫⁻ z, ∫⁻ q, ∫⁻ a, ∫⁻ u,
        f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
          ((z.1, z.2, a), u))
      ∂ν ∂μScalar ∂μSO ∂μRE) =
      ∫⁻ w, f w
        ∂L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure
          S := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μAR := RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure
  let μAE :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure B
  let μSpinR := V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let μSpinEAmb := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B
  let CE := V.retainedSpinExceptionalIdentityCarrier B
  let μSpinE := μSpinEAmb.restrict CE
  let μSpin := V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B
  let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
  let μScalar :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
  let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
  let ρ := μSpinR.prod μSpinE
  let ν := L.cliffordGeneralSpinVerticalRetainedSpinSourceMeasure S
  let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S
  let pairE := L.cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
  let toFull := V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  let realSpinChart := V.realCliffordSpinCandidateIdentityChart
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe realSpinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite μSpinR := by
    rw [show μSpinR = V.realCliffordSpinCandidateIdentityChartSourceMeasure by rfl,
      RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact realSpinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite μSpinEAmb :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite B
  letI : SigmaFinite μSpinE := by infer_instance
  letI : IsProbabilityMeasure μSpin :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability B
  letI : IsFiniteMeasure μSpin := by infer_instance
  letI : SigmaFinite μSpin := IsFiniteMeasure.toSigmaFinite _
  letI : IsFiniteMeasure μSO := by infer_instance
  letI : SigmaFinite μSO := IsFiniteMeasure.toSigmaFinite _
  letI : IsFiniteMeasure μScalar := by infer_instance
  letI : SigmaFinite μScalar := IsFiniteMeasure.toSigmaFinite _
  letI : IsProbabilityMeasure μG :=
    V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isProbability E
  letI : IsFiniteMeasure μG := by infer_instance
  letI : SigmaFinite μG := IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
    Measure.IsHaarMeasure.sigmaFinite _
  letI : SigmaFinite μAR := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [show μAR =
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure by rfl,
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure,
      map_comap_subtype_coe (Rat.unitSquareIdentityChart ℝ).open_source.measurableSet]
    infer_instance
  letI : SigmaFinite μAE := by infer_instance
  letI : SFinite ρ := by infer_instance
  have hpairE : Measurable pairE :=
    L.measurable_cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S
  have htoFull : Measurable toFull :=
    V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  have hν : ν = μSpinR.prod (μSpinE.prod μSpin) := by
    simpa only [ν, μSpinR, μSpinE, μSpinEAmb, CE, μSpin, V, E, B] using
      L.cliffordGeneralSpinVerticalRetainedSpinSourceMeasure_eq_split S
  have hroot (z : (Rat.unitSquareIdentityChart ℝ).source ×
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource B) :
      (∫⁻ q, ∫⁻ a, ∫⁻ u,
          f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
            ((z.1, z.2, a), u)) ∂ν ∂μScalar ∂μSO) =
        ∫⁻ p, ∫⁻ w,
          f (toFull ((z.1, p.1), pairE (p.2, z.2), w)) ∂μG ∂ρ := by
    let F :
        (V.realCliffordSpinCandidateIdentityChart.source ×
            V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) ×
          V.CliffordGeneralSpinHorizontalIntegralTail E → ENNReal :=
      fun y => f (toFull ((z.1, y.1.1), pairE (y.1.2, z.2), y.2))
    have hF : Measurable F := by
      apply hf.comp
      apply htoFull.comp
      exact (measurable_const.prodMk (measurable_fst.comp measurable_fst)).prodMk
        ((hpairE.comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_const)).prodMk
            measurable_snd)
    have htailJoint
        (q : V.FiniteAdelicSpecialOrthogonalIntegralTail B)
        (a : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B) :
        Measurable (fun y :
            (V.realCliffordSpinCandidateIdentityChart.source ×
                V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) ×
              V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B =>
          F (y.1, fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S y.2 v * g q v)) := by
      apply hF.comp
      exact measurable_fst.prodMk
        (measurable_pi_lambda _ fun v =>
          Measurable.subtype_mk
            (((continuous_subtype_val.measurable.comp
              ((V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom E v).measurable
                |>.comp measurable_const)).mul
              (continuous_subtype_val.measurable.comp
                ((L.measurable_retainedIntegralSpinTailAction S v).comp measurable_snd))).mul_const
                  (g q v).1))
    have horiginal
        (q : V.FiniteAdelicSpecialOrthogonalIntegralTail B)
        (a : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B) :
        Measurable (fun u : L.CliffordGeneralSpinVerticalRetainedSpinSource S =>
          f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
            ((z.1, z.2, a), u))) := by
      let root : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource B :=
        (z.1, z.2, a)
      let c := RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V RationalAdele
          (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B root)
      have hleft : Measurable (fun w : V.FullAdelicCliffordGeneralSpinGroup => c * w) :=
        (continuous_const.mul continuous_id).measurable
      apply hf.comp
      simpa only [root, c, Prod.fst, Prod.snd,
        cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit] using
        hleft.comp
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.continuous.measurable.comp
            (L.measurable_retainedRealFiniteSpinSourceOrbit S (x q)))
    have hexpand :
        (∫⁻ q, ∫⁻ a, ∫⁻ u,
            f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
              ((z.1, z.2, a), u)) ∂ν ∂μScalar ∂μSO) =
          ∫⁻ q, ∫⁻ a, ∫⁻ uR, ∫⁻ uE, ∫⁻ u,
            f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
              ((z.1, z.2, a), (uR, (uE, u))))
          ∂μSpin ∂μSpinE ∂μSpinR ∂μScalar ∂μSO := by
      apply lintegral_congr
      intro q
      apply lintegral_congr
      intro a
      rw [hν]
      rw [lintegral_prod _ (horiginal q a).aemeasurable]
      apply lintegral_congr
      intro uR
      have h : Measurable (fun y :
          V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
            V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B =>
          f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
            ((z.1, z.2, a), (uR, y)))) :=
        (horiginal q a).comp (measurable_const.prodMk
          (measurable_fst.prodMk measurable_snd))
      exact lintegral_prod _ h.aemeasurable
    rw [hexpand]
    have hreplace :
        (∫⁻ q, ∫⁻ a, ∫⁻ uR, ∫⁻ uE, ∫⁻ u,
            f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
              ((z.1, z.2, a), (uR, (uE, u))))
          ∂μSpin ∂μSpinE ∂μSpinR ∂μScalar ∂μSO) =
          ∫⁻ q, ∫⁻ a, ∫⁻ uR, ∫⁻ uE, ∫⁻ u,
            F ((uR, uE), fun v =>
              V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
                L.retainedIntegralSpinTailAction S u v * g q v)
          ∂μSpin ∂μSpinE ∂μSpinR ∂μScalar ∂μSO := by
      apply lintegral_congr
      intro q
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro uR
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (V.measurableSet_retainedSpinExceptionalIdentityCarrier B)]
        with uE huE
      apply lintegral_congr
      intro u
      apply congrArg f
      exact L.cliffordGeneralSpinVerticalRetainedBaseLiteralOrbit_eq_toFull
        S z q a uR uE huE u
    rw [hreplace]
    have hassociate :
        (∫⁻ q, ∫⁻ a, ∫⁻ uR, ∫⁻ uE, ∫⁻ u,
            F ((uR, uE), fun v =>
              V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
                L.retainedIntegralSpinTailAction S u v * g q v)
          ∂μSpin ∂μSpinE ∂μSpinR ∂μScalar ∂μSO) =
          ∫⁻ q, ∫⁻ a, ∫⁻ p, ∫⁻ u,
            F (p, fun v =>
              V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
                L.retainedIntegralSpinTailAction S u v * g q v)
          ∂μSpin ∂ρ ∂μScalar ∂μSO := by
      apply lintegral_congr
      intro q
      apply lintegral_congr
      intro a
      let K :
          V.realCliffordSpinCandidateIdentityChart.source ×
              V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B → ENNReal :=
        fun p => ∫⁻ u, F (p, fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
            L.retainedIntegralSpinTailAction S u v * g q v) ∂μSpin
      have hK : Measurable K := (htailJoint q a).lintegral_prod_right'
      exact (lintegral_prod K hK.aemeasurable).symm
    rw [hassociate]
    simpa only [F, ρ, μSpin, μSO, μScalar, μG, V, E, B, g, pairE, toFull] using
      L.lintegral_retainedIntegralScalarSpinTail_centralFiberBind_baseOrder_param
        S ρ F hF
  have hbase :
      (∫⁻ z, ∫⁻ q, ∫⁻ a, ∫⁻ u,
          f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
            ((z.1, z.2, a), u)) ∂ν ∂μScalar ∂μSO ∂(μAR.prod μAE)) =
        ∫⁻ z, ∫⁻ p, ∫⁻ w,
          f (toFull ((z.1, p.1), pairE (p.2, z.2), w)) ∂μG ∂ρ ∂(μAR.prod μAE) := by
    apply lintegral_congr
    exact hroot
  rw [hbase]
  have hcollapsed := lintegral_prod_prod_rotate μAR μAE μSpinR μSpinE μG
    (fun y => f (toFull ((y.1.1, y.2.1.1), pairE (y.2.1.2, y.1.2), y.2.2)))
    (by
      apply hf.comp
      apply htoFull.comp
      exact ((measurable_fst.comp measurable_fst).prodMk
          (measurable_fst.comp (measurable_fst.comp measurable_snd))).prodMk
        ((hpairE.comp
          ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
            (measurable_snd.comp measurable_fst))).prodMk
          (measurable_snd.comp measurable_snd))
    )
  rw [hcollapsed]
  have htail (zR : (Rat.unitSquareIdentityChart ℝ).source ×
      V.realCliffordSpinCandidateIdentityChart.source)
      (uE : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B)
      (aE : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource B) :
      (∫⁻ w, f (toFull (zR, pairE (uE, aE), w)) ∂μG) =
        ∫⁻ u, ∫⁻ q, ∫⁻ a,
          f (toFull (zR, pairE (uE, aE), fun v =>
            V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
              L.retainedIntegralSpinTailAction S u v * g q v))
        ∂μScalar ∂μSO ∂μSpin := by
    symm
    simpa only [μSpin, μSO, μScalar, μG, V, E, B, g] using
      L.lintegral_retainedIntegralScalarSpinTail_centralFiberBind S
        (fun w => f (toFull (zR, pairE (uE, aE), w)))
        (hf.comp (htoFull.comp
          (measurable_const.prodMk (measurable_const.prodMk measurable_id))))
  apply Eq.trans ?_ (L.lintegral_cliffordGeneralSpinVerticalRetainedCylinderIntegrationOrder_fullAdelic
    S f hf)
  apply lintegral_congr
  intro zR
  apply lintegral_congr
  intro uE
  apply lintegral_congr
  exact htail zR uE

/-- Retained-carrier form of `(V)`: the restricted positive-idèle orbital
bind is the calibrated horizontal differential cylinder multiplied by the
unique raw finite Spin-block coefficient. -/
theorem lintegral_positiveSpinOrbitalKernelRestrictIdentityChart_retainedBase_eq_block_mul_horizontalCylinder
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let c : ℝ≥0∞ := (D.spinFiniteScale : ℝ≥0∞) *
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B
    (∫⁻ b, ∫⁻ w, f w
        ∂L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S b
      ∂(RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure.restrict
        (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier B))) =
      c * ∫⁻ w, f w
        ∂L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure
          S := by
  dsimp only
  rw [L.lintegral_positiveSpinOrbitalKernelRestrictIdentityChart_retainedBase_eq_block_mul_normalized
    hr D S f hf]
  rw [L.lintegral_cliffordGeneralSpinVerticalRetainedBaseNormalizedOrder_fullAdelic S f hf]

end PositiveDefiniteIntegralLattice

end
