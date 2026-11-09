import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedOuterProductReassociation

/-!
# Identify the retained cylinder integration order

The retained vertical source has already been expanded in the only order in
which the definition-only good-tail lift is used safely: the normalized Spin
tail is outside the `SO`-indexed central fiber, and the differential scalar
tail is inside it.  This file identifies the result of that ordered integral
with the horizontal reassociation-kernel bind.
-/

noncomputable section

open MeasureTheory Measure
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

local instance retainedCylinderOrderDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedCylinderOrderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

noncomputable local instance retainedCylinderOrderPadicSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance retainedCylinderOrderPadicSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance retainedCylinderOrderHeightOneSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance retainedCylinderOrderHeightOneSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance retainedCylinderOrderHeightOneSOSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    L.rationalQuadraticSpaceMatrix.pairingMatrix
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance retainedCylinderOrderIntegralSOFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  Subtype.borelSpace _

local instance retainedCylinderOrderIntegralSOFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedCylinderOrderIntegralSOTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedCylinderOrderIntegralSOTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Pi.borelSpace

private theorem retainedCylinderOrder_parallelComp_bind_prod
    {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (κ : ProbabilityTheory.Kernel A C) (η : ProbabilityTheory.Kernel B D)
    [ProbabilityTheory.IsSFiniteKernel κ] [ProbabilityTheory.IsSFiniteKernel η]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] :
    (κ ∥ₖ η) ∘ₘ (μ.prod ν) = (κ ∘ₘ μ).prod (η ∘ₘ ν) := by
  let kμ := ProbabilityTheory.Kernel.const Unit μ
  let kν := ProbabilityTheory.Kernel.const Unit ν
  have h := ProbabilityTheory.Kernel.parallelComp_comp_prod
    (κ := kμ) (κ' := kν) (η := κ) (η' := η)
  have h' := congrArg (fun k => k ()) h
  simpa only [ProbabilityTheory.Kernel.comp_apply,
    ProbabilityTheory.Kernel.prod_apply,
    ProbabilityTheory.Kernel.const_apply] using h'

set_option backward.isDefEq.respectTransparency false in
private theorem retainedCylinderOrder_realPairKernel_comp_spinMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    L.cliffordGeneralSpinHorizontalRealDifferentialPairKernel ∘ₘ
        L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure =
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
        L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let μS := V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let μA := RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  let realSpinChart := V.realCliffordSpinCandidateIdentityChart
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe realSpinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite μS := by
    rw [show μS = V.realCliffordSpinCandidateIdentityChartSourceMeasure by rfl,
      RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact realSpinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
    Measure.IsHaarMeasure.sigmaFinite _
  letI : SigmaFinite μA := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [show μA =
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure by rfl,
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure,
      map_comap_subtype_coe (Rat.unitSquareIdentityChart ℝ).open_source.measurableSet]
    infer_instance
  change
    ((ProbabilityTheory.Kernel.id ×ₖ ProbabilityTheory.Kernel.const _ μA).map Prod.swap) ∘ₘ μS =
      μA.prod μS
  rw [← Measure.map_comp _ _ measurable_swap]
  rw [← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  exact Measure.prod_swap

set_option backward.isDefEq.respectTransparency false in
/-- The horizontal reassociation bind is exactly the product measure exposed
by the retained outer integral: real differential/Spin pair, exceptional
reassociation bind, and normalized horizontal `GSpin` tail. -/
theorem cliffordGeneralSpinHorizontalReassociationBind_eq_retainedProducts
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let μR :=
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
        V.realCliffordSpinCandidateIdentityChartSourceMeasure
    let μES := V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B
    let κE := L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B
    let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
    L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel S ∘ₘ
        V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B =
      μR.prod ((κE ∘ₘ μES).prod μG) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μSpinR := V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let μES := V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B
  let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
  let κR := L.cliffordGeneralSpinHorizontalRealDifferentialPairKernel
  let κE := L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B
  let κT := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
    E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
  let μR :=
    RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod μSpinR
  let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
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
  letI : SigmaFinite μES := by infer_instance
  letI : SigmaFinite μSO := IsFiniteMeasure.toSigmaFinite _
  letI : ProbabilityTheory.IsSFiniteKernel κR := by
    unfold κR cliffordGeneralSpinHorizontalRealDifferentialPairKernel
    infer_instance
  letI : ProbabilityTheory.IsSFiniteKernel κE := by
    unfold κE cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel
    infer_instance
  have hR : κR ∘ₘ μSpinR = μR :=
    L.retainedCylinderOrder_realPairKernel_comp_spinMeasure
  have hT : κT ∘ₘ μSO = μG :=
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_normalizedSO_canonical
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  change (κR ∥ₖ (κE ∥ₖ κT)) ∘ₘ (μSpinR.prod (μES.prod μSO)) =
    μR.prod ((κE ∘ₘ μES).prod μG)
  calc
    _ = (κR ∘ₘ μSpinR).prod ((κE ∥ₖ κT) ∘ₘ (μES.prod μSO)) :=
      retainedCylinderOrder_parallelComp_bind_prod κR (κE ∥ₖ κT)
        μSpinR (μES.prod μSO)
    _ = (κR ∘ₘ μSpinR).prod ((κE ∘ₘ μES).prod (κT ∘ₘ μSO)) := by
      rw [retainedCylinderOrder_parallelComp_bind_prod κE κT μES μSO]
    _ = _ := by rw [hR, hT]

/-- The ordered retained-cylinder integral is the horizontal differential
reassociation bind.  It is used in place of a global map through the
definition-only good-tail lift, which is not available. -/
theorem lintegral_cliffordGeneralSpinVerticalRetainedCylinderIntegrationOrder
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
      ∫⁻ w, f w
        ∂(L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel S ∘ₘ
          V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B) := by
  dsimp only
  rw [L.lintegral_cliffordGeneralSpinVerticalRetainedOuterProductReassociation S f hf]
  rw [L.cliffordGeneralSpinHorizontalReassociationBind_eq_retainedProducts S]
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μR :=
    RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
      V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let μES := V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B
  let κE := L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B
  let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
  letI : SigmaFinite μES := by infer_instance
  letI : ProbabilityTheory.IsSFiniteKernel κE := by
    unfold κE cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel
    infer_instance
  letI : IsProbabilityMeasure μG :=
    V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isProbability E
  letI : IsFiniteMeasure μG := by infer_instance
  letI : SigmaFinite μG := IsFiniteMeasure.toSigmaFinite _
  letI : SFinite (κE ∘ₘ μES) := by infer_instance
  rw [lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro zR
  have hzR : Measurable (fun z :
      V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource B ×
        V.CliffordGeneralSpinHorizontalIntegralTail E =>
      f (zR, z.1, z.2)) :=
    hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  rw [lintegral_prod _ hzR.aemeasurable]

/-- Mapping the ordered horizontal reassociation bind into intrinsic
full-adelic `GSpin` gives the already calibrated differential cylinder. -/
theorem map_cliffordGeneralSpinHorizontalReassociationBind_eq_fullAdelicCylinder
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    Measure.map
        (V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E)
        (L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel S ∘ₘ
          V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B) =
      L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let κ := L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel S
  let μ := V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B
  let F := V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  let η := ProbabilityTheory.Kernel.comap
    (L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart E)
    (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
    (V.measurable_cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
  rw [Measure.map_comp μ κ
    (V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E)]
  have hpoint : κ.map F = η := by
    ext x s hs
    rw [ProbabilityTheory.Kernel.map_apply _
      (V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E)]
    rw [L.map_cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel_apply S x]
  rw [hpoint]
  exact
    L.comap_fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_comp_fullSOChartSourceMeasure
      S

/-- Full-adelic form of the ordered retained-cylinder reassociation.  Every
real, exceptional, scalar-tail, Spin-tail, and `SO`-tail coordinate is
absorbed by the differential cylinder, with coefficient one. -/
theorem lintegral_cliffordGeneralSpinVerticalRetainedCylinderIntegrationOrder_fullAdelic
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ENNReal)
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
    let pairE := L.cliffordGeneralSpinVerticalRetainedExceptionalDifferentialPairMap S
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    let toFull := V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
    (∫⁻ zR, ∫⁻ uE, ∫⁻ aE, ∫⁻ u, ∫⁻ q, ∫⁻ a,
        f (toFull (zR, pairE (uE, aE), fun v =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) *
            L.retainedIntegralSpinTailAction S u v * g q v))
      ∂μScalar ∂μSO ∂μSpin ∂μA ∂μE ∂μR) =
      ∫⁻ w, f w
        ∂L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure
          S := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μ :=
    L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel S ∘ₘ
      V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B
  let toFull := V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  have htoFull : Measurable toFull :=
    V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  have hordered :=
    L.lintegral_cliffordGeneralSpinVerticalRetainedCylinderIntegrationOrder S
      (fun w => f (toFull w)) (hf.comp htoFull)
  rw [hordered]
  rw [← lintegral_map hf htoFull]
  rw [L.map_cliffordGeneralSpinHorizontalReassociationBind_eq_fullAdelicCylinder S]

end PositiveDefiniteIntegralLattice

end
