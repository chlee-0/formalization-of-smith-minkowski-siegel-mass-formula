import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedCylinderReassociationMap

/-!
# Full-adelic reconstruction of the retained vertical cylinder

The measurable retained-cylinder split map is reconstructed in the
full-adelic `GSpin` group.  On the retained exceptional identity carrier its
value is exactly the full differential scalar multiplied by the translated
Spin orbit through the retained horizontal origin.  The proof compares exact
real and height-one finite components; it does not choose a further good-tail lift.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 900000
set_option maxHeartbeats 3000000

local instance retainedCylinderReconstructionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedCylinderReconstructionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Reconstructing the retained square--Spin split is the literal full
differential scalar times the translated Spin orbit, on the retained carrier.
-/
theorem cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic_retainedCylinder
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (z : L.CliffordGeneralSpinVerticalRetainedCylinderSource S)
    (hz : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      z.2.2.1 ∈ V.retainedSpinExceptionalIdentityCarrier B) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
        (L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x z) =
      RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele
          (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
            B z.1) *
        V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
          (L.retainedRealFiniteSpinSourceOrbit S x z.2) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let w := L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x z
  let y := (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph E).symm w
  have hy : V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph E y = w :=
    (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph E).apply_symm_apply w
  rw [V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph_apply] at hy
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteChartSplit
    RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalExceptionalChartSplit at hy
  change V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E w = _
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic
  simp only [Function.comp_apply]
  apply V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.injective
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient
  change V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
      (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient E y)) =
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
      (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele
          (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
            B z.1) *
        V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
          (L.retainedRealFiniteSpinSourceOrbit S x z.2))
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply,
    map_mul,
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_scalarGroupHom,
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply]
  unfold RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
  simp only [Function.comp_apply]
  rw [RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv.apply_symm_apply]
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient
  apply Prod.ext
  · have hyR := congrArg (fun q ↦ q.1) hy
    have hyScalar : ((y.1 : ℝˣ × V.RealCliffordSpinCandidateGroup)).1 = z.1.1 := by
      simpa [w] using congrArg (fun q ↦ (q.1 : ℝˣ)) hyR
    have hySpin : ((y.1 : ℝˣ × V.RealCliffordSpinCandidateGroup)).2 = z.2.1 := by
      simpa [w] using congrArg (fun q ↦ (q.2 : V.RealCliffordSpinCandidateGroup)) hyR
    change V.cliffordGeneralSpinCentralSpinMultiplication ℝ
        (y.1 : ℝˣ × V.RealCliffordSpinCandidateGroup) =
      RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V ℝ (z.1.1 : ℝˣ) *
        (L.retainedRealFiniteSpinSourceOrbit S x z.2).1
    rw [L.retainedRealFiniteSpinSourceOrbit_fst S x z.2]
    unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinCentralSpinMultiplication
    rw [hyScalar, hySpin]
  · have hyExceptional (v : {v // v ∈ B}) :
        (Homeomorph.Set.prod
            (Rat.unitSquareIdentityChart
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source
            (V.padicCliffordSpinCandidateIdentityChart
              (Rat.HeightOneSpectrum.primesEquiv v.1).1).source (y.2.1 v)) =
          (z.1.2.1 v, L.retainedExceptionalSpinIdentityChartTotal S z.2.2.1 v) := by
      have h := congrArg (fun q ↦ q.2.1 v) hy
      change
        (Homeomorph.Set.prod
            (Rat.unitSquareIdentityChart
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source
            (V.padicCliffordSpinCandidateIdentityChart
              (Rat.HeightOneSpectrum.primesEquiv v.1).1).source (y.2.1 v)) =
          (L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x z).2.1 v at h
      exact h
    have hyTail : y.2.2 = w.2.2 := by
      exact congrArg (fun q ↦ q.2.2) hy
    change V.cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient E y.2 =
      RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalFiniteAdele
          (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
            B z.1.2) *
        (L.retainedRealFiniteSpinSourceOrbit S x z.2).2
    unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient
      RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteChartParameterToSource
    simp only [Function.comp_apply]
    apply V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom_injective
    funext v
    change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient E
          (Prod.map (V.cliffordGeneralSpinHorizontalExceptionalChartToBlock E) id y.2)) =
      V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalFiniteAdele
            (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
              B z.1.2) *
          (L.retainedRealFiniteSpinSourceOrbit S x z.2).2)
    rw [V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
      (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_mul,
      V.finiteAdelicCliffordGeneralSpinHeightOneComponent_scalarGroupHom]
    by_cases hv : v ∈ B
    · have hscalar :
          RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
              (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
                B z.1.2) = z.1.2.1 ⟨v, hv⟩ := by
        rw [RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponent_squareChartToAmbient]
        simp [RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalTailLocalUnit,
          B, hv]
      have hvPair := hyExceptional ⟨v, hv⟩
      have hvScalar :
          (((y.2.1 ⟨v, hv⟩ :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ ×
              V.PadicCliffordSpinCandidateGroup
                (Rat.HeightOneSpectrum.primesEquiv v).1)).1) = z.1.2.1 ⟨v, hv⟩ := by
        simpa using congrArg
          (fun q ↦ (q.1 : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)) hvPair
      have hvSpinChart :
          (((y.2.1 ⟨v, hv⟩ :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ ×
              V.PadicCliffordSpinCandidateGroup
                (Rat.HeightOneSpectrum.primesEquiv v).1)).2) =
            (L.retainedExceptionalSpinIdentityChartTotal S z.2.2.1 ⟨v, hv⟩).1 := by
        simpa using congrArg
          (fun q ↦ (q.2 : V.PadicCliffordSpinCandidateGroup
            (Rat.HeightOneSpectrum.primesEquiv v).1)) hvPair
      have hvSpin := hvSpinChart.trans
        (L.retainedExceptionalSpinIdentityChartTotal_apply_of_mem S z.2.2.1 hz ⟨v, hv⟩)
      rw [L.finiteAdelicCliffordGeneralSpinHeightOneComponent_retainedOrbit_mem
        S x z.2 v hv]
      simp [RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalExceptionalChartToBlock,
        RationalQuadraticSpaceMatrix.cliffordGeneralSpinCentralSpinMultiplication,
        B, hv, hscalar, hvScalar, hvSpin]
      congr 2
    · have hscalar :
          RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
              (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
                B z.1.2) = (z.1.2.2 ⟨v, hv⟩).1 := by
        rw [RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponent_squareChartToAmbient]
        simp [RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalTailLocalUnit,
          B, hv]
      have hyTailAt := congrFun hyTail ⟨v, hv⟩
      have hwTail := L.cliffordGeneralSpinVerticalRetainedCylinderToSplit_tail S x z ⟨v, hv⟩
      have hyTailFormula := hyTailAt.trans hwTail
      rw [L.finiteAdelicCliffordGeneralSpinHeightOneComponent_retainedOrbit_notMem
        S x z.2 v hv]
      simpa [B, hv, hscalar,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
        RationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralScalarHom,
        mul_assoc] using congrArg Subtype.val hyTailFormula

set_option backward.isDefEq.respectTransparency false in
/-- The normalized retained-cylinder source is almost everywhere supported on
the exceptional identity carrier on which reconstruction is literal. -/
theorem ae_cliffordGeneralSpinVerticalRetainedCylinderSource_mem_identityCarrier
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    ∀ᵐ z ∂L.cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure S,
      z.2.2.1 ∈ V.retainedSpinExceptionalIdentityCarrier B := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let C : Set
      (V.realCliffordSpinCandidateIdentityChart.source ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)) :=
    Set.univ ×ˢ (V.retainedSpinExceptionalIdentityCarrier B ×ˢ Set.univ)
  have hC : MeasurableSet C :=
    MeasurableSet.univ.prod
      ((V.measurableSet_retainedSpinExceptionalIdentityCarrier B).prod MeasurableSet.univ)
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite B
  letI : IsProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability B
  letI : IsFiniteMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) := by
    infer_instance
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B) := by
    unfold
      RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
    infer_instance
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  let realSpinChart := V.realCliffordSpinCandidateIdentityChart
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe realSpinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact realSpinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  unfold cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure
    RationalQuadraticSpaceMatrix.retainedSpinExceptionalTailIdentityCylinder
  have hsupport :
      ∀ᵐ z ∂
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure B).prod
          ((V.realCliffordSpinCandidateIdentityChartSourceMeasure.prod
            (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
              B)).restrict C),
        z.2 ∈ C := by
    refine (Measure.ae_prod_iff_ae_ae (hC.preimage measurable_snd)).2 ?_
    filter_upwards [] with a
    exact ae_restrict_mem hC
  exact hsupport.mono fun z hz => hz.2.1

/-- At the level of the normalized source measure, reconstructed split
coordinates and the literal scalar-times-Spin orbit have identical
pushforwards.  Thus the off-carrier totalization disappears before the
remaining nonnegative-integral reassociation. -/
theorem map_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic_retainedCylinder
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    Measure.map
        (fun z => V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
          (L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x z))
        (L.cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure S) =
      Measure.map
        (fun z =>
          RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele
              (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
                B z.1) *
            V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
              (L.retainedRealFiniteSpinSourceOrbit S x z.2))
        (L.cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure S) := by
  dsimp only
  apply Measure.map_congr
  filter_upwards [
    L.ae_cliffordGeneralSpinVerticalRetainedCylinderSource_mem_identityCarrier S] with z hz
  exact L.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic_retainedCylinder S x z hz

end PositiveDefiniteIntegralLattice
