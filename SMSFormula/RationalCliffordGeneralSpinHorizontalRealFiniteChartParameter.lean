import SMSFormula.RationalCliffordGeneralSpinHorizontalIdentityChartGenuineBlock

/-!
# Real--finite horizontal chart parameters

The coherent identity-chart cylinders on genuine finite-adelic `GSpin` are
realized here from their literal scalar/Spin parameters.  Only the finitely
exceptional coordinates are parametrized: the normalized integral tail is
carried unchanged.  The joint central multiplication map then pushes the
block-weighted parameter measure exactly to the coherent finite cylinder.

After adjoining the real identity chart, the same construction gives the
real--finite cylinder used by the ambient horizontal disintegration.  The
separate scalar/Spin splitting remembers the literal real and finite square
moduli; when the dyadic place is exceptional their product is one.  No Euler
product or additional sheet coefficient occurs.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3000000

local instance horizontalRealFiniteChartParameterPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalRealFiniteChartParameterDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance horizontalRealFiniteChartParameterRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance horizontalRealFiniteChartParameterRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance horizontalRealFiniteChartParameterPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance horizontalRealFiniteChartParameterPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance horizontalRealFiniteChartParameterPadicUnitSecondCountable
    (p : ℕ) [Fact (Nat.Prime p)] : SecondCountableTopology ℚ_[p]ˣ := by
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

noncomputable local instance horizontalRealFiniteChartParameterRealSOMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance horizontalRealFiniteChartParameterRealSOBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance horizontalRealFiniteChartParameterPadicSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalRealFiniteChartParameterPadicSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance horizontalRealFiniteChartParameterRealGSpinMeasurableSpace :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) := borel _

noncomputable local instance horizontalRealFiniteChartParameterRealGSpinBorelSpace :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) := ⟨rfl⟩

noncomputable local instance horizontalRealFiniteChartParameterPadicGSpinMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := borel _

noncomputable local instance horizontalRealFiniteChartParameterPadicGSpinBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := ⟨rfl⟩

local instance horizontalRealFiniteChartParameterIntegralFactorSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalRealFiniteChartParameterIntegralFactorBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance horizontalRealFiniteChartParameterExceptionalSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalRealFiniteChartParameterExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance horizontalRealFiniteChartParameterTailSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalRealFiniteChartParameterTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance horizontalRealFiniteChartParameterFiniteGroupMeasurableSpace :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup := borel _

local instance horizontalRealFiniteChartParameterFiniteGroupBorelSpace :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup := ⟨rfl⟩

local instance horizontalRealFiniteChartParameterGenuineBlockBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-! ## Finite chart parameters -/

/-- Finitely exceptional scalar/Spin chart parameters together with the
unchanged normalized good tail. -/
abbrev CliffordGeneralSpinHorizontalFiniteChartParameterSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  V.CliffordGeneralSpinHorizontalExceptionalBlockChartSource S ×
    V.CliffordGeneralSpinHorizontalIntegralTail S

/-- The block-weighted measure on the finite chart parameter source. -/
def cliffordGeneralSpinHorizontalFiniteChartParameterMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalFiniteChartParameterSource S) :=
  V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
    ((V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)).prod
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S))

/-- Central multiplication on the exceptional coordinates, with the good
tail left unchanged. -/
def cliffordGeneralSpinHorizontalFiniteChartParameterToSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalFiniteChartParameterSource S →
      V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S :=
  Prod.map (V.cliffordGeneralSpinHorizontalExceptionalChartToBlock S) id

theorem measurable_cliffordGeneralSpinHorizontalFiniteChartParameterToSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalFiniteChartParameterToSource S) := by
  unfold cliffordGeneralSpinHorizontalFiniteChartParameterToSource
  exact
    (V.continuous_cliffordGeneralSpinHorizontalExceptionalChartToBlock S).measurable.prodMap
      measurable_id

/-- The established sequence from the direct exceptional/tail source through
the restricted block and genuine block into the common finite carrier. -/
def cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S) →
      V.FiniteAdelicCliffordGeneralSpinGroup :=
  V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S ∘
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm ∘
      V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S

theorem measurable_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S) := by
  unfold cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
  exact
    (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S).measurable.comp
      ((V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm.measurable.comp
        (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S).measurable)

/-- The joint finite parameter map into the common intrinsic finite-adelic
`GSpin` carrier. -/
def cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalFiniteChartParameterSource S →
      V.FiniteAdelicCliffordGeneralSpinGroup :=
  V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S ∘
    V.cliffordGeneralSpinHorizontalFiniteChartParameterToSource S

theorem measurable_cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient S) := by
  unfold cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient
  exact
    (V.measurable_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S).comp
      (V.measurable_cliffordGeneralSpinHorizontalFiniteChartParameterToSource S)

set_option backward.isDefEq.respectTransparency false in
/-- The finite chart parameters first map exactly to the weighted direct
exceptional/tail identity-chart cylinder. -/
theorem map_cliffordGeneralSpinHorizontalFiniteChartParameterToSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalFiniteChartParameterToSource S)
        (V.cliffordGeneralSpinHorizontalFiniteChartParameterMeasure S) =
      V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
        V.cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure S := by
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
    unfold cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
    letI (v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
        SigmaFinite
          (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1) := by
      let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
      let productChart := V.padicCliffordGeneralSpinHorizontalProductIdentityChart p
      letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) :=
        Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
      letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
        PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
          p n V.pairingMatrix V.form_symm V.form_det_ne_zero
      letI : SigmaFinite
          (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) := by
        unfold padicCliffordGeneralSpinHorizontalDifferentialProductMeasure
        infer_instance
      letI : SigmaFinite
          (V.padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure p) := by
        apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
        rw [padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure,
          map_comap_subtype_coe productChart.open_target.measurableSet]
        infer_instance
      unfold padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
      exact productChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
    infer_instance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  unfold cliffordGeneralSpinHorizontalFiniteChartParameterToSource
    cliffordGeneralSpinHorizontalFiniteChartParameterMeasure
    cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure
  rw [Measure.map_smul, ← Measure.map_prod_map,
    V.map_cliffordGeneralSpinHorizontalExceptionalChartToBlock S, Measure.map_id]
  all_goals
    first
    | exact (V.continuous_cliffordGeneralSpinHorizontalExceptionalChartToBlock S).measurable
    | fun_prop

/-- Joint central multiplication and the established block bridges send the
finite parameter measure exactly to the coherent common-carrier cylinder. -/
theorem map_cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient S)
        (V.cliffordGeneralSpinHorizontalFiniteChartParameterMeasure S) =
      V.cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure S := by
  let sourceToAmbient :=
    V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  let parameterToSource :=
    V.cliffordGeneralSpinHorizontalFiniteChartParameterToSource S
  have hs : Measurable sourceToAmbient :=
    V.measurable_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  have hp : Measurable parameterToSource :=
    V.measurable_cliffordGeneralSpinHorizontalFiniteChartParameterToSource S
  calc
    Measure.map
        (V.cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient S)
        (V.cliffordGeneralSpinHorizontalFiniteChartParameterMeasure S) =
      Measure.map sourceToAmbient
        (Measure.map parameterToSource
          (V.cliffordGeneralSpinHorizontalFiniteChartParameterMeasure S)) := by
        rw [Measure.map_map hs hp]
        rfl
    _ = Measure.map sourceToAmbient
        (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
          V.cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure S) := by
      rw [V.map_cliffordGeneralSpinHorizontalFiniteChartParameterToSource S]
    _ = V.cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure S := by
      unfold sourceToAmbient cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
        cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure
        cliffordGeneralSpinHorizontalCoherentIdentityChartGenuinePrincipalBlockMeasure
        cliffordGeneralSpinHorizontalCoherentIdentityChartRestrictedPrincipalBlockMeasure
        cliffordGeneralSpinHorizontalIdentityChartRestrictedPrincipalBlockMeasure
      rw [Measure.map_smul, Measure.map_smul, Measure.map_smul,
        Measure.map_map, Measure.map_map]
      · simp only [Function.comp_def]
      · exact
          (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S).measurable.comp
            (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm.measurable
      · exact
          (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S).measurable
      · exact
          (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S).measurable
      · exact
          (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm.measurable

/-! ## Real--finite chart parameters -/

/-- The real scalar/Spin chart together with the coherent finite parameter
source. -/
abbrev CliffordGeneralSpinHorizontalRealFiniteChartParameterSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  V.realCliffordGeneralSpinHorizontalProductIdentityChart.source ×
    V.CliffordGeneralSpinHorizontalFiniteChartParameterSource S

/-- The literal real chart measure times the block-weighted finite parameter
measure. -/
def cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalRealFiniteChartParameterSource S) :=
  V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
    (V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure.prod
      ((V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)).prod
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)))

/-- Joint central multiplication into the common real--finite `GSpin`
carrier. -/
def cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalRealFiniteChartParameterSource S →
      V.RealCliffordGeneralSpinGroup ×
        V.FiniteAdelicCliffordGeneralSpinGroup :=
  Prod.map
    (fun x ↦ V.cliffordGeneralSpinCentralSpinMultiplication ℝ x)
    (V.cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient S)

set_option backward.isDefEq.respectTransparency false in
/-- The joint real--finite parameter measure maps exactly to the coherent
real--finite identity-chart cylinder. -/
theorem map_cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient S)
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S) =
      V.cliffordGeneralSpinHorizontalCoherentIdentityChartRealFiniteMeasure S := by
  letI : SigmaFinite
      V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure := by
    let productChart := V.realCliffordGeneralSpinHorizontalProductIdentityChart
    letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
      Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℝˣ)
    letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
      PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
        V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure := by
      unfold realCliffordGeneralSpinHorizontalDifferentialProductMeasure
      infer_instance
    letI : SigmaFinite
        V.realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure,
        map_comap_subtype_coe productChart.open_target.measurableSet]
      infer_instance
    unfold realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
    exact productChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
    unfold cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
    letI (v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
        SigmaFinite
          (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1) := by
      let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
      let productChart := V.padicCliffordGeneralSpinHorizontalProductIdentityChart p
      letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) :=
        Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
      letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
        PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
          p n V.pairingMatrix V.form_symm V.form_det_ne_zero
      letI : SigmaFinite
          (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) := by
        unfold padicCliffordGeneralSpinHorizontalDifferentialProductMeasure
        infer_instance
      letI : SigmaFinite
          (V.padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure p) := by
        apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
        rw [padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure,
          map_comap_subtype_coe productChart.open_target.measurableSet]
        infer_instance
      unfold padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
      exact productChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
    infer_instance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  have hreal :
      Measure.map
          (fun x : V.realCliffordGeneralSpinHorizontalProductIdentityChart.source ↦
            V.cliffordGeneralSpinCentralSpinMultiplication ℝ x)
          V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure =
        V.realCliffordGeneralSpinHorizontalIdentityChartAmbientMeasure := by
    rw [V.map_realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_centralSpin]
    exact V.restrict_realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_identity.symm
  unfold cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient
    cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure
    cliffordGeneralSpinHorizontalCoherentIdentityChartRealFiniteMeasure
  rw [Measure.map_smul, ← Measure.map_prod_map, hreal]
  rw [← Measure.prod_smul_right]
  rw [← Measure.map_smul]
  change
    V.realCliffordGeneralSpinHorizontalIdentityChartAmbientMeasure.prod
        (Measure.map
          (V.cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient S)
          (V.cliffordGeneralSpinHorizontalFiniteChartParameterMeasure S)) = _
  rw [V.map_cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient S]
  all_goals
    first
    | exact (V.continuous_cliffordGeneralSpinCentralSpinMultiplication ℝ).measurable.comp
        continuous_subtype_val.measurable
    | exact V.measurable_cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient S

/-! ## Joint scalar/Spin splitting and finite cancellation -/

/-- The scalar/Spin coordinates of the real chart and every finitely
exceptional p-adic chart, with the normalized good tail unchanged. -/
abbrev CliffordGeneralSpinHorizontalRealFiniteChartSplitSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  ((Rat.unitSquareIdentityChart ℝ).source ×
      V.realCliffordSpinCandidateIdentityChart.source) ×
    (V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) ×
      V.CliffordGeneralSpinHorizontalIntegralTail S)

/-- Componentwise scalar/Spin splitting on the complete real--finite
parameter source. -/
def cliffordGeneralSpinHorizontalRealFiniteChartSplit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalRealFiniteChartParameterSource S →
      V.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource S :=
  Prod.map
    (Homeomorph.Set.prod
      (Rat.unitSquareIdentityChart ℝ).source
      V.realCliffordSpinCandidateIdentityChart.source)
    (Prod.map
      (V.cliffordGeneralSpinHorizontalExceptionalChartSplit
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) id)

/-- The finite exceptional component of the split map is a genuine product
homeomorphism, not merely a measurable choice of coordinates. -/
def cliffordGeneralSpinHorizontalExceptionalChartSplitHomeomorph
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalExceptionalChartSource S ≃ₜ
      V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource S :=
  Homeomorph.piCongrRight fun v ↦
    Homeomorph.Set.prod
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source
      (V.padicCliffordSpinCandidateIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).source

@[simp]
theorem cliffordGeneralSpinHorizontalExceptionalChartSplitHomeomorph_apply
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalExceptionalChartSource S) :
    V.cliffordGeneralSpinHorizontalExceptionalChartSplitHomeomorph S g =
      V.cliffordGeneralSpinHorizontalExceptionalChartSplit S g := rfl

/-- The ambient scalar/Spin split measure before multiplication by the one
finite real--dyadic modulus and by the coherent block weight. -/
def cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource S) :=
  (realUnitSquareIdentityChartAmbientSourceMeasure.prod
      V.realCliffordSpinCandidateIdentityChartSourceMeasure).prod
    ((V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)).prod
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S))

set_option backward.isDefEq.respectTransparency false in
/-- The joint splitting exposes exactly the coherent block weight times the
literal real modulus times the finite exceptional modulus. -/
theorem map_cliffordGeneralSpinHorizontalRealFiniteChartSplit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalRealFiniteChartSplit S)
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S) =
      V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
        (((rationalIdeleRealSquareModulus : ENNReal) *
            (cliffordGeneralSpinHorizontalExceptionalChartSquareModulus
              (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) : ENNReal)) •
          V.cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure S) := by
  let E := S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let realSplit := Homeomorph.Set.prod
    (Rat.unitSquareIdentityChart ℝ).source
    V.realCliffordSpinCandidateIdentityChart.source
  let finiteSplit := V.cliffordGeneralSpinHorizontalExceptionalChartSplit E
  letI : SigmaFinite
      V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure := by
    let productChart := V.realCliffordGeneralSpinHorizontalProductIdentityChart
    letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
      Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℝˣ)
    letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
      PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
        V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure := by
      unfold realCliffordGeneralSpinHorizontalDifferentialProductMeasure
      infer_instance
    letI : SigmaFinite
        V.realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure,
        map_comap_subtype_coe productChart.open_target.measurableSet]
      infer_instance
    unfold realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
    exact productChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure E) := by
    unfold cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
    letI (v : {v // v ∈ E}) : SigmaFinite
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1) := by
      let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
      let productChart := V.padicCliffordGeneralSpinHorizontalProductIdentityChart p
      letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) :=
        Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
      letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
        PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
          p n V.pairingMatrix V.form_symm V.form_det_ne_zero
      letI : SigmaFinite
          (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) := by
        unfold padicCliffordGeneralSpinHorizontalDifferentialProductMeasure
        infer_instance
      letI : SigmaFinite
          (V.padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure p) := by
        apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
        rw [padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure,
          map_comap_subtype_coe productChart.open_target.measurableSet]
        infer_instance
      unfold padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
      exact productChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
    infer_instance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure E) := by
    rw [← V.map_cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure E]
    change SigmaFinite
      (Measure.map
        (V.cliffordGeneralSpinHorizontalExceptionalChartSplitHomeomorph E)
        (V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure E))
    exact
      (V.cliffordGeneralSpinHorizontalExceptionalChartSplitHomeomorph E).toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure E) := by
    let base := fun v : {v // v ∈ E} ↦
      (padicUnitSquareIdentityChartAmbientSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).prod
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1)
    letI (v : {v // v ∈ E}) : SigmaFinite (base v) := by
      let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
      let squareChart := Rat.unitSquareIdentityChart ℚ_[p]
      let spinChart := V.padicCliffordSpinCandidateIdentityChart p
      letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) :=
        Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
      letI : SigmaFinite (padicUnitSquareIdentityChartAmbientSourceMeasure p) := by
        apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
        rw [padicUnitSquareIdentityChartAmbientSourceMeasure,
          map_comap_subtype_coe squareChart.open_source.measurableSet]
        infer_instance
      letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
        PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
          p n V.pairingMatrix V.form_symm V.form_det_ne_zero
      letI : SigmaFinite
          (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
        apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
        rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
          map_comap_subtype_coe spinChart.open_target.measurableSet]
        infer_instance
      letI : SigmaFinite
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
        rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
        exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
      infer_instance
    unfold cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure
    infer_instance
  letI : SigmaFinite
      ((cliffordGeneralSpinHorizontalExceptionalChartSquareModulus E : ENNReal) •
        V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure E) := by
    change SigmaFinite
      (cliffordGeneralSpinHorizontalExceptionalChartSquareModulus E •
        V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure E)
    rw [← V.cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure_eq_smul E]
    infer_instance
  letI : SigmaFinite
      ((V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure E).prod
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)) := by
    infer_instance
  letI : SigmaFinite
      ((cliffordGeneralSpinHorizontalExceptionalChartSquareModulus E : ENNReal) •
        ((V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure E).prod
          (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S))) := by
    rw [← Measure.prod_smul_left]
    infer_instance
  have hfinite :
      Measure.map (Prod.map finiteSplit id)
          ((V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure E).prod
            (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)) =
        (V.cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure E).prod
          (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) := by
    rw [← Measure.map_prod_map,
      V.map_cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure E,
      Measure.map_id]
    all_goals
      first
      | exact V.measurable_cliffordGeneralSpinHorizontalExceptionalChartSplit E
      | fun_prop
  unfold cliffordGeneralSpinHorizontalRealFiniteChartSplit
    cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure
    cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure
  change Measure.map (Prod.map realSplit (Prod.map finiteSplit id)) _ = _
  rw [Measure.map_smul, ← Measure.map_prod_map,
    V.realHorizontalProductSourceMeasure_split, hfinite]
  rw [V.cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure_eq_smul E,
    show rationalIdeleRealSquareModulus •
        (realUnitSquareIdentityChartAmbientSourceMeasure.prod
          V.realCliffordSpinCandidateIdentityChartSourceMeasure) =
      (rationalIdeleRealSquareModulus : ENNReal) •
        (realUnitSquareIdentityChartAmbientSourceMeasure.prod
          V.realCliffordSpinCandidateIdentityChartSourceMeasure) from rfl,
    show cliffordGeneralSpinHorizontalExceptionalChartSquareModulus E •
        V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure E =
      (cliffordGeneralSpinHorizontalExceptionalChartSquareModulus E : ENNReal) •
        V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure E from rfl,
    show ((cliffordGeneralSpinHorizontalExceptionalChartSquareModulus E : ENNReal) •
          V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure E).prod
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) =
      (cliffordGeneralSpinHorizontalExceptionalChartSquareModulus E : ENNReal) •
        ((V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure E).prod
          (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)) from
      Measure.prod_smul_left _,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  all_goals
    first
    | exact realSplit.measurable
    | exact (V.measurable_cliffordGeneralSpinHorizontalExceptionalChartSplit E).prodMap
        measurable_id
    | simp only [E, smul_smul, mul_assoc]

/-- If the retained exceptional carrier contains the dyadic place, the real
factor `2` and dyadic factor `2⁻¹` cancel literally on the joint split
measure. -/
theorem map_cliffordGeneralSpinHorizontalRealFiniteChartSplit_of_dyadic
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hdyadic : rationalIdeleDyadicPlace ∈
      S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalRealFiniteChartSplit S)
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S) =
      V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
        V.cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure S := by
  have hcancel :
      (rationalIdeleRealSquareModulus : ENNReal) *
          (cliffordGeneralSpinHorizontalExceptionalChartSquareModulus
            (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) : ENNReal) = 1 := by
    exact_mod_cast
      real_mul_cliffordGeneralSpinHorizontalExceptionalChartSquareModulus_eq_one
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) hdyadic
  rw [V.map_cliffordGeneralSpinHorizontalRealFiniteChartSplit S, hcancel, one_smul]

end RationalQuadraticSpaceMatrix
