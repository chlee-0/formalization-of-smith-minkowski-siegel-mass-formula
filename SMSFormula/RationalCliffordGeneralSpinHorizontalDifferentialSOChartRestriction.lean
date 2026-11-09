import SMSFormula.RationalCliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelic
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicDifferentialMeasure

/-!
# Differential SO chart restrictions for the horizontal central extension

The ambient central-fiber bind is based on the carrier-independent
differential Haar measure on adelic `SO`.  On a finite exceptional block this
measure is not the bare product of unrestricted local differential Haar and
the normalized integral tail: the established restricted-product
normalization contributes the literal finite special-orthogonal block weight.

This file transports the chosen Spin identity charts into that exact finite
`SO` block and records the resulting restriction formula.  It isolates the
base-measure coefficient needed by the forthcoming restriction of the
ambient central-fiber bind.  No central-fiber integral, direct-product
identification, quotient comparison, or assertion that the block weight is
one is made here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

local instance horizontalDifferentialSOChartPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalDifferentialSOChartDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance horizontalDifferentialSOChartPadicSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalDifferentialSOChartPadicSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance horizontalDifferentialSOChartRealSOMeasurableSpace :
    MeasurableSpace V.RealSpecialOrthogonalGroup :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance horizontalDifferentialSOChartRealSOBorelSpace :
    BorelSpace V.RealSpecialOrthogonalGroup :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance horizontalDifferentialSOChartHeightOneSOMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalDifferentialSOChartHeightOneSOBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalDifferentialSOChartHeightOneSOSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    V.pairingMatrix (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalDifferentialSOChartExceptionalSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalDifferentialSOChartExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  Pi.borelSpace

local instance horizontalDifferentialSOChartIntegralFactorBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  Subtype.borelSpace _

local instance horizontalDifferentialSOChartIntegralFactorSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalDifferentialSOChartTailSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalDifferentialSOChartTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Pi.borelSpace

local instance horizontalDifferentialSOChartFiniteGroupMeasurableSpace :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup := borel _

local instance horizontalDifferentialSOChartFiniteGroupBorelSpace :
    BorelSpace V.FiniteAdelicSpecialOrthogonalGroup := ⟨rfl⟩

local instance horizontalDifferentialSOChartFullGroupMeasurableSpace :
    MeasurableSpace V.FullAdelicSpecialOrthogonalGroup := borel _

local instance horizontalDifferentialSOChartFullGroupBorelSpace :
    BorelSpace V.FullAdelicSpecialOrthogonalGroup := ⟨rfl⟩

local instance horizontalDifferentialSOChartLocalFactorSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalDifferentialSOChartLocalFactorBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance horizontalDifferentialSOChartMixedSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalDifferentialSOChartMixedBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance horizontalDifferentialSOChartGenuineMeasurableSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSpace (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  borel _

local instance horizontalDifferentialSOChartGenuineBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  ⟨rfl⟩

/-! ## Exceptional Spin charts inside the SO product -/

/-- Product of the chosen Spin chart sources over a finite set of places. -/
abbrev CliffordGeneralSpinHorizontalExceptionalSOChartSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ S}) →
    (V.padicCliffordSpinCandidateIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).source

/-- Literal product of the inverse-transport differential measures on those
Spin chart sources. -/
def cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalExceptionalSOChartSource S) :=
  Measure.pi fun v : {v // v ∈ S} ↦
    V.padicCliffordSpinCandidateIdentityChartSourceMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1

set_option backward.isDefEq.respectTransparency false in
instance cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure_sigmaFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure S) := by
  letI (v : {v // v ∈ S}) : SigmaFinite
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let spinChart := V.padicCliffordSpinCandidateIdentityChart p
    letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        p n V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
        map_comap_subtype_coe spinChart.open_target.measurableSet]
      infer_instance
    rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
    exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  unfold cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure
  infer_instance

/-- Apply the Spin-to-`SO` chart map componentwise. -/
def cliffordGeneralSpinHorizontalExceptionalSOChartToProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalExceptionalSOChartSource S →
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S :=
  fun x v ↦
    V.cliffordSpinCandidateGroupToSpecialOrthogonal
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (x v)

theorem measurable_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S) := by
  apply measurable_pi_lambda
  intro v
  have hchart : Measurable
      (fun x : (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).source ↦
        V.cliffordSpinCandidateGroupToSpecialOrthogonal
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] x) := by
    simpa only [V.padicCliffordSpinCandidateIdentityChart_coe] using
      (continuous_subtype_val.measurable.comp
        (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          |>.toHomeomorphSourceTarget.measurable))
  exact hchart.comp (measurable_pi_apply v)

theorem measurableEmbedding_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (V.cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S) := by
  have hlocal : ∀ v : {v // v ∈ S}, Topology.IsOpenEmbedding
      (fun x : (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).source ↦
        V.cliffordSpinCandidateGroupToSpecialOrthogonal
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] x) := by
    intro v
    have h := (V.padicCliffordSpinCandidateIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).open_target.isOpenEmbedding_subtypeVal.comp
        (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          |>.toHomeomorphSourceTarget.isOpenEmbedding)
    simpa only [V.padicCliffordSpinCandidateIdentityChart_coe] using h
  exact (Topology.IsOpenEmbedding.piMap hlocal).measurableEmbedding

/-- The literal product target occupied by the chosen Spin identity charts. -/
def cliffordGeneralSpinHorizontalExceptionalSOChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  Set.pi Set.univ fun v : {v // v ∈ S} ↦
    (V.padicCliffordSpinCandidateIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).target

theorem measurableSet_cliffordGeneralSpinHorizontalExceptionalSOChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (V.cliffordGeneralSpinHorizontalExceptionalSOChartCarrier S) := by
  apply MeasurableSet.univ_pi
  intro v
  exact (V.padicCliffordSpinCandidateIdentityChart
    (Rat.HeightOneSpectrum.primesEquiv v.1).1).open_target.measurableSet

set_option backward.isDefEq.respectTransparency false in
/-- The exceptional Spin chart product maps exactly to the restriction of the
unrestricted differential `SO` product. -/
theorem map_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S)
        (V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure S) =
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).restrict
        (V.cliffordGeneralSpinHorizontalExceptionalSOChartCarrier S) := by
  let f := fun v : {v // v ∈ S} ↦
    fun x : (V.padicCliffordSpinCandidateIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).source ↦
      V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] x
  let μ := fun v : {v // v ∈ S} ↦
    V.padicCliffordSpinCandidateIdentityChartSourceMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  letI (v : {v // v ∈ S}) : SigmaFinite ((μ v).map (f v)) := by
    rw [V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure_pointMap]
    letI : SigmaFinite
        (V.padicInvariantDifferentialGroupMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 n V.pairingMatrix
        V.form_symm V.form_det_ne_zero
    infer_instance
  have hpi :
      (Measure.pi μ).map (fun x v ↦ f v (x v)) =
        Measure.pi fun v ↦ (μ v).map (f v) :=
    Measure.pi_map_pi fun v ↦ by
      have hchart : Measurable (f v) := by
        simpa only [f, V.padicCliffordSpinCandidateIdentityChart_coe] using
          (continuous_subtype_val.measurable.comp
            (V.padicCliffordSpinCandidateIdentityChart
              (Rat.HeightOneSpectrum.primesEquiv v.1).1
              |>.toHomeomorphSourceTarget.measurable))
      exact hchart.aemeasurable
  simpa only [cliffordGeneralSpinHorizontalExceptionalSOChartToProduct,
    cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure,
    finiteAdelicSpecialOrthogonalExceptionalProductMeasure,
    cliffordGeneralSpinHorizontalExceptionalSOChartCarrier,
    V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure_pointMap,
    Measure.restrict_pi_pi, f, μ] using hpi

/-! ## Finite-adelic assembly and its exact block weight -/

/-- The exceptional Spin charts together with the normalized integral `SO`
tail. -/
abbrev CliffordGeneralSpinHorizontalFiniteSOChartSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  V.CliffordGeneralSpinHorizontalExceptionalSOChartSource S ×
    V.FiniteAdelicSpecialOrthogonalIntegralTail S

/-- Bare differential chart product; the global restricted-product block
weight is deliberately not included. -/
def cliffordGeneralSpinHorizontalFiniteSOChartSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalFiniteSOChartSource S) :=
  (V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure S).prod
    (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S)

set_option backward.isDefEq.respectTransparency false in
instance cliffordGeneralSpinHorizontalFiniteSOChartSourceMeasure_sigmaFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite (V.cliffordGeneralSpinHorizontalFiniteSOChartSourceMeasure S) := by
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  unfold cliffordGeneralSpinHorizontalFiniteSOChartSourceMeasure
  infer_instance

/-- Assemble the finite `SO` chart source into the intrinsic finite-adelic
carrier through the existing mixed and genuine principal blocks. -/
def cliffordGeneralSpinHorizontalFiniteSOChartToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalFiniteSOChartSource S →
      V.FiniteAdelicSpecialOrthogonalGroup :=
  (fun a : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S ↦ a.1) ∘
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S).symm ∘
      V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S ∘
        Prod.map (V.cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S) id

theorem measurable_cliffordGeneralSpinHorizontalFiniteSOChartToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient S) := by
  unfold cliffordGeneralSpinHorizontalFiniteSOChartToAmbient
  exact continuous_subtype_val.measurable.comp
    ((V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S).symm.measurable.comp
      ((V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S).measurable.comp
        ((V.measurable_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S).prodMap
          measurable_id)))

/-- The actual finite-adelic carrier occupied by the exceptional Spin charts
and the complete integral tail. -/
def cliffordGeneralSpinHorizontalFiniteSOChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set V.FiniteAdelicSpecialOrthogonalGroup :=
  Set.range (V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient S)

set_option backward.isDefEq.respectTransparency false in
/-- The global finite-adelic differential `SO` Haar restriction contains the
literal absolute `SO` block weight.  This coefficient is not part of the bare
chart source measure and is not asserted to be one. -/
theorem
    finiteAdelicInvariantDifferentialGroupMeasure_restrict_horizontalSOChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicInvariantDifferentialGroupMeasure.restrict
        (V.cliffordGeneralSpinHorizontalFiniteSOChartCarrier S) =
      V.finiteAdelicSpecialOrthogonalBlockWeight S •
        Measure.map
          (V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient S)
          (V.cliffordGeneralSpinHorizontalFiniteSOChartSourceMeasure S) := by
  let chart := V.cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S
  let μchart := V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure S
  let C := V.cliffordGeneralSpinHorizontalExceptionalSOChartCarrier S
  let μE := V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S
  let μT := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S
  let mixed := V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S
  let genuine := V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S
  let val := fun a : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S ↦ a.1
  let f := val ∘ genuine.symm ∘ mixed ∘ Prod.map chart id
  let B := Set.range val
  let D : Set (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
      V.FiniteAdelicSpecialOrthogonalIntegralTail S) := C ×ˢ Set.univ
  have hval : MeasurableEmbedding val :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubtypeVal_measurableEmbedding S
  have hchart_range : Set.range chart = C := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      intro v _
      simpa only [chart,
        cliffordGeneralSpinHorizontalExceptionalSOChartToProduct,
        V.padicCliffordSpinCandidateIdentityChart_coe] using
        (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).map_source (y v).2
    · intro hx
      let y : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource S :=
        fun v ↦
          (V.padicCliffordSpinCandidateIdentityChart
            (Rat.HeightOneSpectrum.primesEquiv v.1).1).toHomeomorphSourceTarget.symm
              ⟨x v, hx v (Set.mem_univ v)⟩
      refine ⟨y, ?_⟩
      funext v
      have h := (V.padicCliffordSpinCandidateIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).toHomeomorphSourceTarget.apply_symm_apply
          ⟨x v, hx v (Set.mem_univ v)⟩
      simpa only [chart,
        cliffordGeneralSpinHorizontalExceptionalSOChartToProduct,
        V.padicCliffordSpinCandidateIdentityChart_coe] using congrArg Subtype.val h
  have hD : MeasurableSet D :=
    (V.measurableSet_cliffordGeneralSpinHorizontalExceptionalSOChartCarrier S).prod
      MeasurableSet.univ
  have hmap_chart : Measure.map chart μchart = μE.restrict C :=
    V.map_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S
  have hsource :
      V.finiteAdelicInvariantDifferentialGroupMeasure.comap val =
        V.finiteAdelicSpecialOrthogonalBlockWeight S •
          Measure.map genuine.symm (Measure.map mixed (μE.prod μT)) := by
    rw [V.finiteAdelicInvariantDifferentialGroupMeasure_comap_genuineBlock S]
    unfold finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
      finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
      finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure
      finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
    simp_rw [Measure.map_smul]
    rfl
  have hpreimage :
      val ⁻¹' (Set.range f) = genuine.symm '' (mixed '' D) := by
    ext x
    constructor
    · rintro ⟨z, hz⟩
      have hx : x = genuine.symm (mixed (chart z.1, z.2)) :=
        hval.injective hz.symm
      rw [hx]
      exact ⟨mixed (chart z.1, z.2),
        ⟨(chart z.1, z.2), ⟨hchart_range ▸ Set.mem_range_self z.1, trivial⟩, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨d, hd, rfl⟩, rfl⟩
      rcases (hchart_range.symm ▸ hd.1) with ⟨z, hz⟩
      refine ⟨(z, d.2), ?_⟩
      change val (genuine.symm (mixed (chart z, d.2))) =
        val (genuine.symm (mixed d))
      rw [hz]
  have hchart : MeasurableEmbedding chart :=
    V.measurableEmbedding_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S
  have hf : MeasurableEmbedding f :=
    hval.comp (genuine.symm.measurableEmbedding.comp
      (mixed.measurableEmbedding.comp (hchart.prodMap MeasurableEmbedding.id)))
  have hf_range : MeasurableSet (Set.range f) := hf.measurableSet_range
  have hf_sub : Set.range f ⊆ B := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  letI (v : {v // v ∈ S}) : SigmaFinite
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let spinChart := V.padicCliffordSpinCandidateIdentityChart p
    letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        p n V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
        map_comap_subtype_coe spinChart.open_target.measurableSet]
      infer_instance
    rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
    exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite μchart := by
    unfold μchart cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure
    infer_instance
  have hprod :
      (Measure.map chart μchart).prod μT =
        Measure.map (Prod.map chart id) (μchart.prod μT) := by
    have hid : Measure.map id μT = μT := Measure.map_id
    calc
      (Measure.map chart μchart).prod μT =
          (Measure.map chart μchart).prod (Measure.map id μT) := by rw [hid]
      _ = Measure.map (Prod.map chart id) (μchart.prod μT) :=
        Measure.map_prod_map μchart μT hchart.measurable measurable_id
  change V.finiteAdelicInvariantDifferentialGroupMeasure.restrict (Set.range f) = _
  calc
    V.finiteAdelicInvariantDifferentialGroupMeasure.restrict (Set.range f) =
        (V.finiteAdelicInvariantDifferentialGroupMeasure.restrict B).restrict
          (Set.range f) := by
      rw [Measure.restrict_restrict hf_range]
      congr 1
      exact (Set.inter_eq_left.mpr hf_sub).symm
    _ = (Measure.map val
          (V.finiteAdelicInvariantDifferentialGroupMeasure.comap val)).restrict
            (Set.range f) := by
      rw [hval.map_comap]
    _ = Measure.map val
          ((V.finiteAdelicInvariantDifferentialGroupMeasure.comap val).restrict
            (val ⁻¹' Set.range f)) := by
      rw [hval.restrict_map]
    _ = Measure.map val
        ((V.finiteAdelicSpecialOrthogonalBlockWeight S •
          Measure.map genuine.symm (Measure.map mixed (μE.prod μT))).restrict
            (genuine.symm '' (mixed '' D))) := by rw [hsource, hpreimage]
    _ = V.finiteAdelicSpecialOrthogonalBlockWeight S •
        Measure.map f (μchart.prod μT) := by
      rw [Measure.restrict_smul, Measure.map_smul]
      rw [genuine.symm.measurableEmbedding.restrict_map]
      rw [mixed.measurableEmbedding.restrict_map]
      rw [Set.preimage_image_eq _ genuine.symm.injective,
        Set.preimage_image_eq _ mixed.injective]
      rw [← Measure.restrict_prod_eq_prod_univ]
      rw [← hmap_chart]
      rw [hprod]
      rw [Measure.map_map mixed.measurable
        ((V.measurable_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S).prodMap
          measurable_id)]
      rw [Measure.map_map genuine.symm.measurable
        (mixed.measurable.comp
          ((V.measurable_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S).prodMap
            measurable_id))]
      rw [Measure.map_map continuous_subtype_val.measurable
        (genuine.symm.measurable.comp
          (mixed.measurable.comp
            ((V.measurable_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S).prodMap
              measurable_id)))]

/-! ## Real--finite and full-adelic SO chart -/

/-- The real Spin chart together with the finite exceptional/tail `SO`
chart. -/
abbrev CliffordGeneralSpinHorizontalFullSOChartSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  V.realCliffordSpinCandidateIdentityChart.source ×
    V.CliffordGeneralSpinHorizontalFiniteSOChartSource S

/-- Bare differential source measure for the full `SO` chart. -/
def cliffordGeneralSpinHorizontalFullSOChartSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalFullSOChartSource S) :=
  V.realCliffordSpinCandidateIdentityChartSourceMeasure.prod
    (V.cliffordGeneralSpinHorizontalFiniteSOChartSourceMeasure S)

/-- Assemble the chosen real and finite `SO` chart coordinates into the exact
intrinsic full-adelic `SO` carrier. -/
def cliffordGeneralSpinHorizontalFullSOChartToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalFullSOChartSource S →
      V.FullAdelicSpecialOrthogonalGroup :=
  V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm ∘
    Prod.map
      (fun x : V.realCliffordSpinCandidateIdentityChart.source ↦
        V.realCliffordSpinCandidateToSpecialOrthogonalHom x)
      (V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient S)

theorem measurable_cliffordGeneralSpinHorizontalFullSOChartToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient S) := by
  let realChart := V.realCliffordSpinCandidateIdentityChart
  have hreal : Measurable
      (fun x : realChart.source ↦
        V.realCliffordSpinCandidateToSpecialOrthogonalHom x) := by
    simpa only [realChart, V.realCliffordSpinCandidateIdentityChart_coe] using
      (continuous_subtype_val.measurable.comp
        realChart.toHomeomorphSourceTarget.measurable)
  exact
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.measurable.comp
      (hreal.prodMap
        (V.measurable_cliffordGeneralSpinHorizontalFiniteSOChartToAmbient S))

/-- The literal full-adelic `SO` carrier corresponding to the retained
identity charts. -/
def cliffordGeneralSpinHorizontalFullSOChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set V.FullAdelicSpecialOrthogonalGroup :=
  Set.range (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient S)

set_option backward.isDefEq.respectTransparency false in
/-- Full-adelically, the chosen `SO` chart still carries exactly the absolute
finite special-orthogonal block weight.  The real chart introduces no extra
coefficient because its source measure was defined by inverse transport from
the fixed real differential Haar. -/
theorem fullAdelicInvariantDifferentialGroupMeasure_restrict_horizontalSOChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.fullAdelicInvariantDifferentialGroupMeasure.restrict
        (V.cliffordGeneralSpinHorizontalFullSOChartCarrier S) =
      V.finiteAdelicSpecialOrthogonalBlockWeight S •
        Measure.map
          (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient S)
          (V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure S) := by
  let realMap := fun x : V.realCliffordSpinCandidateIdentityChart.source ↦
    V.realCliffordSpinCandidateToSpecialOrthogonalHom x
  let finiteMap := V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient S
  let e := V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toHomeomorph
  let sourceMeasure := V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure S
  let realCarrier := V.realCliffordSpinCandidateIdentityChart.target
  let finiteCarrier := V.cliffordGeneralSpinHorizontalFiniteSOChartCarrier S
  let realFiniteCarrier : Set
      (V.RealSpecialOrthogonalGroup × V.FiniteAdelicSpecialOrthogonalGroup) :=
    realCarrier ×ˢ finiteCarrier
  have hreal : MeasurableEmbedding realMap := by
    have h := V.realCliffordSpinCandidateIdentityChart.open_target
      |>.isOpenEmbedding_subtypeVal.comp
        V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.isOpenEmbedding
    simpa only [realMap, V.realCliffordSpinCandidateIdentityChart_coe] using
      h.measurableEmbedding
  have hfinite : MeasurableEmbedding finiteMap := by
    let chart := V.cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S
    exact
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubtypeVal_measurableEmbedding S).comp
        ((V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S).symm.measurableEmbedding.comp
          ((V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S).measurableEmbedding.comp
            ((V.measurableEmbedding_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct S).prodMap
              MeasurableEmbedding.id)))
  have hprod : MeasurableEmbedding (Prod.map realMap finiteMap) :=
    hreal.prodMap hfinite
  have hfull : MeasurableEmbedding
      (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient S) :=
    e.symm.measurableEmbedding.comp hprod
  have hrange : Set.range (Prod.map realMap finiteMap) = realFiniteCarrier := by
    rw [Set.range_prodMap]
    have hrealRange : Set.range realMap = realCarrier := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        simpa only [realMap, V.realCliffordSpinCandidateIdentityChart_coe] using
          V.realCliffordSpinCandidateIdentityChart.map_source y.2
      · intro hx
        let y := V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.symm
          ⟨x, hx⟩
        refine ⟨y, ?_⟩
        have hy := V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.apply_symm_apply
          ⟨x, hx⟩
        simpa only [realMap, V.realCliffordSpinCandidateIdentityChart_coe] using
          congrArg Subtype.val hy
    rw [hrealRange]
    rfl
  have hrange_full :
      Set.range (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient S) =
        e.symm '' realFiniteCarrier := by
    change Set.range (e.symm ∘ Prod.map realMap finiteMap) = _
    rw [Set.range_comp, hrange]
  have hrealMeasure :
      Measure.map realMap V.realCliffordSpinCandidateIdentityChartSourceMeasure =
        V.realInvariantDifferentialGroupMeasure.restrict realCarrier := by
    exact V.map_realCliffordSpinCandidateIdentityChartSourceMeasure_pointMap
  have hfiniteMeasure :
      V.finiteAdelicInvariantDifferentialGroupMeasure.restrict finiteCarrier =
        V.finiteAdelicSpecialOrthogonalBlockWeight S •
          Measure.map finiteMap
            (V.cliffordGeneralSpinHorizontalFiniteSOChartSourceMeasure S) := by
    exact V.finiteAdelicInvariantDifferentialGroupMeasure_restrict_horizontalSOChart S
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
    V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm
  letI : SFinite
      (Measure.map finiteMap
        (V.cliffordGeneralSpinHorizontalFiniteSOChartSourceMeasure S)) :=
    inferInstance
  let realSpinChart := V.realCliffordSpinCandidateIdentityChart
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [realCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe realSpinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
    rw [realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact realSpinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  have hmapProd :
      (Measure.map realMap V.realCliffordSpinCandidateIdentityChartSourceMeasure).prod
          (Measure.map finiteMap
            (V.cliffordGeneralSpinHorizontalFiniteSOChartSourceMeasure S)) =
        Measure.map (Prod.map realMap finiteMap)
          (V.realCliffordSpinCandidateIdentityChartSourceMeasure.prod
            (V.cliffordGeneralSpinHorizontalFiniteSOChartSourceMeasure S)) :=
    Measure.map_prod_map _ _ hreal.measurable hfinite.measurable
  change
    (Measure.map e.symm V.realFiniteInvariantDifferentialGroupMeasure).restrict
        (Set.range (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient S)) = _
  rw [hrange_full, e.symm.measurableEmbedding.restrict_map,
    Set.preimage_image_eq _ e.symm.injective]
  unfold realFiniteInvariantDifferentialGroupMeasure
  rw [← Measure.prod_restrict]
  rw [← hrealMeasure, hfiniteMeasure]
  rw [Measure.prod_smul_right]
  rw [Measure.map_smul]
  rw [hmapProd]
  rw [Measure.map_map e.symm.measurable hprod.measurable]
  rfl

end RationalQuadraticSpaceMatrix
