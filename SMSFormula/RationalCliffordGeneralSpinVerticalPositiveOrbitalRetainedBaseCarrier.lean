import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedRealExceptionalBaseDisintegration

/-!
# Assemble the retained positive-idèle base carrier

The exposed real and exceptional square targets are paired here with the
normalized integral tail.  Their real--finite assembly is an exact
restriction of differential idèle Haar.  Since the real target is a square
range, this carrier lies in the positive idèles.

Only the exposed coordinates are assembled globally.  The good `SO`-indexed
tail lift is not constructed in this file; it enters only through its
iterated-integral disintegration.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

local instance retainedBaseCarrierDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedBaseCarrierPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance retainedBaseCarrierLocalMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance retainedBaseCarrierLocalBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance retainedBaseCarrierExceptionalSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (RationalIdeleDifferentialExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedBaseCarrierExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialExceptionalProduct S) :=
  Pi.borelSpace

local instance retainedBaseCarrierIntegralFactorSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    SecondCountableTopology (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedBaseCarrierIntegralFactorBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    BorelSpace (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
  Subtype.borelSpace _

local instance retainedBaseCarrierTailSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (RationalIdeleDifferentialIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedBaseCarrierTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialIntegralTail S) :=
  Pi.borelSpace

local instance retainedBaseCarrierFiniteMeasurableSpace :
    MeasurableSpace RationalFiniteAdeleˣ := borel _

local instance retainedBaseCarrierFiniteBorelSpace :
    BorelSpace RationalFiniteAdeleˣ := ⟨rfl⟩

local instance retainedBaseCarrierBlockBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- Forget the retained exceptional square-target subtype coordinatewise. -/
def rationalIdeleDifferentialExceptionalSquareTargetToProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalIdeleDifferentialExceptionalSquareChartTarget S →
      RationalIdeleDifferentialExceptionalProduct S :=
  fun x v ↦ x v

theorem measurableEmbedding_rationalIdeleDifferentialExceptionalSquareTargetToProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (rationalIdeleDifferentialExceptionalSquareTargetToProduct S) := by
  apply Topology.IsOpenEmbedding.measurableEmbedding
  apply Topology.IsOpenEmbedding.piMap
  intro v
  exact (Rat.unitSquareIdentityChart
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_target.isOpenEmbedding_subtypeVal

/-- The exceptional product occupied by the retained square targets. -/
def rationalIdeleDifferentialExceptionalSquareTargetCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (RationalIdeleDifferentialExceptionalProduct S) :=
  Set.pi Set.univ fun v : {v // v ∈ S} ↦
    (Rat.unitSquareIdentityChart
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).target

theorem measurableSet_rationalIdeleDifferentialExceptionalSquareTargetCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (rationalIdeleDifferentialExceptionalSquareTargetCarrier S) := by
  apply MeasurableSet.univ_pi
  intro v
  exact (Rat.unitSquareIdentityChart
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_target.measurableSet

/-- The retained exceptional target measure is exactly unrestricted
differential Haar restricted to the target product. -/
theorem map_rationalIdeleDifferentialExceptionalSquareTargetToProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (rationalIdeleDifferentialExceptionalSquareTargetToProduct S)
        (rationalIdeleDifferentialExceptionalSquareChartTargetMeasure S) =
      (rationalIdeleDifferentialExceptionalProductMeasure S).restrict
        (rationalIdeleDifferentialExceptionalSquareTargetCarrier S) := by
  let f := fun v : {v // v ∈ S} ↦
    fun x : (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).target ↦ (x :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
  let μ := fun v : {v // v ∈ S} ↦
    padicUnitSquareIdentityChartDifferentialTargetMeasure v.1
  have hlocal (v : {v // v ∈ S}) :
      (μ v).map (f v) =
        (rationalPadicIdeleDifferentialHaarMeasure v.1).restrict
          (Rat.unitSquareIdentityChart
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).target := by
    unfold μ f padicUnitSquareIdentityChartDifferentialTargetMeasure
    exact map_comap_subtype_coe
      (μ := rationalPadicIdeleDifferentialHaarMeasure v.1)
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_target.measurableSet
  letI (v : {v // v ∈ S}) : SigmaFinite ((μ v).map (f v)) := by
    rw [hlocal]
    infer_instance
  have hpi :
      (Measure.pi μ).map (fun x v ↦ f v (x v)) =
        Measure.pi fun v ↦ (μ v).map (f v) :=
    Measure.pi_map_pi fun v ↦ continuous_subtype_val.measurable.aemeasurable
  simp_rw [hlocal] at hpi
  simpa only [rationalIdeleDifferentialExceptionalSquareTargetToProduct,
    rationalIdeleDifferentialExceptionalSquareChartTargetMeasure,
    rationalIdeleDifferentialExceptionalProductMeasure,
    rationalIdeleDifferentialExceptionalSquareTargetCarrier,
    Measure.restrict_pi_pi, f, μ] using hpi

/-- Retained exceptional square targets together with the normalized integral
tail. -/
abbrev RationalFiniteIdeleDifferentialSquareTargetSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  RationalIdeleDifferentialExceptionalSquareChartTarget S ×
    RationalIdeleDifferentialIntegralTail S

def rationalFiniteIdeleDifferentialSquareTargetSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalFiniteIdeleDifferentialSquareTargetSource S) :=
  (rationalIdeleDifferentialExceptionalSquareChartTargetMeasure S).prod
    (rationalIdeleDifferentialNormalizedIntegralTailMeasure S)

instance rationalFiniteIdeleDifferentialSquareTargetSourceMeasure_sigmaFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite (rationalFiniteIdeleDifferentialSquareTargetSourceMeasure S) := by
  letI (v : {v // v ∈ S}) : SigmaFinite
      (padicUnitSquareIdentityChartDifferentialTargetMeasure v.1) := by
    unfold padicUnitSquareIdentityChartDifferentialTargetMeasure
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [map_comap_subtype_coe
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_target.measurableSet]
    infer_instance
  letI : SigmaFinite
      (rationalIdeleDifferentialExceptionalSquareChartTargetMeasure S) := by
    unfold rationalIdeleDifferentialExceptionalSquareChartTargetMeasure
    infer_instance
  letI : SigmaFinite
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  unfold rationalFiniteIdeleDifferentialSquareTargetSourceMeasure
  infer_instance

/-- Assemble the retained exceptional targets and normalized tail into a finite
idèle. -/
def rationalFiniteIdeleDifferentialSquareTargetToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalFiniteIdeleDifferentialSquareTargetSource S → RationalFiniteAdeleˣ :=
  rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S ∘
    rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph S ∘
      Prod.map (rationalIdeleDifferentialExceptionalSquareTargetToProduct S) id

theorem measurableEmbedding_rationalFiniteIdeleDifferentialSquareTargetToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding (rationalFiniteIdeleDifferentialSquareTargetToAmbient S) := by
  unfold rationalFiniteIdeleDifferentialSquareTargetToAmbient
  exact
    (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding S).comp
      ((rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph S).measurableEmbedding.comp
        ((measurableEmbedding_rationalIdeleDifferentialExceptionalSquareTargetToProduct S).prodMap
          MeasurableEmbedding.id))

def rationalFiniteIdeleDifferentialSquareTargetCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set RationalFiniteAdeleˣ :=
  Set.range (rationalFiniteIdeleDifferentialSquareTargetToAmbient S)

theorem measurableSet_rationalFiniteIdeleDifferentialSquareTargetCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (rationalFiniteIdeleDifferentialSquareTargetCarrier S) :=
  (measurableEmbedding_rationalFiniteIdeleDifferentialSquareTargetToAmbient S)
    |>.measurableSet_range

/-- Finite differential idèle Haar restricts to the retained square targets
and normalized integral tail with coefficient one. -/
theorem rationalFiniteIdeleDifferentialHaarMeasure_restrict_squareTarget
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    rationalFiniteIdeleDifferentialHaarMeasure.restrict
        (rationalFiniteIdeleDifferentialSquareTargetCarrier S) =
      Measure.map
        (rationalFiniteIdeleDifferentialSquareTargetToAmbient S)
        (rationalFiniteIdeleDifferentialSquareTargetSourceMeasure S) := by
  let chart := rationalIdeleDifferentialExceptionalSquareTargetToProduct S
  let μchart := rationalIdeleDifferentialExceptionalSquareChartTargetMeasure S
  let C := rationalIdeleDifferentialExceptionalSquareTargetCarrier S
  let μE := rationalIdeleDifferentialExceptionalProductMeasure S
  let μT := rationalIdeleDifferentialNormalizedIntegralTailMeasure S
  let e := rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph S
  let i := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S
  let f := i ∘ e ∘ Prod.map chart id
  let B := Set.range i
  let D : Set (RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S) := C ×ˢ Set.univ
  have hi : MeasurableEmbedding i :=
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding S
  have hchart : MeasurableEmbedding chart :=
    measurableEmbedding_rationalIdeleDifferentialExceptionalSquareTargetToProduct S
  have hchart_range : Set.range chart = C := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      intro v _
      exact (y v).2
    · intro hx
      let y : RationalIdeleDifferentialExceptionalSquareChartTarget S :=
        fun v ↦ ⟨x v, hx v (Set.mem_univ v)⟩
      exact ⟨y, rfl⟩
  have hD : MeasurableSet D :=
    (measurableSet_rationalIdeleDifferentialExceptionalSquareTargetCarrier S).prod
      MeasurableSet.univ
  have hmap_chart : Measure.map chart μchart = μE.restrict C :=
    map_rationalIdeleDifferentialExceptionalSquareTargetToProduct S
  have hpreimage : i ⁻¹' Set.range f = e '' D := by
    ext x
    constructor
    · rintro ⟨z, hz⟩
      have hx : x = e (chart z.1, z.2) := hi.injective hz.symm
      rw [hx]
      exact ⟨(chart z.1, z.2),
        ⟨hchart_range ▸ Set.mem_range_self z.1, trivial⟩, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      rcases (hchart_range.symm ▸ hd.1) with ⟨z, hz⟩
      refine ⟨(z, d.2), ?_⟩
      change i (e (chart z, d.2)) = i (e d)
      rw [hz]
  have hf : MeasurableEmbedding f :=
    hi.comp (e.measurableEmbedding.comp
      (hchart.prodMap MeasurableEmbedding.id))
  have hf_range : MeasurableSet (Set.range f) := hf.measurableSet_range
  have hf_sub : Set.range f ⊆ B := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  letI : SigmaFinite μchart := by
    unfold μchart rationalIdeleDifferentialExceptionalSquareChartTargetMeasure
    letI (v : {v // v ∈ S}) : SigmaFinite
        (padicUnitSquareIdentityChartDifferentialTargetMeasure v.1) := by
      unfold padicUnitSquareIdentityChartDifferentialTargetMeasure
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [map_comap_subtype_coe
        (Rat.unitSquareIdentityChart
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_target.measurableSet]
      infer_instance
    infer_instance
  letI : SigmaFinite μT := IsFiniteMeasure.toSigmaFinite _
  have hprod :
      (Measure.map chart μchart).prod μT =
        Measure.map (Prod.map chart id) (μchart.prod μT) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map μchart μT hchart.measurable measurable_id)
  change rationalFiniteIdeleDifferentialHaarMeasure.restrict (Set.range f) = _
  rw [← rationalFiniteIdeleDifferentialDirectedMeasure_eq_haar]
  calc
    rationalFiniteIdeleDifferentialDirectedMeasure.restrict (Set.range f) =
        (rationalFiniteIdeleDifferentialDirectedMeasure.restrict B).restrict
          (Set.range f) := by
      rw [Measure.restrict_restrict hf_range]
      congr 1
      exact (Set.inter_eq_left.mpr hf_sub).symm
    _ = (rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure S).restrict
          (Set.range f) := by
      rw [rationalFiniteIdeleDifferentialDirectedMeasure_restrict_genuineBlock]
    _ = (Measure.map i (Measure.map e (μE.prod μT))).restrict
          (Set.range f) := by rfl
    _ = Measure.map i
          ((Measure.map e (μE.prod μT)).restrict (i ⁻¹' Set.range f)) := by
      rw [hi.restrict_map]
    _ = Measure.map i
          ((Measure.map e (μE.prod μT)).restrict (e '' D)) := by rw [hpreimage]
    _ = Measure.map i (Measure.map e ((μE.prod μT).restrict D)) := by
      rw [e.measurableEmbedding.restrict_map,
        Set.preimage_image_eq _ e.injective]
    _ = Measure.map i (Measure.map e ((μE.restrict C).prod μT)) := by
      rw [Measure.restrict_prod_eq_prod_univ]
    _ = Measure.map i (Measure.map e
          ((Measure.map chart μchart).prod μT)) := by rw [hmap_chart]
    _ = Measure.map i (Measure.map e
          (Measure.map (Prod.map chart id) (μchart.prod μT))) := by rw [hprod]
    _ = Measure.map f (μchart.prod μT) := by
      rw [Measure.map_map e.measurable
        ((hchart.measurable).prodMap measurable_id),
        Measure.map_map hi.measurable
          (e.measurable.comp ((hchart.measurable).prodMap measurable_id))]

local instance retainedBaseCarrierRealMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

local instance retainedBaseCarrierRealBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

local instance retainedBaseCarrierFullMeasurableSpace :
    MeasurableSpace RationalAdeleˣ := borel _

local instance retainedBaseCarrierFullBorelSpace :
    BorelSpace RationalAdeleˣ := ⟨rfl⟩

/-- Real square target, retained exceptional square targets, and the complete
normalized integral tail. -/
abbrev RationalIdeleDifferentialRetainedBaseTargetSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (Rat.unitSquareIdentityChart ℝ).target ×
    RationalFiniteIdeleDifferentialSquareTargetSource S

def rationalIdeleDifferentialRetainedBaseTargetSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalIdeleDifferentialRetainedBaseTargetSource S) :=
  realUnitSquareIdentityChartTargetMeasure.prod
    (rationalFiniteIdeleDifferentialSquareTargetSourceMeasure S)

/-- Assemble the exposed retained targets into a rational idèle. -/
def rationalIdeleDifferentialRetainedBaseTargetToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalIdeleDifferentialRetainedBaseTargetSource S → RationalAdeleˣ :=
  rationalAdeleUnitsRealFiniteContinuousEquiv.symm ∘
    Prod.map Subtype.val (rationalFiniteIdeleDifferentialSquareTargetToAmbient S)

theorem measurableEmbedding_rationalIdeleDifferentialRetainedBaseTargetToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding (rationalIdeleDifferentialRetainedBaseTargetToAmbient S) := by
  unfold rationalIdeleDifferentialRetainedBaseTargetToAmbient
  exact rationalAdeleUnitsRealFiniteContinuousEquiv.symm.measurableEmbedding.comp
    ((Rat.unitSquareIdentityChart ℝ).open_target.isOpenEmbedding_subtypeVal
      |>.measurableEmbedding.prodMap
        (measurableEmbedding_rationalFiniteIdeleDifferentialSquareTargetToAmbient S))

def rationalIdeleDifferentialRetainedBaseCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set RationalAdeleˣ :=
  Set.range (rationalIdeleDifferentialRetainedBaseTargetToAmbient S)

theorem measurableSet_rationalIdeleDifferentialRetainedBaseCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (rationalIdeleDifferentialRetainedBaseCarrier S) :=
  (measurableEmbedding_rationalIdeleDifferentialRetainedBaseTargetToAmbient S)
    |>.measurableSet_range

/-- Full differential idèle Haar restricts to the assembled retained target
carrier with coefficient one. -/
theorem rationalIdeleDifferentialHaarMeasure_restrict_retainedBaseCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    rationalIdeleDifferentialHaarMeasure.restrict
        (rationalIdeleDifferentialRetainedBaseCarrier S) =
      Measure.map
        (rationalIdeleDifferentialRetainedBaseTargetToAmbient S)
        (rationalIdeleDifferentialRetainedBaseTargetSourceMeasure S) := by
  let realMap := fun x : (Rat.unitSquareIdentityChart ℝ).target ↦ (x : ℝˣ)
  let finiteMap := rationalFiniteIdeleDifferentialSquareTargetToAmbient S
  let e := rationalAdeleUnitsRealFiniteContinuousEquiv.toHomeomorph
  let realCarrier := (Rat.unitSquareIdentityChart ℝ).target
  let finiteCarrier := rationalFiniteIdeleDifferentialSquareTargetCarrier S
  let realFiniteCarrier : Set (ℝˣ × RationalFiniteAdeleˣ) :=
    realCarrier ×ˢ finiteCarrier
  have hreal : MeasurableEmbedding realMap :=
    (Rat.unitSquareIdentityChart ℝ).open_target.isOpenEmbedding_subtypeVal
      |>.measurableEmbedding
  have hfinite : MeasurableEmbedding finiteMap :=
    measurableEmbedding_rationalFiniteIdeleDifferentialSquareTargetToAmbient S
  have hprod : MeasurableEmbedding (Prod.map realMap finiteMap) :=
    hreal.prodMap hfinite
  have hrange : Set.range (Prod.map realMap finiteMap) = realFiniteCarrier := by
    rw [Set.range_prodMap]
    have hrealRange : Set.range realMap = realCarrier := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hrealRange]
    rfl
  have hrange_full :
      Set.range (rationalIdeleDifferentialRetainedBaseTargetToAmbient S) =
        e.symm '' realFiniteCarrier := by
    change Set.range (e.symm ∘ Prod.map realMap finiteMap) = _
    rw [Set.range_comp, hrange]
  have hrealMeasure :
      Measure.map realMap realUnitSquareIdentityChartTargetMeasure =
        (Measure.haar : Measure ℝˣ).restrict realCarrier := by
    unfold realUnitSquareIdentityChartTargetMeasure
    exact map_comap_subtype_coe
      (μ := (Measure.haar : Measure ℝˣ))
      (Rat.unitSquareIdentityChart ℝ).open_target.measurableSet
  have hfiniteMeasure :
      rationalFiniteIdeleDifferentialHaarMeasure.restrict finiteCarrier =
        Measure.map finiteMap
          (rationalFiniteIdeleDifferentialSquareTargetSourceMeasure S) :=
    rationalFiniteIdeleDifferentialHaarMeasure_restrict_squareTarget S
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
    Measure.IsHaarMeasure.sigmaFinite _
  letI : SigmaFinite rationalFiniteIdeleDifferentialHaarMeasure := by
    rw [← rationalFiniteIdeleDifferentialDirectedMeasure_eq_haar]
    infer_instance
  letI : SFinite
      (Measure.map finiteMap
        (rationalFiniteIdeleDifferentialSquareTargetSourceMeasure S)) :=
    inferInstance
  letI : SigmaFinite realUnitSquareIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [hrealMeasure]
    infer_instance
  have hmapProd :
      (Measure.map realMap realUnitSquareIdentityChartTargetMeasure).prod
          (Measure.map finiteMap
            (rationalFiniteIdeleDifferentialSquareTargetSourceMeasure S)) =
        Measure.map (Prod.map realMap finiteMap)
          (realUnitSquareIdentityChartTargetMeasure.prod
            (rationalFiniteIdeleDifferentialSquareTargetSourceMeasure S)) :=
    Measure.map_prod_map _ _ hreal.measurable hfinite.measurable
  change
    (Measure.map e.symm rationalIdeleRealFiniteDifferentialHaarMeasure).restrict
        (Set.range (rationalIdeleDifferentialRetainedBaseTargetToAmbient S)) = _
  rw [hrange_full, e.symm.measurableEmbedding.restrict_map,
    Set.preimage_image_eq _ e.symm.injective]
  unfold rationalIdeleRealFiniteDifferentialHaarMeasure
  rw [← Measure.prod_restrict]
  rw [← hrealMeasure, hfiniteMeasure]
  rw [hmapProd]
  rw [Measure.map_map e.symm.measurable hprod.measurable]
  rfl

theorem realUnitSquareIdentityChartTarget_pos
    (x : (Rat.unitSquareIdentityChart ℝ).target) :
    0 < ((x : ℝˣ) : ℝ) := by
  let y := (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget.symm x
  have hxy : (x : ℝˣ) = (y : ℝˣ) ^ 2 := by
    have h := congrArg Subtype.val
      ((Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget.apply_symm_apply x)
    change
      Rat.unitSquareIdentityChart ℝ (y : ℝˣ) = (x : ℝˣ) at h
    rw [Rat.unitSquareIdentityChart_apply] at h
    exact h.symm
  rw [hxy]
  exact sq_pos_of_ne_zero y.1.ne_zero

theorem rationalIdeleDifferentialRetainedBaseCarrier_subset_positive
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    rationalIdeleDifferentialRetainedBaseCarrier S ⊆
      positiveRationalAdeleUnitsSubgroup := by
  rintro a ⟨z, rfl⟩
  change rationalIdeleDifferentialRetainedBaseTargetToAmbient S z ∈
    positiveRationalAdeleUnitsSubgroup
  rw [mem_positiveRationalAdeleUnitsSubgroup_iff]
  unfold rationalIdeleDifferentialRetainedBaseTargetToAmbient
  change 0 <
    ((rationalAdeleUnitsRealFiniteContinuousEquiv
      (rationalAdeleUnitsRealFiniteContinuousEquiv.symm
        ((z.1 : ℝˣ), rationalFiniteIdeleDifferentialSquareTargetToAmbient S z.2))).1 : ℝ)
  rw [rationalAdeleUnitsRealFiniteContinuousEquiv.apply_symm_apply]
  exact realUnitSquareIdentityChartTarget_pos z.1

/-- The same assembled target, now carrying its certified positive-real
similitude. -/
def rationalIdeleDifferentialRetainedBaseTargetToPositive
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalIdeleDifferentialRetainedBaseTargetSource S →
      positiveRationalAdeleUnitsSubgroup :=
  fun z ↦ ⟨rationalIdeleDifferentialRetainedBaseTargetToAmbient S z,
    rationalIdeleDifferentialRetainedBaseCarrier_subset_positive S
      (Set.mem_range_self z)⟩

theorem measurable_rationalIdeleDifferentialRetainedBaseTargetToPositive
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (rationalIdeleDifferentialRetainedBaseTargetToPositive S) := by
  exact Measurable.subtype_mk
    (measurableEmbedding_rationalIdeleDifferentialRetainedBaseTargetToAmbient S).measurable

def positiveRationalIdeleDifferentialRetainedBaseCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set positiveRationalAdeleUnitsSubgroup :=
  (fun a : positiveRationalAdeleUnitsSubgroup ↦ (a : RationalAdeleˣ)) ⁻¹'
    rationalIdeleDifferentialRetainedBaseCarrier S

theorem measurableSet_positiveRationalIdeleDifferentialRetainedBaseCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (positiveRationalIdeleDifferentialRetainedBaseCarrier S) :=
  (measurableSet_rationalIdeleDifferentialRetainedBaseCarrier S).preimage
    continuous_subtype_val.measurable

/-- Positive differential idèle Haar restricts to the retained target
carrier with coefficient one. -/
theorem positiveRationalIdeleDifferentialHaarMeasure_restrict_retainedBaseCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    positiveRationalIdeleDifferentialHaarMeasure.restrict
        (positiveRationalIdeleDifferentialRetainedBaseCarrier S) =
      Measure.map
        (rationalIdeleDifferentialRetainedBaseTargetToPositive S)
        (rationalIdeleDifferentialRetainedBaseTargetSourceMeasure S) := by
  let i := fun a : positiveRationalAdeleUnitsSubgroup ↦ (a : RationalAdeleˣ)
  let F := rationalIdeleDifferentialRetainedBaseTargetToPositive S
  let G := rationalIdeleDifferentialRetainedBaseTargetToAmbient S
  let C := positiveRationalIdeleDifferentialRetainedBaseCarrier S
  let A := rationalIdeleDifferentialRetainedBaseCarrier S
  let μ := positiveRationalIdeleDifferentialHaarMeasure
  let ν := rationalIdeleDifferentialRetainedBaseTargetSourceMeasure S
  have hi : MeasurableEmbedding i :=
    isOpen_positiveRationalAdeleUnitsSubgroup.isOpenEmbedding_subtypeVal.measurableEmbedding
  have hsub : A ⊆ positiveRationalAdeleUnitsSubgroup :=
    rationalIdeleDifferentialRetainedBaseCarrier_subset_positive S
  apply hi.map_injective
  calc
    Measure.map i (μ.restrict C) =
        (Measure.map i μ).restrict A := by
      rw [hi.restrict_map]
      rfl
    _ = (rationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalAdeleUnitsSubgroup).restrict A := by
      rw [map_positiveRationalIdeleDifferentialHaarMeasure_subtype]
    _ = rationalIdeleDifferentialHaarMeasure.restrict A := by
      rw [Measure.restrict_restrict
        (measurableSet_rationalIdeleDifferentialRetainedBaseCarrier S)]
      congr 1
      exact Set.inter_eq_left.mpr hsub
    _ = Measure.map G ν := by
      exact rationalIdeleDifferentialHaarMeasure_restrict_retainedBaseCarrier S
    _ = Measure.map i (Measure.map F ν) := by
      rw [Measure.map_map hi.measurable
        (measurable_rationalIdeleDifferentialRetainedBaseTargetToPositive S)]
      rfl

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

local instance retainedBaseDisintegrationDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedBaseDisintegrationPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The exposed real/exceptional square roots and the existing normalized
`SO`/scalar good-tail bind disintegrate positive differential idèle Haar on
the retained base carrier.  The good-tail lift occurs only inside the
iterated integral. -/
theorem lintegral_positiveRationalIdele_retainedBase_disintegration
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let μRE :=
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure B)
    let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
    let μScalar :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    let toPositive :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToPositive B
    (∫⁻ z, ∫⁻ q, ∫⁻ a,
        f (toPositive
          ((Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget z.1,
            (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget B z.2,
              fun v => (a v) ^ 2 *
                V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g q v))))
      ∂μScalar ∂μSO ∂μRE) =
      ∫⁻ b, f b
        ∂(RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure.restrict
          (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier B)) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μR := RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure
  let μE :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure B
  let νR := RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartTargetMeasure
  let νE :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartTargetMeasure B
  let μRE := μR.prod μE
  let νRE := νR.prod νE
  let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
  let μScalar :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
  let rootMap := Prod.map
    (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget
    (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget B)
  let toPositive :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToPositive B
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
  have htoPositive : Measurable toPositive :=
    RationalQuadraticSpaceMatrix.measurable_rationalIdeleDifferentialRetainedBaseTargetToPositive B
  letI : SigmaFinite νE := by
    unfold νE
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartTargetMeasure
    letI (v : {v // v ∈ B}) : SigmaFinite
        (RationalQuadraticSpaceMatrix.padicUnitSquareIdentityChartDifferentialTargetMeasure v.1) := by
      unfold RationalQuadraticSpaceMatrix.padicUnitSquareIdentityChartDifferentialTargetMeasure
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [map_comap_subtype_coe
        (Rat.unitSquareIdentityChart
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_target.measurableSet]
      infer_instance
    infer_instance
  letI : SigmaFinite μScalar := IsFiniteMeasure.toSigmaFinite _
  have htail (z :
      (Rat.unitSquareIdentityChart ℝ).source ×
        RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource B) :
      (∫⁻ q, ∫⁻ a,
          f (toPositive
            ((Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget z.1,
              (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget B z.2,
                fun v => (a v) ^ 2 *
                  V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g q v))))
        ∂μScalar ∂μSO) =
        ∫⁻ b, f (toPositive ((rootMap z).1, ((rootMap z).2, b))) ∂μScalar := by
    let h : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B → ENNReal :=
      fun b => f (toPositive ((rootMap z).1, ((rootMap z).2, b)))
    have hh : Measurable h := by
      exact hf.comp (htoPositive.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    simpa only [h, V, E, B, μSO, μScalar, g, rootMap, toPositive] using
      L.lintegral_retainedIntegralTailSimilitude_disintegration S h hh
  let H :
      (Rat.unitSquareIdentityChart ℝ).target ×
        RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartTarget B →
          ENNReal :=
    fun z => ∫⁻ b, f (toPositive (z.1, (z.2, b))) ∂μScalar
  have hjoint : Measurable (fun z :
      ((Rat.unitSquareIdentityChart ℝ).target ×
        RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartTarget B) ×
          RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B =>
      f (toPositive (z.1.1, (z.1.2, z.2)))) := by
    exact hf.comp (htoPositive.comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hH : Measurable H := hjoint.lintegral_prod_right'
  have hroot : Measurable rootMap :=
    (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget.measurable.prodMap
      (RationalQuadraticSpaceMatrix.measurable_rationalIdeleDifferentialExceptionalSquareChartToTarget B)
  have hBdyadic : RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace ∈ B :=
    Finset.mem_union_left _
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces_dyadic S)
  have hmapRE : Measure.map rootMap μRE = νRE := by
    simpa only [rootMap, μRE, νRE, μR, μE, νR, νE] using
      RationalQuadraticSpaceMatrix.map_retainedRealExceptionalSquareChartToTarget
        B hBdyadic
  calc
    (∫⁻ z, ∫⁻ q, ∫⁻ a,
        f (toPositive
          ((Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget z.1,
            (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget B z.2,
              fun v => (a v) ^ 2 *
                V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g q v))))
      ∂μScalar ∂μSO ∂μRE) =
        ∫⁻ z, H (rootMap z) ∂μRE := by
      apply lintegral_congr
      intro z
      exact htail z
    _ = ∫⁻ z, H z ∂Measure.map rootMap μRE :=
      (lintegral_map hH hroot).symm
    _ = ∫⁻ z, H z ∂νRE := by rw [hmapRE]
    _ = ∫⁻ zR, ∫⁻ zE, ∫⁻ b,
          f (toPositive (zR, (zE, b))) ∂μScalar ∂νE ∂νR := by
      simpa only [H, νRE] using lintegral_prod H hH.aemeasurable
    _ = ∫⁻ z, f (toPositive z)
          ∂(RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetSourceMeasure B) := by
      unfold RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetSourceMeasure
        RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareTargetSourceMeasure
      symm
      calc
        (∫⁻ z, f (toPositive z) ∂νR.prod (νE.prod μScalar)) =
            ∫⁻ zR, ∫⁻ y, f (toPositive (zR, y)) ∂νE.prod μScalar ∂νR := by
          exact lintegral_prod _ (hf.comp htoPositive).aemeasurable
        _ = ∫⁻ zR, ∫⁻ zE, ∫⁻ b,
              f (toPositive (zR, (zE, b))) ∂μScalar ∂νE ∂νR := by
          apply lintegral_congr
          intro zR
          exact lintegral_prod _
            (hjoint.comp
              ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).aemeasurable
    _ = ∫⁻ b, f b
          ∂Measure.map toPositive
            (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetSourceMeasure B) :=
      (lintegral_map hf htoPositive).symm
    _ = ∫⁻ b, f b
        ∂(RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure.restrict
          (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier B)) := by
      rw [RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure_restrict_retainedBaseCarrier B]

end PositiveDefiniteIntegralLattice

end
