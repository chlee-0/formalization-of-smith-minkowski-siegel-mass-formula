import SMSFormula.RationalCliffordGeneralSpinHorizontalDifferentialSOChartRestriction
import SMSFormula.RationalIdeleDifferentialFiniteIdeleHaarRegularity

/-!
# Differential idele Haar on the scalar square chart

The ambient central-fiber kernel uses the compact-normalized differential Haar
measure on rational ideles.  This file restricts that global measure to
the scalar square chart occurring in the completed horizontal `GSpin`
cylinder.  The finite exceptional coordinates use the inverse-image
square branches, while every unchanged coordinate remains in its normalized
integral-unit subgroup.

The resulting finite and full-adelic formulas have coefficient one.  This is
the differential idele restricted-product normalization; it does not cancel
the separate absolute `SO` block weight, horizontal block weight, lattice
stabilizer volume, or independently selected idele-class Haar scalar.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

local instance rationalIdeleDifferentialSquareChartDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance rationalIdeleDifferentialSquareChartPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance rationalIdeleDifferentialSquareChartLocalMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance rationalIdeleDifferentialSquareChartLocalBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance rationalIdeleDifferentialSquareChartExceptionalSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (RationalIdeleDifferentialExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance rationalIdeleDifferentialSquareChartExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialExceptionalProduct S) :=
  Pi.borelSpace

/-! ## Finite exceptional square branches -/

/-- Product of the chosen scalar square-source branches over a finite set of
places. -/
abbrev RationalIdeleDifferentialExceptionalSquareChartSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ S}) →
    (Rat.unitSquareIdentityChart
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source

/-- Product of compact-normalized differential Haar comapped to the chosen
square branches. -/
def rationalIdeleDifferentialExceptionalSquareChartSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalIdeleDifferentialExceptionalSquareChartSource S) :=
  Measure.pi fun v : {v // v ∈ S} ↦
    padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1

instance rationalIdeleDifferentialExceptionalSquareChartSourceMeasure_sigmaFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (rationalIdeleDifferentialExceptionalSquareChartSourceMeasure S) := by
  letI (v : {v // v ∈ S}) : SigmaFinite
      (padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1) := by
    let chart := Rat.unitSquareIdentityChart
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
    letI : SigmaFinite (rationalPadicIdeleDifferentialHaarMeasure v.1) :=
      Measure.IsHaarMeasure.sigmaFinite _
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure,
      map_comap_subtype_coe chart.open_source.measurableSet]
    infer_instance
  unfold rationalIdeleDifferentialExceptionalSquareChartSourceMeasure
  infer_instance

/-- Forget the square-branch subtype coordinatewise. -/
def rationalIdeleDifferentialExceptionalSquareChartToProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalIdeleDifferentialExceptionalSquareChartSource S →
      RationalIdeleDifferentialExceptionalProduct S :=
  fun x v ↦ x v

theorem measurableEmbedding_rationalIdeleDifferentialExceptionalSquareChartToProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (rationalIdeleDifferentialExceptionalSquareChartToProduct S) := by
  apply Topology.IsOpenEmbedding.measurableEmbedding
  apply Topology.IsOpenEmbedding.piMap
  intro v
  exact (Rat.unitSquareIdentityChart
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_source.isOpenEmbedding_subtypeVal

/-- Literal product carrier occupied by the chosen square branches. -/
def rationalIdeleDifferentialExceptionalSquareChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (RationalIdeleDifferentialExceptionalProduct S) :=
  Set.pi Set.univ fun v : {v // v ∈ S} ↦
    (Rat.unitSquareIdentityChart
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source

theorem measurableSet_rationalIdeleDifferentialExceptionalSquareChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (rationalIdeleDifferentialExceptionalSquareChartCarrier S) := by
  apply MeasurableSet.univ_pi
  intro v
  exact (Rat.unitSquareIdentityChart
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_source.measurableSet

/-- The exceptional differential square chart is exactly the restriction of
the unrestricted exceptional product, with no conversion coefficient. -/
theorem map_rationalIdeleDifferentialExceptionalSquareChartToProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (rationalIdeleDifferentialExceptionalSquareChartToProduct S)
        (rationalIdeleDifferentialExceptionalSquareChartSourceMeasure S) =
      (rationalIdeleDifferentialExceptionalProductMeasure S).restrict
        (rationalIdeleDifferentialExceptionalSquareChartCarrier S) := by
  let f := fun v : {v // v ∈ S} ↦
    fun x : (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source ↦ (x :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
  let μ := fun v : {v // v ∈ S} ↦
    padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1
  have hlocal (v : {v // v ∈ S}) :
      (μ v).map (f v) =
        (rationalPadicIdeleDifferentialHaarMeasure v.1).restrict
          (Rat.unitSquareIdentityChart
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source := by
    unfold μ f padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure
    exact map_comap_subtype_coe
      (μ := rationalPadicIdeleDifferentialHaarMeasure v.1)
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_source.measurableSet
  letI (v : {v // v ∈ S}) : SigmaFinite ((μ v).map (f v)) := by
    rw [hlocal]
    infer_instance
  have hpi :
      (Measure.pi μ).map (fun x v ↦ f v (x v)) =
        Measure.pi fun v ↦ (μ v).map (f v) :=
    Measure.pi_map_pi fun v ↦ continuous_subtype_val.measurable.aemeasurable
  simp_rw [hlocal] at hpi
  simpa only [rationalIdeleDifferentialExceptionalSquareChartToProduct,
    rationalIdeleDifferentialExceptionalSquareChartSourceMeasure,
    rationalIdeleDifferentialExceptionalProductMeasure,
    rationalIdeleDifferentialExceptionalSquareChartCarrier,
    Measure.restrict_pi_pi, f, μ] using hpi

/-! ## Finite-idele square chart -/

local instance rationalIdeleDifferentialSquareChartIntegralFactorSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    SecondCountableTopology (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance rationalIdeleDifferentialSquareChartIntegralFactorBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    BorelSpace (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
  Subtype.borelSpace _

local instance rationalIdeleDifferentialSquareChartTailSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (RationalIdeleDifferentialIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance rationalIdeleDifferentialSquareChartTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialIntegralTail S) :=
  Pi.borelSpace

local instance rationalIdeleDifferentialSquareChartFiniteMeasurableSpace :
    MeasurableSpace RationalFiniteAdeleˣ := borel _

local instance rationalIdeleDifferentialSquareChartFiniteBorelSpace :
    BorelSpace RationalFiniteAdeleˣ := ⟨rfl⟩

local instance rationalIdeleDifferentialSquareChartBlockBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- Exceptional square branches together with the complete normalized
integral-unit tail. -/
abbrev RationalFiniteIdeleDifferentialSquareChartSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  RationalIdeleDifferentialExceptionalSquareChartSource S ×
    RationalIdeleDifferentialIntegralTail S

/-- Bare differential finite-idele square-chart source measure. -/
def rationalFiniteIdeleDifferentialSquareChartSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalFiniteIdeleDifferentialSquareChartSource S) :=
  (rationalIdeleDifferentialExceptionalSquareChartSourceMeasure S).prod
    (rationalIdeleDifferentialNormalizedIntegralTailMeasure S)

instance rationalFiniteIdeleDifferentialSquareChartSourceMeasure_sigmaFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite (rationalFiniteIdeleDifferentialSquareChartSourceMeasure S) := by
  letI : SigmaFinite
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  unfold rationalFiniteIdeleDifferentialSquareChartSourceMeasure
  infer_instance

/-- Assemble the exceptional square chart and normalized integral tail into
the genuine rational finite-idele carrier. -/
def rationalFiniteIdeleDifferentialSquareChartToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalFiniteIdeleDifferentialSquareChartSource S → RationalFiniteAdeleˣ :=
  rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S ∘
    rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph S ∘
      Prod.map (rationalIdeleDifferentialExceptionalSquareChartToProduct S) id

theorem measurableEmbedding_rationalFiniteIdeleDifferentialSquareChartToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding (rationalFiniteIdeleDifferentialSquareChartToAmbient S) := by
  unfold rationalFiniteIdeleDifferentialSquareChartToAmbient
  exact
    (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding S).comp
      ((rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph S).measurableEmbedding.comp
        ((measurableEmbedding_rationalIdeleDifferentialExceptionalSquareChartToProduct S).prodMap
          MeasurableEmbedding.id))

/-- Finite-idele carrier occupied by the square branches at the exceptional
places and the complete integral-unit tail. -/
def rationalFiniteIdeleDifferentialSquareChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set RationalFiniteAdeleˣ :=
  Set.range (rationalFiniteIdeleDifferentialSquareChartToAmbient S)

theorem measurableSet_rationalFiniteIdeleDifferentialSquareChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (rationalFiniteIdeleDifferentialSquareChartCarrier S) :=
  (measurableEmbedding_rationalFiniteIdeleDifferentialSquareChartToAmbient S)
    |>.measurableSet_range

/-- Compact-normalized finite-idele differential Haar restricts to the
scalar square chart with coefficient one. -/
theorem rationalFiniteIdeleDifferentialHaarMeasure_restrict_squareChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    rationalFiniteIdeleDifferentialHaarMeasure.restrict
        (rationalFiniteIdeleDifferentialSquareChartCarrier S) =
      Measure.map
        (rationalFiniteIdeleDifferentialSquareChartToAmbient S)
        (rationalFiniteIdeleDifferentialSquareChartSourceMeasure S) := by
  let chart := rationalIdeleDifferentialExceptionalSquareChartToProduct S
  let μchart := rationalIdeleDifferentialExceptionalSquareChartSourceMeasure S
  let C := rationalIdeleDifferentialExceptionalSquareChartCarrier S
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
    measurableEmbedding_rationalIdeleDifferentialExceptionalSquareChartToProduct S
  have hchart_range : Set.range chart = C := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      intro v _
      exact (y v).2
    · intro hx
      let y : RationalIdeleDifferentialExceptionalSquareChartSource S :=
        fun v ↦ ⟨x v, hx v (Set.mem_univ v)⟩
      exact ⟨y, rfl⟩
  have hD : MeasurableSet D :=
    (measurableSet_rationalIdeleDifferentialExceptionalSquareChartCarrier S).prod
      MeasurableSet.univ
  have hmap_chart : Measure.map chart μchart = μE.restrict C :=
    map_rationalIdeleDifferentialExceptionalSquareChartToProduct S
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
    unfold μchart
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

/-! ## Full rational-idele square chart -/

local instance rationalIdeleDifferentialSquareChartRealMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

local instance rationalIdeleDifferentialSquareChartRealBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

local instance rationalIdeleDifferentialSquareChartFullMeasurableSpace :
    MeasurableSpace RationalAdeleˣ := borel _

local instance rationalIdeleDifferentialSquareChartFullBorelSpace :
    BorelSpace RationalAdeleˣ := ⟨rfl⟩

/-- Real square branch times the finite differential square chart. -/
abbrev RationalIdeleDifferentialFullSquareChartSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (Rat.unitSquareIdentityChart ℝ).source ×
    RationalFiniteIdeleDifferentialSquareChartSource S

/-- Bare full differential scalar-chart measure. -/
def rationalIdeleDifferentialFullSquareChartSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalIdeleDifferentialFullSquareChartSource S) :=
  realUnitSquareIdentityChartAmbientSourceMeasure.prod
    (rationalFiniteIdeleDifferentialSquareChartSourceMeasure S)

/-- Assemble the real and finite square branches into the literal rational
idele carrier. -/
def rationalIdeleDifferentialFullSquareChartToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalIdeleDifferentialFullSquareChartSource S → RationalAdeleˣ :=
  rationalAdeleUnitsRealFiniteContinuousEquiv.symm ∘
    Prod.map Subtype.val (rationalFiniteIdeleDifferentialSquareChartToAmbient S)

theorem measurableEmbedding_rationalIdeleDifferentialFullSquareChartToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding (rationalIdeleDifferentialFullSquareChartToAmbient S) := by
  unfold rationalIdeleDifferentialFullSquareChartToAmbient
  exact rationalAdeleUnitsRealFiniteContinuousEquiv.symm.measurableEmbedding.comp
    ((Rat.unitSquareIdentityChart ℝ).open_source.isOpenEmbedding_subtypeVal
      |>.measurableEmbedding.prodMap
        (measurableEmbedding_rationalFiniteIdeleDifferentialSquareChartToAmbient S))

/-- Full rational-idele carrier occupied by the square branches at the
exceptional places and the integral tail. -/
def rationalIdeleDifferentialFullSquareChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set RationalAdeleˣ :=
  Set.range (rationalIdeleDifferentialFullSquareChartToAmbient S)

theorem measurableSet_rationalIdeleDifferentialFullSquareChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (rationalIdeleDifferentialFullSquareChartCarrier S) :=
  (measurableEmbedding_rationalIdeleDifferentialFullSquareChartToAmbient S)
    |>.measurableSet_range

/-- Full differential idele Haar restricts to the scalar square
chart with coefficient one. -/
theorem rationalIdeleDifferentialHaarMeasure_restrict_squareChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    rationalIdeleDifferentialHaarMeasure.restrict
        (rationalIdeleDifferentialFullSquareChartCarrier S) =
      Measure.map
        (rationalIdeleDifferentialFullSquareChartToAmbient S)
        (rationalIdeleDifferentialFullSquareChartSourceMeasure S) := by
  let realMap := fun x : (Rat.unitSquareIdentityChart ℝ).source ↦ (x : ℝˣ)
  let finiteMap := rationalFiniteIdeleDifferentialSquareChartToAmbient S
  let e := rationalAdeleUnitsRealFiniteContinuousEquiv.toHomeomorph
  let realCarrier := (Rat.unitSquareIdentityChart ℝ).source
  let finiteCarrier := rationalFiniteIdeleDifferentialSquareChartCarrier S
  let realFiniteCarrier : Set (ℝˣ × RationalFiniteAdeleˣ) :=
    realCarrier ×ˢ finiteCarrier
  have hreal : MeasurableEmbedding realMap :=
    (Rat.unitSquareIdentityChart ℝ).open_source.isOpenEmbedding_subtypeVal
      |>.measurableEmbedding
  have hfinite : MeasurableEmbedding finiteMap :=
    measurableEmbedding_rationalFiniteIdeleDifferentialSquareChartToAmbient S
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
      Set.range (rationalIdeleDifferentialFullSquareChartToAmbient S) =
        e.symm '' realFiniteCarrier := by
    change Set.range (e.symm ∘ Prod.map realMap finiteMap) = _
    rw [Set.range_comp, hrange]
  have hrealMeasure :
      Measure.map realMap realUnitSquareIdentityChartAmbientSourceMeasure =
        (Measure.haar : Measure ℝˣ).restrict realCarrier := by
    unfold realUnitSquareIdentityChartAmbientSourceMeasure
    exact map_comap_subtype_coe
      (μ := (Measure.haar : Measure ℝˣ))
      (Rat.unitSquareIdentityChart ℝ).open_source.measurableSet
  have hfiniteMeasure :
      rationalFiniteIdeleDifferentialHaarMeasure.restrict finiteCarrier =
        Measure.map finiteMap
          (rationalFiniteIdeleDifferentialSquareChartSourceMeasure S) :=
    rationalFiniteIdeleDifferentialHaarMeasure_restrict_squareChart S
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
    Measure.IsHaarMeasure.sigmaFinite _
  letI : SigmaFinite rationalFiniteIdeleDifferentialHaarMeasure := by
    rw [← rationalFiniteIdeleDifferentialDirectedMeasure_eq_haar]
    infer_instance
  letI : SFinite
      (Measure.map finiteMap
        (rationalFiniteIdeleDifferentialSquareChartSourceMeasure S)) :=
    inferInstance
  letI : SigmaFinite realUnitSquareIdentityChartAmbientSourceMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [hrealMeasure]
    infer_instance
  have hmapProd :
      (Measure.map realMap realUnitSquareIdentityChartAmbientSourceMeasure).prod
          (Measure.map finiteMap
            (rationalFiniteIdeleDifferentialSquareChartSourceMeasure S)) =
        Measure.map (Prod.map realMap finiteMap)
          (realUnitSquareIdentityChartAmbientSourceMeasure.prod
            (rationalFiniteIdeleDifferentialSquareChartSourceMeasure S)) :=
    Measure.map_prod_map _ _ hreal.measurable hfinite.measurable
  change
    (Measure.map e.symm rationalIdeleRealFiniteDifferentialHaarMeasure).restrict
        (Set.range (rationalIdeleDifferentialFullSquareChartToAmbient S)) = _
  rw [hrange_full, e.symm.measurableEmbedding.restrict_map,
    Set.preimage_image_eq _ e.symm.injective]
  unfold rationalIdeleRealFiniteDifferentialHaarMeasure
  rw [← Measure.prod_restrict]
  rw [← hrealMeasure, hfiniteMeasure]
  rw [hmapProd]
  rw [Measure.map_map e.symm.measurable hprod.measurable]
  rfl

end RationalQuadraticSpaceMatrix
