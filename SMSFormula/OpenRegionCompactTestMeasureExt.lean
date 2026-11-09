import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.Topology.Metrizable.Basic

noncomputable section

open Set MeasureTheory Topology TopologicalSpace
open scoped ENNReal

namespace MeasureTheory.Measure

variable {ambient : Type*} [TopologicalSpace ambient] [T2Space ambient]
  [PseudoMetrizableSpace ambient] [LocallyCompactSpace ambient]
  [SecondCountableTopology ambient] [MeasurableSpace ambient] [BorelSpace ambient]

omit [PseudoMetrizableSpace ambient] [LocallyCompactSpace ambient] [SecondCountableTopology ambient] in
theorem comap_region_finiteOnCompacts (measure : Measure ambient) (region : Set ambient)
    (hfinite : ∀ compactSet : Set ambient, IsCompact compactSet → compactSet ⊆ region → measure compactSet < ∞) :
    IsFiniteMeasureOnCompacts (measure.comap (Subtype.val : region → ambient)) := by
  constructor
  intro compactSet hcompact
  apply lt_of_le_of_lt (Measure.comap_apply_le _ _ hcompact.measurableSet.nullMeasurableSet)
  exact hfinite _ (hcompact.image continuous_subtype_val) (Subtype.coe_image_subset _ _)

theorem restrict_eq_of_compact_tests_on_open (first second : Measure ambient)
    (region : Set ambient) (hopen : IsOpen region)
    (hfirst : ∀ compactSet : Set ambient, IsCompact compactSet → compactSet ⊆ region → first compactSet < ∞)
    (hsecond : ∀ compactSet : Set ambient, IsCompact compactSet → compactSet ⊆ region → second compactSet < ∞)
    (htests : ∀ weight : ambient → ℝ, Continuous weight → HasCompactSupport weight →
      tsupport weight ⊆ region →
      (∫⁻ vector, ENNReal.ofReal (weight vector) ∂first) =
        ∫⁻ vector, ENNReal.ofReal (weight vector) ∂second) :
    first.restrict region = second.restrict region := by
  letI : LocallyCompactSpace region := hopen.locallyCompactSpace
  letI := first.comap_region_finiteOnCompacts region hfirst
  letI := second.comap_region_finiteOnCompacts region hsecond
  have hequal : first.comap (Subtype.val : region → ambient) = second.comap Subtype.val := by
    apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
    intro test
    let weight : ambient → ℝ := Subtype.val.extend (fun vector : region ↦ (test vector : ℝ)) 0
    have htestContinuous : Continuous (fun vector : region ↦ (test vector : ℝ)) :=
      NNReal.continuous_coe.comp test.continuous
    have htestCompact : HasCompactSupport (fun vector : region ↦ (test vector : ℝ)) := by
      exact test.hasCompactSupport.comp_left (by simp)
    have hweightContinuous : Continuous weight := HasCompactSupport.continuous_extend_zero hopen htestContinuous htestCompact
    have hweightCompact : HasCompactSupport weight := htestCompact.extend_zero continuous_subtype_val
    have hsupport : tsupport weight ⊆ region :=
      (htestCompact.tsupport_extend_zero_subset continuous_subtype_val).trans (Subtype.coe_image_subset _ _)
    have hweight (vector : region) : weight vector.val = (test vector : ℝ) :=
      congrFun (Function.extend_comp Subtype.val_injective _ _) vector
    have hpair := htests weight hweightContinuous hweightCompact hsupport
    have htransport (measure : Measure ambient) :
        (∫⁻ vector : region, ENNReal.ofReal (test vector : ℝ) ∂measure.comap Subtype.val) =
          ∫⁻ vector, ENNReal.ofReal (weight vector) ∂measure := by
      calc
        _ = ∫⁻ vector : region, ENNReal.ofReal (weight vector.val) ∂measure.comap Subtype.val := by
          simp only [hweight]
        _ = ∫⁻ vector in region, ENNReal.ofReal (weight vector) ∂measure :=
          lintegral_subtype_comap (μ := measure) hopen.measurableSet (fun vector ↦ ENNReal.ofReal (weight vector))
        _ = _ := by
          rw [← lintegral_indicator hopen.measurableSet]
          apply lintegral_congr
          intro vector
          by_cases hmem : vector ∈ region
          · exact Set.indicator_of_mem hmem _
          · rw [Set.indicator_of_notMem hmem,
              image_eq_zero_of_notMem_tsupport (fun hs ↦ hmem (hsupport hs)), ENNReal.ofReal_zero]
    rw [← htransport first, ← htransport second] at hpair
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun vector ↦ (test vector).coe_nonneg)) htestContinuous.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun vector ↦ (test vector).coe_nonneg)) htestContinuous.aestronglyMeasurable,
      hpair]
  have hmapped := congrArg (Measure.map (Subtype.val : region → ambient)) hequal
  simpa only [map_comap_subtype_coe hopen.measurableSet] using hmapped

theorem closedSubtype_restrict_eq_of_compact_ambient_tests
    (closedSet : Set ambient) (hclosed : IsClosed closedSet)
    (first second : Measure closedSet) (region : Set ambient) (hopen : IsOpen region)
    (hfirst : ∀ compactSet : Set closedSet, IsCompact compactSet →
      compactSet ⊆ Subtype.val ⁻¹' region → first compactSet < ∞)
    (hsecond : ∀ compactSet : Set closedSet, IsCompact compactSet →
      compactSet ⊆ Subtype.val ⁻¹' region → second compactSet < ∞)
    (htests : ∀ weight : ambient → ℝ, Continuous weight → HasCompactSupport weight →
      tsupport weight ⊆ region →
      (∫⁻ vector, ENNReal.ofReal (weight vector.val) ∂first) =
        ∫⁻ vector, ENNReal.ofReal (weight vector.val) ∂second) :
    first.restrict (Subtype.val ⁻¹' region) = second.restrict (Subtype.val ⁻¹' region) := by
  have hfinite (measure : Measure closedSet)
      (hmeasure : ∀ compactSet : Set closedSet, IsCompact compactSet →
        compactSet ⊆ Subtype.val ⁻¹' region → measure compactSet < ∞)
      (compactSet : Set ambient) (hcompact : IsCompact compactSet) (hsubset : compactSet ⊆ region) :
      (Measure.map Subtype.val measure) compactSet < ∞ := by
    rw [Measure.map_apply measurable_subtype_coe hcompact.measurableSet]
    exact hmeasure _ (hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hcompact)
      (Set.preimage_mono hsubset)
  have hequal := restrict_eq_of_compact_tests_on_open (Measure.map Subtype.val first)
    (Measure.map Subtype.val second) region hopen (hfinite first hfirst) (hfinite second hsecond)
    (fun weight hcontinuous hcompact hsupport ↦ by
      rw [lintegral_map hcontinuous.measurable.ennreal_ofReal measurable_subtype_coe,
        lintegral_map hcontinuous.measurable.ennreal_ofReal measurable_subtype_coe]
      exact htests weight hcontinuous hcompact hsupport)
  apply (MeasurableEmbedding.subtype_coe hclosed.measurableSet).map_injective
  simpa only [Measure.restrict_map measurable_subtype_coe hopen.measurableSet] using hequal

end MeasureTheory.Measure
