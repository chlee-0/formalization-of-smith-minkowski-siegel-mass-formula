import SMSFormula.QuadraticPadicSquareBranchFiberImage

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance : MeasurableSpace ℚ_[prime] := borel _
local instance : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space]

theorem isCompact_preimage_padicSquareBranchFiberMap (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (value : ℚ_[prime])
    (compactSet : Set {vector : space // form vector = value}) (hcompact : IsCompact compactSet)
    (hbranch : compactSet ⊆ Set.range (form.padicSquareBranchFiberMap prime point hpoint value)) :
    IsCompact (form.padicSquareBranchFiberMap prime point hpoint value ⁻¹' compactSet) := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have hequal : Subtype.val '' (form.padicSquareBranchFiberMap prime point hpoint value ⁻¹' compactSet) =
      (fun vector : {vector : space // form vector = value} ↦
        ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector.val).1) '' compactSet := by
    ext transverse
    constructor
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨form.padicSquareBranchFiberMap prime point hpoint value source, hsource,
        congrArg Prod.fst (form.padicSquareBranchFiberMap_coordinates prime point hpoint value source)⟩
    · rintro ⟨vector, hvector, rfl⟩
      obtain ⟨source, rfl⟩ := hbranch hvector
      exact ⟨source, hvector,
        (congrArg Prod.fst (form.padicSquareBranchFiberMap_coordinates prime point hpoint value source)).symm⟩
  rw [hequal]
  exact hcompact.image ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm.continuous.fst.comp
    continuous_subtype_val)

theorem continuous_padicSquareBranchFiberJacobianInverse_on_domain (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (value : ℚ_[prime]) :
    Continuous (fun transverse : form.padicSquareBranchFiberDomain prime point value ↦
      form.padicSquareBranchFiberJacobianInverse prime point value transverse.val) := by
  have hscalar := ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm.continuous.comp
    (continuous_subtype_val.comp (form.continuous_padicSquareBranchFiberMap prime point hpoint value))).snd
  have hcontinuous := (ENNReal.continuous_coe.comp
    ((continuous_const (y := 2 * form point)).mul hscalar).nnnorm).inv
  convert hcontinuous using 1
  funext transverse
  dsimp only [Function.comp_def, Pi.mul_apply]
  rw [form.padicSquareBranchFiberMap_coordinates prime]
  rfl

omit [FiniteDimensional ℚ_[prime] space] in
theorem padicSquareBranchFiberJacobianInverse_ne_top_on_domain (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (value : ℚ_[prime])
    (transverse : form.padicSquareBranchFiberDomain prime point value) :
    form.padicSquareBranchFiberJacobianInverse prime point value transverse.val ≠ ∞ := by
  have hsource := (Rat.padicUnitSquareScalarInverse_mem_and_sq prime transverse.property).1
  have hnonzero := Rat.padicUnitSquareScalarSource_ne_zero prime hsource
  unfold padicSquareBranchFiberJacobianInverse
  rw [Rat.padicUnitSquareTargetSupportedInverse_eq prime transverse.property]
  exact ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr
    (mul_ne_zero (mul_ne_zero (by norm_num) hpoint) hnonzero)))

variable [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space]

theorem padicSquareBranchFiberMeasure_compact_lt_top (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point))
    [IsFiniteMeasureOnCompacts transverseMeasure] (value : ℚ_[prime])
    (compactSet : Set {vector : space // form vector = value}) (hcompact : IsCompact compactSet)
    (hbranch : compactSet ⊆ Set.range (form.padicSquareBranchFiberMap prime point hpoint value)) :
    form.padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value compactSet < ∞ := by
  have hpreimage := form.isCompact_preimage_padicSquareBranchFiberMap prime point hpoint value compactSet hcompact hbranch
  have hfinite : (Measure.comap (Subtype.val : form.padicSquareBranchFiberDomain prime point value → form.anisotropicOrthogonal point)
      transverseMeasure) (form.padicSquareBranchFiberMap prime point hpoint value ⁻¹' compactSet) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (Measure.comap_apply_le _ _ hpreimage.measurableSet.nullMeasurableSet)
    exact (hpreimage.image continuous_subtype_val).measure_lt_top
  have hweight := form.continuous_padicSquareBranchFiberJacobianInverse_on_domain prime point hpoint value
  have hnotop := form.padicSquareBranchFiberJacobianInverse_ne_top_on_domain prime point hpoint value
  have hnnreal := ENNReal.continuousOn_toNNReal.comp_continuous hweight hnotop
  rw [padicSquareBranchFiberMeasure, Measure.map_apply
    (form.measurable_padicSquareBranchFiberMap prime point hpoint value) hcompact.measurableSet,
    withDensity_apply _ hpreimage.measurableSet]
  have hequal : (fun transverse : form.padicSquareBranchFiberDomain prime point value ↦
      form.padicSquareBranchFiberJacobianInverse prime point value transverse.val) =
      (fun transverse : form.padicSquareBranchFiberDomain prime point value ↦
        ((form.padicSquareBranchFiberJacobianInverse prime point value transverse.val).toNNReal : ℝ≥0∞)) := by
    funext transverse
    exact (ENNReal.coe_toNNReal (hnotop transverse)).symm
  rw [hequal]
  exact setLIntegral_lt_top_of_isCompact hfinite hpreimage hnnreal

theorem padicSquareBranchFiberMeasure_finiteAt_nhds_of_mem_range [LocallyCompactSpace space]
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point))
    [IsFiniteMeasureOnCompacts transverseMeasure] (value : ℚ_[prime])
    (vector : {vector : space // form vector = value})
    (hvector : vector ∈ Set.range (form.padicSquareBranchFiberMap prime point hpoint value)) :
    (form.padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value).FiniteAtFilter (𝓝 vector) := by
  have hform : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  letI : LocallyCompactSpace {vector : space // form vector = value} :=
    (isClosed_eq hform continuous_const).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hopen : IsOpen (Set.range (form.padicSquareBranchFiberMap prime point hpoint value)) := by
    rw [form.range_padicSquareBranchFiberMap prime point hpoint value]
    exact (Rat.isOpen_padicUnitSquareScalarSource prime).preimage
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm.continuous.snd.comp
        continuous_subtype_val)
  obtain ⟨compactSet, hcompact, hneighborhood, hsubset⟩ := exists_compact_subset hopen hvector
  exact ⟨compactSet, mem_interior_iff_mem_nhds.mp hneighborhood,
    form.padicSquareBranchFiberMeasure_compact_lt_top prime point hpoint transverseMeasure value compactSet hcompact hsubset⟩

end QuadraticMap
