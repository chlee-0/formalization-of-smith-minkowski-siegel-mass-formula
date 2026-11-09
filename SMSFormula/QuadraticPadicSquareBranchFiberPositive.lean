import SMSFormula.QuadraticPadicSquareBranchFiberFinite
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicSquareBranchFiberPositiveMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicSquareBranchFiberPositiveBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space]

theorem isOpenEmbedding_padicSquareBranchFiberMap (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (value : ℚ_[prime]) :
    IsOpenEmbedding (form.padicSquareBranchFiberMap prime point hpoint value) := by
  let projection := fun vector : {vector : space // form vector = value} ↦
    ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector.val).1
  have hprojection : Continuous projection :=
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm.continuous.fst.comp
      continuous_subtype_val
  have hcomp : projection ∘ form.padicSquareBranchFiberMap prime point hpoint value =
      (Subtype.val : form.padicSquareBranchFiberDomain prime point value → form.anisotropicOrthogonal point) := by
    funext transverse
    exact congrArg Prod.fst (form.padicSquareBranchFiberMap_coordinates prime point hpoint value transverse)
  refine ⟨Topology.IsEmbedding.of_comp (form.continuous_padicSquareBranchFiberMap prime point hpoint value)
    hprojection (hcomp.symm ▸ Topology.IsEmbedding.subtypeVal), ?_⟩
  rw [form.range_padicSquareBranchFiberMap prime point hpoint value]
  exact (Rat.isOpen_padicUnitSquareScalarSource prime).preimage
    ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm.continuous.snd.comp
      continuous_subtype_val)

omit [FiniteDimensional ℚ_[prime] space] in
theorem padicSquareBranchFiberJacobianInverse_pos (form : QuadraticForm ℚ_[prime] space)
    (point : space) (value : ℚ_[prime]) (transverse : form.anisotropicOrthogonal point) :
    0 < form.padicSquareBranchFiberJacobianInverse prime point value transverse :=
  ENNReal.inv_pos.mpr ENNReal.coe_ne_top

variable [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space]

theorem padicSquareBranchFiberMeasure_open_pos (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point)) [transverseMeasure.IsOpenPosMeasure]
    (value : ℚ_[prime]) (region : Set {vector : space // form vector = value}) (hopen : IsOpen region)
    (hmeets : (region ∩ Set.range (form.padicSquareBranchFiberMap prime point hpoint value)).Nonempty) :
    0 < form.padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value region := by
  letI : (Measure.comap (Subtype.val : form.padicSquareBranchFiberDomain prime point value →
      form.anisotropicOrthogonal point) transverseMeasure).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap transverseMeasure
      (form.isOpen_padicSquareBranchFiberDomain prime point value).isOpenEmbedding_subtypeVal
  have hpreimage : (form.padicSquareBranchFiberMap prime point hpoint value ⁻¹' region).Nonempty := by
    obtain ⟨vector, hregion, transverse, rfl⟩ := hmeets
    exact ⟨transverse, hregion⟩
  rw [padicSquareBranchFiberMeasure, Measure.map_apply
    (form.measurable_padicSquareBranchFiberMap prime point hpoint value) hopen.measurableSet]
  apply pos_iff_ne_zero.mpr
  have hweight : Measurable (fun transverse : form.padicSquareBranchFiberDomain prime point value ↦
      form.padicSquareBranchFiberJacobianInverse prime point value transverse.val) :=
    (form.measurable_padicSquareBranchFiberJacobianInverse prime point value).comp measurable_subtype_coe
  intro hzero
  have hzero' := (withDensity_apply_eq_zero (μ := Measure.comap
    (Subtype.val : form.padicSquareBranchFiberDomain prime point value → form.anisotropicOrthogonal point)
    transverseMeasure) hweight).mp hzero
  have hsupport : {transverse : form.padicSquareBranchFiberDomain prime point value |
      form.padicSquareBranchFiberJacobianInverse prime point value transverse.val ≠ 0} = univ := by
    ext transverse
    simp only [mem_setOf_eq, mem_univ, iff_true]
    exact (form.padicSquareBranchFiberJacobianInverse_pos prime point value transverse.val).ne'
  rw [hsupport, univ_inter] at hzero'
  exact ((hopen.preimage (form.continuous_padicSquareBranchFiberMap prime point hpoint value)).measure_pos
    _ hpreimage).ne' hzero'

theorem padicSquareBranchFiberMeasure_image_open_pos (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point)) [transverseMeasure.IsOpenPosMeasure]
    (value : ℚ_[prime]) (region : Set (form.padicSquareBranchFiberDomain prime point value))
    (hopen : IsOpen region) (hnonempty : region.Nonempty) :
    0 < form.padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value
      (form.padicSquareBranchFiberMap prime point hpoint value '' region) := by
  apply form.padicSquareBranchFiberMeasure_open_pos prime point hpoint transverseMeasure value _
    ((form.isOpenEmbedding_padicSquareBranchFiberMap prime point hpoint value).isOpenMap _ hopen)
  obtain ⟨transverse, htransverse⟩ := hnonempty
  exact ⟨_, ⟨transverse, htransverse, rfl⟩, ⟨transverse, rfl⟩⟩

theorem padicSquareBranchFiberMeasure_normalized_open_pos [LocallyCompactSpace space]
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    (value : ℚ_[prime]) (region : Set {vector : space // form vector = value}) (hopen : IsOpen region)
    (hmeets : (region ∩ Set.range (form.padicSquareBranchFiberMap prime point hpoint value)).Nonempty) :
    0 < ((form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime point hpoint transverseHaar value) region := by
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top)
    (form.padicSquareBranchFiberMeasure_open_pos prime point hpoint transverseHaar value region hopen hmeets).ne'

theorem padicSquareBranchFiberMeasure_exists_compact_pos_lt_top [LocallyCompactSpace space]
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point)) [transverseHaar.IsAddHaarMeasure]
    (value : ℚ_[prime]) (vector : {vector : space // form vector = value})
    (hvector : vector ∈ Set.range (form.padicSquareBranchFiberMap prime point hpoint value)) :
    ∃ compactSet : Set {vector : space // form vector = value}, IsCompact compactSet ∧
      vector ∈ interior compactSet ∧ compactSet ⊆ Set.range (form.padicSquareBranchFiberMap prime point hpoint value) ∧
      0 < form.padicSquareBranchFiberMeasure prime point hpoint transverseHaar value compactSet ∧
      form.padicSquareBranchFiberMeasure prime point hpoint transverseHaar value compactSet < ∞ := by
  have hform : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  letI : LocallyCompactSpace {vector : space // form vector = value} :=
    (isClosed_eq hform continuous_const).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨compactSet, hcompact, hneighborhood, hsubset⟩ := exists_compact_subset
    (form.isOpenEmbedding_padicSquareBranchFiberMap prime point hpoint value).isOpen_range hvector
  refine ⟨compactSet, hcompact, hneighborhood, hsubset, ?_,
    form.padicSquareBranchFiberMeasure_compact_lt_top prime point hpoint transverseHaar value compactSet hcompact hsubset⟩
  exact lt_of_lt_of_le
    (form.padicSquareBranchFiberMeasure_open_pos prime point hpoint transverseHaar value (interior compactSet)
      isOpen_interior ⟨vector, hneighborhood, hvector⟩)
    (measure_mono interior_subset)

end QuadraticMap
