import SMSFormula.QuadraticPadicSquareBranchFiberOverlap
import SMSFormula.QuadraticPadicSquareBranchIsometry

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicSquareBranchHaarIndependenceMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicSquareBranchHaarIndependenceBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]
  [SecondCountableTopology space]

omit [SecondCountableTopology space] in
theorem padicSquareBranchFiberMeasure_restrict_range (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point)) (value : ℚ_[prime]) :
    (form.padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value).restrict
      (Set.range (form.padicSquareBranchFiberMap prime point hpoint value)) =
    form.padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value := by
  have hopen : IsOpen (Set.range (form.padicSquareBranchFiberMap prime point hpoint value)) := by
    rw [form.range_padicSquareBranchFiberMap prime point hpoint value]
    exact (Rat.isOpen_padicUnitSquareScalarSource prime).preimage
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm.continuous.snd.comp
        continuous_subtype_val)
  exact Measure.restrict_eq_self_of_ae_mem
    (ae_map_mem_range _ hopen.measurableSet _)

variable [LocallyCompactSpace space]

theorem padicSquareBranchFiberMeasure_normalized_eq (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0)
    (firstHaar secondHaar : Measure (form.anisotropicOrthogonal point))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [firstHaar.IsAddHaarMeasure] [secondHaar.IsAddHaarMeasure]
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) :
    (form.anisotropicOrthogonalProductHaarScalar point hpoint firstHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime point hpoint firstHaar value =
    (form.anisotropicOrthogonalProductHaarScalar point hpoint secondHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime point hpoint secondHaar value := by
  have hequal := form.padicSquareBranchFiberMeasure_normalized_restrict_overlap_eq prime point point hpoint hpoint
    firstHaar secondHaar scalarHaar vectorHaar value
  have hregion : (Subtype.val ⁻¹' form.padicSquareBranchOverlap prime point point hpoint hpoint) =
      Set.range (form.padicSquareBranchFiberMap prime point hpoint value) := by
    rw [form.range_padicSquareBranchFiberMap prime point hpoint value]
    ext vector
    simp only [padicSquareBranchOverlap, Set.mem_preimage, Set.mem_setOf_eq, and_self]
  rw [hregion, Measure.restrict_smul, Measure.restrict_smul,
    form.padicSquareBranchFiberMeasure_restrict_range prime point hpoint firstHaar value,
    form.padicSquareBranchFiberMeasure_restrict_range prime point hpoint secondHaar value] at hequal
  exact hequal

theorem padicSquareBranchFiberMeasure_normalized_isometry_of_targetHaar (form : QuadraticForm ℚ_[prime] space)
    (isometry : form.IsometryEquiv form) (point : space) (hpoint : form point ≠ 0)
    (sourceHaar : Measure (form.anisotropicOrthogonal point))
    (targetHaar : Measure (form.anisotropicOrthogonal (isometry point)))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [sourceHaar.IsAddHaarMeasure] [targetHaar.IsAddHaarMeasure]
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) :
    (form.anisotropicOrthogonalProductHaarScalar (isometry point)
      (by simpa only [isometry.map_app] using hpoint) targetHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime (isometry point)
        (by simpa only [isometry.map_app] using hpoint) targetHaar value =
    (isometry.vectorHaarModulus form vectorHaar : ℝ≥0∞)⁻¹ •
      Measure.map (isometry.valueFiberMap form value)
        ((form.anisotropicOrthogonalProductHaarScalar point hpoint sourceHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
          form.padicSquareBranchFiberMeasure prime point hpoint sourceHaar value) := by
  rw [form.padicSquareBranchFiberMeasure_normalized_eq prime (isometry point)
    (by simpa only [isometry.map_app] using hpoint) targetHaar
    (Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) sourceHaar)
    scalarHaar vectorHaar value]
  exact form.padicSquareBranchFiberMeasure_normalized_isometry prime isometry point hpoint sourceHaar scalarHaar vectorHaar value

end QuadraticMap
