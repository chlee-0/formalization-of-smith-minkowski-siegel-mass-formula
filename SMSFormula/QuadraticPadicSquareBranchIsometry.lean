import SMSFormula.QuadraticPadicSquareBranchFiberMeasure
import SMSFormula.QuadraticIsometryOrthogonalHaarTransport

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicSquareBranchIsometryMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicSquareBranchIsometryBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space]

theorem padicSquareBranchValueKernel_isometry (form : QuadraticForm ℚ_[prime] space)
    (isometry : form.IsometryEquiv form) (point : space) (weight : space → ℝ≥0∞)
    (transverse : form.anisotropicOrthogonal point) (value : ℚ_[prime]) :
    form.padicSquareBranchValueKernel prime (isometry point) weight
      (isometry.anisotropicOrthogonalContinuousLinearEquiv form point transverse, value) =
    form.padicSquareBranchValueKernel prime point (fun vector ↦ weight (isometry vector)) (transverse, value) := by
  have hquadratic : form.orthogonalRestriction (isometry point)
      (isometry.anisotropicOrthogonalContinuousLinearEquiv form point transverse) =
      form.orthogonalRestriction point transverse := isometry.map_app transverse
  classical
  simp only [padicSquareBranchValueKernel, Set.indicator, Set.mem_preimage, hquadratic, isometry.map_app]
  split_ifs <;> simp only [IsometryEquiv.coe_anisotropicOrthogonalContinuousLinearEquiv, map_add, map_smul]

variable [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space]

theorem padicSquareBranchValueDensity_isometry (form : QuadraticForm ℚ_[prime] space)
    (isometry : form.IsometryEquiv form) (point : space)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point))
    (weight : space → ℝ≥0∞) (hweight : Measurable weight) (value : ℚ_[prime]) :
    form.padicSquareBranchValueDensity prime (isometry point)
      (Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseMeasure) weight value =
    form.padicSquareBranchValueDensity prime point transverseMeasure (fun vector ↦ weight (isometry vector)) value := by
  rw [padicSquareBranchValueDensity, lintegral_map (f := fun transverse ↦
    form.padicSquareBranchValueKernel prime (isometry point) weight (transverse, value))
    ((form.measurable_padicSquareBranchValueKernel prime (isometry point) weight hweight).comp
      (measurable_id.prodMk measurable_const))
    (isometry.anisotropicOrthogonalContinuousLinearEquiv form point).continuous.measurable]
  apply lintegral_congr
  intro transverse
  exact form.padicSquareBranchValueKernel_isometry prime isometry point weight transverse value

theorem padicSquareBranchFiberMeasure_isometry (form : QuadraticForm ℚ_[prime] space)
    (isometry : form.IsometryEquiv form) (point : space) (hpoint : form point ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point)) (value : ℚ_[prime]) :
    form.padicSquareBranchFiberMeasure prime (isometry point)
      (by simpa only [isometry.map_app] using hpoint)
      (Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseMeasure) value =
    Measure.map (isometry.valueFiberMap form value)
      (form.padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value) := by
  have hform : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  apply (MeasurableEmbedding.subtype_coe (isClosed_eq hform continuous_const).measurableSet).map_injective
  apply Measure.ext_of_lintegral
  intro weight hweight
  erw [lintegral_map hweight measurable_subtype_coe,
    lintegral_map hweight measurable_subtype_coe,
    lintegral_map (hweight.comp measurable_subtype_coe)
      (isometry.continuous_valueFiberMap form value).measurable]
  change (∫⁻ vector : {vector : space // form vector = value}, weight vector.val ∂_) =
    ∫⁻ vector : {vector : space // form vector = value}, weight (isometry vector.val) ∂_
  erw [form.lintegral_padicSquareBranchFiberMeasure_restrict_weight prime (isometry point)
    (by simpa only [isometry.map_app] using hpoint) _ value weight hweight,
    form.lintegral_padicSquareBranchFiberMeasure_restrict_weight prime point hpoint transverseMeasure value
      (fun vector ↦ weight (isometry vector))
      (hweight.comp isometry.toLinearEquiv.toContinuousLinearEquiv.continuous.measurable)]
  exact form.padicSquareBranchValueDensity_isometry prime isometry point transverseMeasure weight hweight value

variable [LocallyCompactSpace space]

theorem padicSquareBranch_normalized_density_isometry (form : QuadraticForm ℚ_[prime] space)
    (isometry : form.IsometryEquiv form) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point)) (scalarHaar : Measure ℚ_[prime])
    (vectorHaar : Measure space) [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure]
    [vectorHaar.IsAddHaarMeasure] (weight : space → ℝ≥0∞) (hweight : Measurable weight) (value : ℚ_[prime]) :
    form.padicSquareBranchValueDensity prime (isometry point)
      (Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseHaar) weight value /
      (form.anisotropicOrthogonalProductHaarScalar (isometry point)
        (by simpa only [isometry.map_app] using hpoint)
        (Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseHaar)
        scalarHaar vectorHaar : ℝ≥0∞) =
    (isometry.vectorHaarModulus form vectorHaar : ℝ≥0∞)⁻¹ *
      (form.padicSquareBranchValueDensity prime point transverseHaar (fun vector ↦ weight (isometry vector)) value /
        (form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar : ℝ≥0∞)) := by
  letI : LocallyCompactSpace (form.anisotropicOrthogonal point) :=
    (form.anisotropicOrthogonal point).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  rw [form.padicSquareBranchValueDensity_isometry prime isometry point transverseHaar weight hweight value,
    isometry.anisotropicOrthogonalProductHaarScalar_transport form point hpoint transverseHaar scalarHaar vectorHaar]
  simp only [ENNReal.coe_mul, div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)]
  ac_rfl

theorem padicSquareBranchFiberMeasure_normalized_isometry (form : QuadraticForm ℚ_[prime] space)
    (isometry : form.IsometryEquiv form) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point)) (scalarHaar : Measure ℚ_[prime])
    (vectorHaar : Measure space) [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure]
    [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) :
    (form.anisotropicOrthogonalProductHaarScalar (isometry point)
      (by simpa only [isometry.map_app] using hpoint)
      (Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseHaar)
      scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime (isometry point)
        (by simpa only [isometry.map_app] using hpoint)
        (Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseHaar) value =
    (isometry.vectorHaarModulus form vectorHaar : ℝ≥0∞)⁻¹ •
      Measure.map (isometry.valueFiberMap form value)
        ((form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
          form.padicSquareBranchFiberMeasure prime point hpoint transverseHaar value) := by
  letI : LocallyCompactSpace (form.anisotropicOrthogonal point) :=
    (form.anisotropicOrthogonal point).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  rw [form.padicSquareBranchFiberMeasure_isometry prime isometry point hpoint transverseHaar value,
    isometry.anisotropicOrthogonalProductHaarScalar_transport form point hpoint transverseHaar scalarHaar vectorHaar,
    Measure.map_smul, smul_smul, ENNReal.coe_mul,
    ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), mul_comm]

end QuadraticMap
