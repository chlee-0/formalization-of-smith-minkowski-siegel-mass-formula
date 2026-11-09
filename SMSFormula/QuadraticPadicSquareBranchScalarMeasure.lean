import SMSFormula.QuadraticPadicSquareBranchScalar
import SMSFormula.QuadraticScalarOrthogonalHaarTransport

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicSquareBranchScalarMeasureMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicSquareBranchScalarMeasureBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]
  [SecondCountableTopology space]

set_option backward.isDefEq.respectTransparency false in
theorem padicSquareBranchFiberMeasure_scalar (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point)) (value : ℚ_[prime]) :
    form.padicSquareBranchFiberMeasure prime (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar)
      (Measure.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) transverseMeasure)
      (scalar ^ 2 * value) =
    (‖scalar ^ 2‖₊ : ℝ≥0∞)⁻¹ • Measure.map (form.scalarValueFiberMap scalar value)
      (form.padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value) := by
  have hform : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  apply (MeasurableEmbedding.subtype_coe (isClosed_eq hform continuous_const).measurableSet).map_injective
  rw [Measure.map_smul]
  apply Measure.ext_of_lintegral
  intro weight hweight
  erw [lintegral_map hweight measurable_subtype_coe, lintegral_smul_measure,
    lintegral_map hweight measurable_subtype_coe,
    lintegral_map (hweight.comp measurable_subtype_coe)
      (form.continuous_scalarValueFiberMap scalar value).measurable]
  change (∫⁻ vector : {vector : space // form vector = scalar ^ 2 * value}, weight vector.val ∂_) =
    (‖scalar ^ 2‖₊ : ℝ≥0∞)⁻¹ *
      ∫⁻ vector : {vector : space // form vector = value}, weight (scalar • vector.val) ∂_
  erw [form.lintegral_padicSquareBranchFiberMeasure_restrict_weight prime (scalar • point)
    (form.quadratic_smul_ne_zero point hpoint scalar hscalar) _ (scalar ^ 2 * value) weight hweight,
    form.lintegral_padicSquareBranchFiberMeasure_restrict_weight prime point hpoint transverseMeasure value
      (fun vector ↦ weight (scalar • vector))
      (hweight.comp (continuous_const.smul continuous_id).measurable)]
  exact form.padicSquareBranchValueDensity_scalar prime point scalar hscalar transverseMeasure weight hweight value

theorem padicSquareBranchFiberMeasure_normalized_scalar [LocallyCompactSpace space]
    (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point)) (scalarHaar : Measure ℚ_[prime])
    (vectorHaar : Measure space) [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure]
    [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) :
    (form.anisotropicOrthogonalProductHaarScalar (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar)
      (Measure.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) transverseHaar)
      scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime (scalar • point)
        (form.quadratic_smul_ne_zero point hpoint scalar hscalar)
        (Measure.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) transverseHaar)
        (scalar ^ 2 * value) =
    ((‖scalar ^ 2‖₊ : ℝ≥0∞)⁻¹ * (scalarVectorHaarModulus scalar hscalar vectorHaar : ℝ≥0∞)⁻¹) •
      Measure.map (form.scalarValueFiberMap scalar value)
        ((form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
          form.padicSquareBranchFiberMeasure prime point hpoint transverseHaar value) := by
  letI : LocallyCompactSpace (form.anisotropicOrthogonal point) :=
    (form.anisotropicOrthogonal point).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  rw [form.padicSquareBranchFiberMeasure_scalar prime point hpoint scalar hscalar transverseHaar value,
    form.anisotropicOrthogonalProductHaarScalar_scalar point hpoint scalar hscalar transverseHaar scalarHaar vectorHaar,
    Measure.map_smul, smul_smul, smul_smul, ENNReal.coe_mul,
    ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)]
  congr 1
  ac_rfl

end QuadraticMap
