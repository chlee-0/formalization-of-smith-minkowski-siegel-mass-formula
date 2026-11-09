import SMSFormula.LocalScalarCoordinateHaar
import SMSFormula.QuadraticPadicSquareBranchScalarMeasure
import SMSFormula.QuadraticPadicSquareBranchHaarIndependence

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicCoordinateBranchScalarMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicCoordinateBranchScalarBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {rank : ℕ}

theorem padicCoordinateBranch_normalized_scalar (form : QuadraticForm ℚ_[prime] (Fin rank → ℚ_[prime]))
    (point : Fin rank → ℚ_[prime]) (hpoint : form point ≠ 0) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (sourceHaar : Measure (form.anisotropicOrthogonal point))
    (targetHaar : Measure (form.anisotropicOrthogonal (scalar • point)))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure (Fin rank → ℚ_[prime]))
    [sourceHaar.IsAddHaarMeasure] [targetHaar.IsAddHaarMeasure]
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) :
    (form.anisotropicOrthogonalProductHaarScalar (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar) targetHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime (scalar • point)
        (form.quadratic_smul_ne_zero point hpoint scalar hscalar) targetHaar (scalar ^ 2 * value) =
    (‖scalar‖₊ : ℝ≥0∞) ^ ((rank : ℤ) - 2) •
      Measure.map (form.scalarValueFiberMap scalar value)
      ((form.anisotropicOrthogonalProductHaarScalar point hpoint sourceHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
        form.padicSquareBranchFiberMeasure prime point hpoint sourceHaar value) := by
  have hnorm : ‖scalar‖₊ ≠ 0 := by
    intro hzero
    have hreal := congrArg (fun number : ℝ≥0 ↦ (number : ℝ)) hzero
    exact (norm_pos_iff.mpr hscalar).ne' hreal
  have hJacobian : (‖scalar ^ 2‖₊ : ℝ≥0∞) = (‖scalar‖₊ : ℝ≥0∞) ^ 2 := by
    simp only [nnnorm_pow, ENNReal.coe_pow]
  rw [form.padicSquareBranchFiberMeasure_normalized_eq prime (scalar • point)
    (form.quadratic_smul_ne_zero point hpoint scalar hscalar) targetHaar
    (Measure.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) sourceHaar)
    scalarHaar vectorHaar (scalar ^ 2 * value),
    form.padicSquareBranchFiberMeasure_normalized_scalar prime point hpoint scalar hscalar
      sourceHaar scalarHaar vectorHaar value,
    padicScalarVectorHaarModulus prime scalar hscalar scalarHaar vectorHaar,
    Fintype.card_fin, hJacobian, scalar_normalized_coefficient rank ‖scalar‖₊ hnorm]

theorem padicCoordinateBranch_map_normalized_scalar (form : QuadraticForm ℚ_[prime] (Fin rank → ℚ_[prime]))
    (point : Fin rank → ℚ_[prime]) (hpoint : form point ≠ 0) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (sourceHaar : Measure (form.anisotropicOrthogonal point))
    (targetHaar : Measure (form.anisotropicOrthogonal (scalar • point)))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure (Fin rank → ℚ_[prime]))
    [sourceHaar.IsAddHaarMeasure] [targetHaar.IsAddHaarMeasure]
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) :
    Measure.map (form.scalarValueFiberMap scalar value)
      ((form.anisotropicOrthogonalProductHaarScalar point hpoint sourceHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
        form.padicSquareBranchFiberMeasure prime point hpoint sourceHaar value) =
    (‖scalar‖₊ : ℝ≥0∞) ^ (2 - (rank : ℤ)) • ((form.anisotropicOrthogonalProductHaarScalar (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar) targetHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime (scalar • point)
        (form.quadratic_smul_ne_zero point hpoint scalar hscalar) targetHaar (scalar ^ 2 * value)) := by
  have hnorm : (‖scalar‖₊ : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]; exact hscalar
  rw [form.padicCoordinateBranch_normalized_scalar prime point hpoint scalar hscalar
    sourceHaar targetHaar scalarHaar vectorHaar value, smul_smul,
    ← ENNReal.zpow_add hnorm ENNReal.coe_ne_top]
  simp only [sub_add_sub_cancel, sub_self, zpow_zero, one_smul]

end QuadraticMap
