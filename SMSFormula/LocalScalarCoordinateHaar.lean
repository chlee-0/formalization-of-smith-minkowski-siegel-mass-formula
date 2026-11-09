import SMSFormula.QuadraticScalarOrthogonalHaarTransport
import SMSFormula.PadicCoordinateVectorHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace QuadraticMap

theorem det_scalarCoordinate {field index : Type*} [Field field] [Fintype index]
    (scalar : field) (hscalar : scalar ≠ 0) :
    LinearMap.det (LinearEquiv.smulOfNeZero field (index → field) scalar hscalar).toLinearMap =
      scalar ^ Fintype.card index := by
  have heq : (LinearEquiv.smulOfNeZero field (index → field) scalar hscalar).toLinearMap =
      scalar • (LinearMap.id : (index → field) →ₗ[field] (index → field)) := by
    ext vector coordinate
    rfl
  rw [heq, LinearMap.det_smul, LinearMap.det_id]
  simp

theorem map_realScalarCoordinateHaar {index : Type*} [Fintype index]
    (scalar : ℝ) (hscalar : scalar ≠ 0)
    (vectorHaar : Measure (index → ℝ)) [vectorHaar.IsAddHaarMeasure] :
    Measure.map (LinearEquiv.smulOfNeZero ℝ (index → ℝ) scalar hscalar).toContinuousLinearEquiv vectorHaar =
      (‖scalar‖₊ ^ Fintype.card index)⁻¹ • vectorHaar := by
  have hdet := det_scalarCoordinate (index := index) scalar hscalar
  have hmap := Measure.map_linearMap_addHaar_pi_eq_smul_addHaar
    (hdet.trans_ne (pow_ne_zero _ hscalar)) vectorHaar
  have hfactor : |(scalar ^ Fintype.card index)⁻¹| =
      (((‖scalar‖₊ ^ Fintype.card index)⁻¹ : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_inv, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, abs_inv, abs_pow]
  rw [hdet, hfactor, ENNReal.ofReal_coe_nnreal] at hmap
  exact hmap

theorem realScalarVectorHaarModulus {index : Type*} [Fintype index]
    (scalar : ℝ) (hscalar : scalar ≠ 0)
    (vectorHaar : Measure (index → ℝ)) [vectorHaar.IsAddHaarMeasure] :
    scalarVectorHaarModulus scalar hscalar vectorHaar = (‖scalar‖₊ ^ Fintype.card index)⁻¹ := by
  simp only [scalarVectorHaarModulus, map_realScalarCoordinateHaar scalar hscalar vectorHaar,
    Measure.addHaarScalarFactor_smul, Measure.addHaarScalarFactor_self, smul_eq_mul, mul_one]

section Padic

variable (prime : ℕ) [Fact prime.Prime]

local instance scalarCoordinateHaarMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance scalarCoordinateHaarBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

theorem map_padicScalarCoordinateHaar {index : Type*} [Fintype index] [DecidableEq index]
    (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure (index → ℚ_[prime]))
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] :
    Measure.map (LinearEquiv.smulOfNeZero ℚ_[prime] (index → ℚ_[prime]) scalar hscalar).toContinuousLinearEquiv vectorHaar =
      (‖scalar‖₊ ^ Fintype.card index)⁻¹ • vectorHaar := by
  let linear := (LinearEquiv.smulOfNeZero ℚ_[prime] (index → ℚ_[prime]) scalar hscalar).toLinearMap
  have hdet : (LinearMap.toMatrix' linear).det = scalar ^ Fintype.card index := by
    rw [LinearMap.det_toMatrix']
    exact det_scalarCoordinate scalar hscalar
  simpa only [hdet, nnnorm_pow, Matrix.toLin'_toMatrix'] using
    Padic.map_vectorHaar_matrix prime scalarHaar vectorHaar (LinearMap.toMatrix' linear)
      (hdet.trans_ne (pow_ne_zero _ hscalar))

theorem padicScalarVectorHaarModulus {index : Type*} [Fintype index] [DecidableEq index]
    (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure (index → ℚ_[prime]))
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] :
    scalarVectorHaarModulus scalar hscalar vectorHaar = (‖scalar‖₊ ^ Fintype.card index)⁻¹ := by
  simp only [scalarVectorHaarModulus, map_padicScalarCoordinateHaar prime scalar hscalar scalarHaar vectorHaar,
    Measure.addHaarScalarFactor_smul, Measure.addHaarScalarFactor_self, smul_eq_mul, mul_one]

end Padic

theorem scalar_normalized_coefficient (size : ℕ) (modulus : ℝ≥0) (hmodulus : modulus ≠ 0) :
    ((modulus : ℝ≥0∞) ^ 2)⁻¹ * (((modulus ^ size)⁻¹ : ℝ≥0) : ℝ≥0∞)⁻¹ =
      (modulus : ℝ≥0∞) ^ ((size : ℤ) - 2) := by
  have hzero : (modulus : ℝ≥0∞) ≠ 0 := by exact_mod_cast hmodulus
  rw [ENNReal.coe_inv (pow_ne_zero _ hmodulus), ENNReal.coe_pow, inv_inv,
    ENNReal.zpow_sub hzero ENNReal.coe_ne_top]
  simp only [zpow_natCast, zpow_ofNat]
  exact mul_comm _ _

end QuadraticMap
