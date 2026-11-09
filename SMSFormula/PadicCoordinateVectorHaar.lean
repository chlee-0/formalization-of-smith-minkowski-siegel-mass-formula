import SMSFormula.PadicScalarAdditiveHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section

open MeasureTheory Matrix Set
open scoped ENNReal NNReal

namespace Padic

variable (prime : ℕ) [Fact prime.Prime]

local instance coordinateVectorHaarMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance coordinateVectorHaarBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {index : Type*} [Fintype index] [DecidableEq index]
  (haar : Measure ℚ_[prime]) [haar.IsAddHaarMeasure]

theorem map_piHaar_transvection (shear : TransvectionStruct index ℚ_[prime]) :
    Measure.map (toLin' shear.toMatrix) (Measure.pi fun _ : index ↦ haar) =
      Measure.pi (fun _ : index ↦ haar) := by
  have hmeasurable : Measurable (toLin' shear.toMatrix) :=
    (toLin' shear.toMatrix).continuous_of_finiteDimensional.measurable
  apply Measure.ext_of_lintegral
  intro weight hweight
  rw [lintegral_map hweight hmeasurable]
  apply lintegral_eq_of_lmarginal_eq {shear.i}
    (hweight.comp hmeasurable) hweight
  simp_rw [lmarginal_singleton]
  ext vector
  cases shear with | mk row column hdistinct coefficient =>
  simp [transvection, single_mulVec, hdistinct.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun scalar ↦ weight (Function.update vector row scalar)]

theorem smul_map_piHaar_diagonal (diagonalValues : index → ℚ_[prime])
    (hdet : det (diagonal diagonalValues) ≠ 0) :
    ‖det (diagonal diagonalValues)‖₊ •
      Measure.map (toLin' (diagonal diagonalValues)) (Measure.pi fun _ : index ↦ haar) =
    Measure.pi (fun _ : index ↦ haar) := by
  refine (Measure.pi_eq fun sets hsets ↦ ?_).symm
  simp only [Measure.coe_smul, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [Measure.map_apply (toLin' (diagonal diagonalValues)).continuous_of_finiteDimensional.measurable
    (MeasurableSet.univ_pi hsets)]
  have hpreimage : (toLin' (diagonal diagonalValues) ⁻¹' univ.pi sets) =
      univ.pi (fun coordinate ↦ (diagonalValues coordinate * ·) ⁻¹' sets coordinate) := by
    ext vector
    simp only [LinearMap.coe_proj, smul_eq_mul, LinearMap.smul_apply, mem_univ_pi,
      mem_preimage, LinearMap.pi_apply, diagonal_toLin']
  have hcoordinate (coordinate : index) :
      (‖diagonalValues coordinate‖₊ : ℝ≥0∞) *
        haar ((diagonalValues coordinate * ·) ⁻¹' sets coordinate) = haar (sets coordinate) := by
    have hnonzero : diagonalValues coordinate ≠ 0 := by
      rw [det_diagonal] at hdet
      exact Finset.prod_ne_zero_iff.mp hdet coordinate (Finset.mem_univ coordinate)
    rw [← Measure.map_apply (f := fun scalar : ℚ_[prime] ↦ diagonalValues coordinate * scalar)
      (continuous_const.mul continuous_id).measurable (hsets coordinate)]
    have hmap := map_additiveHaar_mul_unit prime haar (Units.mk0 (diagonalValues coordinate) hnonzero)
    dsimp only [Units.val_mk0] at hmap
    rw [hmap, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
      mul_inv_cancel₀ (nnnorm_ne_zero_iff.mpr hnonzero), ENNReal.coe_one, one_mul]
  rw [hpreimage, Measure.pi_pi, det_diagonal, nnnorm_prod, ENNReal.coe_finset_prod,
    ← Finset.prod_mul_distrib]
  simp only [hcoordinate]

theorem map_piHaar_matrix (matrix : Matrix index index ℚ_[prime]) (hdet : matrix.det ≠ 0) :
    Measure.map (toLin' matrix) (Measure.pi fun _ : index ↦ haar) =
      ‖matrix.det‖₊⁻¹ • Measure.pi (fun _ : index ↦ haar) := by
  apply diagonal_transvection_induction_of_det_ne_zero _ matrix hdet
  · intro diagonalValues hdiagonal
    conv_rhs => rw [← smul_map_piHaar_diagonal prime haar diagonalValues hdiagonal]
    rw [smul_smul]
    rw [inv_mul_cancel₀ (nnnorm_ne_zero_iff.mpr hdiagonal), one_smul]
  · intro shear
    simp only [TransvectionStruct.det, nnnorm_one, inv_one, one_smul,
      map_piHaar_transvection prime haar]
  · intro first second _ _ hfirst hsecond
    rw [toLin'_mul, det_mul, LinearMap.coe_comp,
      ← Measure.map_map (toLin' first).continuous_of_finiteDimensional.measurable
        (toLin' second).continuous_of_finiteDimensional.measurable,
      hsecond, Measure.map_smul, hfirst, smul_smul, nnnorm_mul, _root_.mul_inv_rev]

include haar in
theorem map_vectorHaar_matrix (vectorHaar : Measure (index → ℚ_[prime]))
    [vectorHaar.IsAddHaarMeasure] (matrix : Matrix index index ℚ_[prime]) (hdet : matrix.det ≠ 0) :
    Measure.map (toLin' matrix) vectorHaar = ‖matrix.det‖₊⁻¹ • vectorHaar := by
  have hscale := Measure.isAddLeftInvariant_eq_smul vectorHaar (Measure.pi fun _ : index ↦ haar)
  rw [hscale, Measure.map_smul, map_piHaar_matrix prime haar matrix hdet, smul_comm]

include haar in
theorem map_vectorHaar_of_det_eq_one (vectorHaar : Measure (index → ℚ_[prime]))
    [vectorHaar.IsAddHaarMeasure]
    (linear : (index → ℚ_[prime]) ≃L[ℚ_[prime]] (index → ℚ_[prime]))
    (hdet : LinearMap.det linear.toLinearMap = 1) :
    Measure.map linear vectorHaar = vectorHaar := by
  have hmatrix : (LinearMap.toMatrix' linear.toLinearMap).det = 1 := by
    simpa only [LinearMap.det_toMatrix'] using hdet
  simpa only [hmatrix, nnnorm_one, inv_one, one_smul, toLin'_toMatrix'] using
    map_vectorHaar_matrix prime haar vectorHaar (LinearMap.toMatrix' linear.toLinearMap)
      (hmatrix.trans_ne one_ne_zero)

end Padic
