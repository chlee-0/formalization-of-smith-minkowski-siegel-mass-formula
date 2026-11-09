import SMSFormula.PadicCoordinateVectorHaar
import SMSFormula.QuadraticPadicCayleyProductSourceHaar
import SMSFormula.SkewAdjointPadicElementaryCoordinateFormula
import SMSFormula.SkewAdjointPadicElementaryCoordinateMeasureScale

/-!
# Unit-cube Haar masses of linear images

For the unit-cube Haar measure on `κ → ℚ_p`:

* a matrix `M` with `det M ≠ 0` scales masses by `‖det M‖`;
* coordinate permutations preserve masses;
* the form-adapted elementary coordinate measure is carried to the unit-cube Haar by its
  coordinates, and the skew-adjoint coordinate measure is `‖e‖` times it, `e` the rational
  basis-comparison determinant.

Everything is an identification of existing normalizations; nothing is chosen.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace Padic

variable {p : ℕ} [Fact (Nat.Prime p)]

local instance linearImagePadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance linearImagePadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- A nonsingular matrix scales unit-cube Haar masses by the norm of its determinant. -/
theorem unitHaar_image_toLin' {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℚ_[p])
    (hM : M.det ≠ 0) {S : Set (κ → ℚ_[p])} (hS : MeasurableSet S) :
    unitHaar p κ (Matrix.toLin' M '' S) = (‖M.det‖₊ : ℝ≥0∞) * unitHaar p κ S := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  have himg : (Matrix.toLin' M : (κ → ℚ_[p]) → κ → ℚ_[p]) '' S = Matrix.toLin' M⁻¹ ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using hx
    · intro hy
      exact ⟨M⁻¹.mulVec y, hy, by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu]⟩
  have hdet : M⁻¹.det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hM
  rw [himg, ← Measure.map_apply (LinearMap.continuous_of_finiteDimensional _).measurable hS,
    map_vectorHaar_matrix p Measure.addHaar (unitHaar p κ) M⁻¹ hdet, Measure.smul_apply,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', nnnorm_inv, inv_inv, ENNReal.smul_def, smul_eq_mul]

/-- Coordinate permutations preserve unit-cube Haar masses of images. -/
theorem unitHaar_image_funCongrLeft {κ ι : Type*} [Fintype κ] [Fintype ι] (e : κ ≃ ι)
    (S : Set (ι → ℚ_[p])) :
    unitHaar p κ ((LinearEquiv.funCongrLeft ℚ_[p] ℚ_[p] e).toContinuousLinearEquiv '' S) = unitHaar p ι S := by
  set E := (LinearEquiv.funCongrLeft ℚ_[p] ℚ_[p] e).toContinuousLinearEquiv
  have h : (unitHaar p ι).map E (E '' S) = unitHaar p ι (E ⁻¹' (E '' S)) :=
    E.toHomeomorph.toMeasurableEquiv.map_apply _
  rw [← map_funCongrLeft_unitHaar e, h, Set.preimage_image_eq S E.injective]

end Padic

namespace Matrix

variable {n : ℕ} (p : ℕ) [Fact (Nat.Prime p)] (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
  (hdet : F.det ≠ 0)

local instance linearImageSkewMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance linearImageSkewBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance linearImagePadicMeasurableSpace' : MeasurableSpace ℚ_[p] := borel _
local instance linearImagePadicBorelSpace' : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The form-adapted elementary coordinate measure, read in its coordinates, is the unit-cube
Haar measure. -/
theorem map_skewAdjointFormElementaryPadicCoordinateMeasure :
    (skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet).map
        (skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet) =
      Padic.unitHaar p (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) := by
  haveI := skewAdjointFormElementaryPadicCoordinateMeasure_isAddHaarMeasure p F hF hdet
  apply Padic.eq_unitHaar_of_unitCube
  rw [Measure.map_apply (skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet).continuous.measurable
    isClosed_closedBall.measurableSet]
  have hpre : (skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet) ⁻¹' closedBall 0 1 =
      (skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet : Set _) := by
    ext x
    rw [Set.mem_preimage, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one,
      SetLike.mem_coe, mem_skewAdjointFormElementaryPadicCoordinateLattice_iff]
  rw [hpre]
  exact skewAdjointFormElementaryPadicCoordinateMeasure_lattice p F hF hdet

/-- The skew-adjoint coordinate mass of a set is `‖e‖` times the unit-cube Haar mass of its
form-adapted elementary coordinates. -/
theorem skewAdjointPadicCoordinateMeasure_eq_elementary
    (S : Set (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateMeasure F p S =
      (‖algebraMap ℚ ℚ_[p] (skewAdjointFixedFormElementaryDetScalar F hF hdet)‖₊ : ℝ≥0∞) *
        Padic.unitHaar p (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
          (skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet '' S) := by
  set c := ‖algebraMap ℚ ℚ_[p] (skewAdjointFixedFormElementaryDetScalar F hF hdet)‖₊ with hc
  have hc0 : c ≠ 0 := by
    rw [hc, nnnorm_ne_zero_iff, map_ne_zero]
    exact skewAdjointFixedFormElementaryDetScalar_ne_zero F hF hdet
  set E := skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet
  have h : (skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet).map E (E '' S) =
      skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet (E ⁻¹' (E '' S)) :=
    E.toHomeomorph.toMeasurableEquiv.map_apply _
  rw [← map_skewAdjointFormElementaryPadicCoordinateMeasure p F hF hdet, h, Set.preimage_image_eq S E.injective,
    skewAdjointFormElementaryPadicCoordinateMeasure_eq_smul p F hF hdet, Measure.smul_apply, ← hc]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ hc0,
    ENNReal.coe_one, one_mul]

end Matrix
