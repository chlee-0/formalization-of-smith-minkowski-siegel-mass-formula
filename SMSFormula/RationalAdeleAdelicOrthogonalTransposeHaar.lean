import SMSFormula.RationalAdeleRationalMatrixHaar
import SMSFormula.RationalSpecialOrthogonalTamagawa

/-!
# Adelic orthogonal Haar invariance is equivalent to its transpose form

The common-shell bridge and the geometric covariance need the statement that an adelic orthogonal
matrix preserves the fixed coordinate Haar.  This file reduces that statement to its transpose
form, using only the rational-matrix Haar law.

The form relation `g^T C g = C` for the polar matrix `C = 2F` rearranges to
`g^T = C g^-1 C^-1`, and `C` is the image of a rational matrix of nonzero determinant, so both
`C` and `C^-1` already preserve the coordinate Haar.  Hence the transpose action is the direct
action of `g^-1` conjugated by two Haar-preserving rational maps, and `g^T`, `g^-1` and `g` are
Haar preserving together or not at all.

So what is left to prove is exactly that the Haar scalar factor is symmetric under transposition
-- a Plancherel-type statement -- rather than the full determinant-modulus theorem for adelic
matrices: the conjugation already forces the factors of `g` and of `g^T` to be reciprocal.

Scope: nothing here proves that any adelic orthogonal matrix preserves the Haar.  No
disintegration is constructed, and no scalar factor is defined or evaluated.
-/

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Multiplication by a full-adelic matrix is continuous, hence measurable. -/
theorem continuous_fullAdelicMatrixMulVec (M : Matrix (Fin n) (Fin n) RationalAdele) :
    Continuous (fun x : Fin n → RationalAdele ↦ M.mulVec x) := by
  refine continuous_pi fun i ↦ ?_
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finset_sum _ fun j _ ↦ continuous_const.mul (continuous_apply j)

/-- A full-adelic matrix unit acts as a measurable equivalence of the coordinate carrier. -/
def fullAdelicMatrixUnitMeasurableEquiv (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    (Fin n → RationalAdele) ≃ᵐ (Fin n → RationalAdele) where
  toFun x := g.1.mulVec x
  invFun x := (g⁻¹).1.mulVec x
  left_inv x := by
    show (g⁻¹).1.mulVec (g.1.mulVec x) = x
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv x := by
    show g.1.mulVec ((g⁻¹).1.mulVec x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  measurable_toFun := (continuous_fullAdelicMatrixMulVec _).measurable
  measurable_invFun := (continuous_fullAdelicMatrixMulVec _).measurable

/-- The direct and inverse actions of a full-adelic matrix unit preserve the coordinate Haar
together. -/
theorem measurePreserving_fullAdelicMatrixUnit_inv_iff
    (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    MeasurePreserving (fun x : Fin n → RationalAdele ↦ (g⁻¹).1.mulVec x)
        (rationalAdeleCoordinateAddHaarMeasure n) (rationalAdeleCoordinateAddHaarMeasure n) ↔
      MeasurePreserving (fun x : Fin n → RationalAdele ↦ g.1.mulVec x)
        (rationalAdeleCoordinateAddHaarMeasure n) (rationalAdeleCoordinateAddHaarMeasure n) := by
  constructor
  · intro h
    exact h.symm (fullAdelicMatrixUnitMeasurableEquiv g).symm
  · intro h
    exact h.symm (fullAdelicMatrixUnitMeasurableEquiv g)

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

open PositiveDefiniteIntegralLattice

/-- The full-adelic polar matrix is preserved by the full-adelic orthogonal group. -/
theorem fullAdelicOrthogonal_polarMatrix_conj (V : RationalQuadraticSpaceMatrix n)
    (g : V.fullAdelicOrthogonalMatrixSubgroup) :
    g.1.1ᵀ * V.fullAdelicPolarMatrix * g.1.1 = V.fullAdelicPolarMatrix := by
  have hform : g.1.1ᵀ * V.fullAdelicFormMatrix * g.1.1 = V.fullAdelicFormMatrix :=
    (V.mem_fullAdelicOrthogonalMatrixSubgroup_iff g.1).mp g.2
  rw [V.fullAdelicPolarMatrix_eq_two_smul, Matrix.mul_smul, Matrix.smul_mul, hform]

/-- The image of the rational inverse polar matrix is a right inverse of the adelic polar
matrix. -/
theorem fullAdelicPolarMatrix_mul_inv_map (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicPolarMatrix * (V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele)) = 1 := by
  rw [fullAdelicPolarMatrix, ← Matrix.map_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr V.polarMatrix_det_ne_zero),
    Matrix.map_one] <;> simp

/-- The conjugation: the transpose of a full-adelic orthogonal matrix is the inverse conjugated
by the polar matrix, which is the image of a rational matrix of nonzero determinant. -/
theorem fullAdelicOrthogonal_transpose_eq (V : RationalQuadraticSpaceMatrix n)
    (g : V.fullAdelicOrthogonalMatrixSubgroup) :
    g.1.1ᵀ =
      V.fullAdelicPolarMatrix * (g.1⁻¹).1 *
        (V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele)) := by
  have hconj := V.fullAdelicOrthogonal_polarMatrix_conj g
  have hginv : g.1.1 * (g.1⁻¹).1 = 1 := Units.mul_inv g.1
  have hstep : g.1.1ᵀ * V.fullAdelicPolarMatrix = V.fullAdelicPolarMatrix * (g.1⁻¹).1 := by
    calc
      g.1.1ᵀ * V.fullAdelicPolarMatrix
          = (g.1.1ᵀ * V.fullAdelicPolarMatrix * g.1.1) * (g.1⁻¹).1 := by
            rw [Matrix.mul_assoc (g.1.1ᵀ * V.fullAdelicPolarMatrix), hginv, Matrix.mul_one]
      _ = V.fullAdelicPolarMatrix * (g.1⁻¹).1 := by rw [hconj]
  calc
    g.1.1ᵀ = g.1.1ᵀ * (V.fullAdelicPolarMatrix *
        (V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele))) := by
          rw [V.fullAdelicPolarMatrix_mul_inv_map, Matrix.mul_one]
    _ = (g.1.1ᵀ * V.fullAdelicPolarMatrix) *
        (V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele)) := by rw [Matrix.mul_assoc]
    _ = _ := by rw [hstep]

/-- The image of the rational inverse polar matrix is also a left inverse. -/
theorem fullAdelicPolarMatrix_inv_map_mul (V : RationalQuadraticSpaceMatrix n) :
    (V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele)) * V.fullAdelicPolarMatrix = 1 := by
  rw [fullAdelicPolarMatrix, ← Matrix.map_mul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr V.polarMatrix_det_ne_zero),
    Matrix.map_one] <;> simp

/-- The conjugation, other side: the inverse of a full-adelic orthogonal matrix is its transpose
conjugated the other way. -/
theorem fullAdelicOrthogonal_inv_eq (V : RationalQuadraticSpaceMatrix n)
    (g : V.fullAdelicOrthogonalMatrixSubgroup) :
    (g.1⁻¹).1 =
      (V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele)) * g.1.1ᵀ * V.fullAdelicPolarMatrix := by
  rw [V.fullAdelicOrthogonal_transpose_eq g]
  calc
    (g.1⁻¹).1 = 1 * (g.1⁻¹).1 * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
    _ = ((V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele)) * V.fullAdelicPolarMatrix) *
          (g.1⁻¹).1 *
          ((V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele)) * V.fullAdelicPolarMatrix) := by
        rw [V.fullAdelicPolarMatrix_inv_map_mul]
    _ = (V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele)) *
          (V.fullAdelicPolarMatrix * (g.1⁻¹).1 *
            (V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele))) * V.fullAdelicPolarMatrix := by
        simp only [Matrix.mul_assoc]

/-- The equivalence: the transpose action of a full-adelic orthogonal matrix preserves the fixed
coordinate Haar exactly when the direct action does.  Only the existing rational-matrix Haar law
is used. -/
theorem measurePreserving_fullAdelicOrthogonal_transpose_iff
    (V : RationalQuadraticSpaceMatrix n) (g : V.fullAdelicOrthogonalMatrixSubgroup) :
    MeasurePreserving (fun x : Fin n → RationalAdele ↦ g.1.1ᵀ.mulVec x)
        (rationalAdeleCoordinateAddHaarMeasure n) (rationalAdeleCoordinateAddHaarMeasure n) ↔
      MeasurePreserving (fun x : Fin n → RationalAdele ↦ g.1.1.mulVec x)
        (rationalAdeleCoordinateAddHaarMeasure n) (rationalAdeleCoordinateAddHaarMeasure n) := by
  have hC : MeasurePreserving (rationalMatrixFullAdelicMulVec V.polarMatrix)
      (rationalAdeleCoordinateAddHaarMeasure n) (rationalAdeleCoordinateAddHaarMeasure n) :=
    measurePreserving_rationalMatrixFullAdelicMulVec V.polarMatrix V.polarMatrix_det_ne_zero
  have hdetinv : (V.polarMatrix⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_ne_zero V.polarMatrix_det_ne_zero
  have hCinv : MeasurePreserving (rationalMatrixFullAdelicMulVec V.polarMatrix⁻¹)
      (rationalAdeleCoordinateAddHaarMeasure n) (rationalAdeleCoordinateAddHaarMeasure n) :=
    measurePreserving_rationalMatrixFullAdelicMulVec V.polarMatrix⁻¹ hdetinv
  have hfun : (fun x : Fin n → RationalAdele ↦ g.1.1ᵀ.mulVec x) =
      (rationalMatrixFullAdelicMulVec V.polarMatrix) ∘
        ((fun x : Fin n → RationalAdele ↦ (g.1⁻¹).1.mulVec x) ∘
          (rationalMatrixFullAdelicMulVec V.polarMatrix⁻¹)) := by
    funext x
    rw [V.fullAdelicOrthogonal_transpose_eq g]
    simp only [Function.comp_apply, rationalMatrixFullAdelicMulVec, fullAdelicPolarMatrix]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hback : (fun x : Fin n → RationalAdele ↦ (g.1⁻¹).1.mulVec x) =
      (rationalMatrixFullAdelicMulVec V.polarMatrix⁻¹) ∘
        ((fun x : Fin n → RationalAdele ↦ g.1.1ᵀ.mulVec x) ∘
          (rationalMatrixFullAdelicMulVec V.polarMatrix)) := by
    funext x
    rw [V.fullAdelicOrthogonal_inv_eq g]
    simp only [Function.comp_apply, rationalMatrixFullAdelicMulVec, fullAdelicPolarMatrix]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [← measurePreserving_fullAdelicMatrixUnit_inv_iff g.1]
  constructor
  · intro h
    rw [hback]
    exact hCinv.comp (h.comp hC)
  · intro h
    rw [hfun]
    exact hC.comp (h.comp hCinv)

end RationalQuadraticSpaceMatrix

end
