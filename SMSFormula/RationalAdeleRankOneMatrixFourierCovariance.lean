import SMSFormula.RationalAdeleRationalMatrixHaar
import SMSFormula.RationalAdeleRankOneWeilGenerators

/-!
# Rational matrix covariance of the rank-one Fourier operator

The fixed coordinate adelic Haar is invariant under every invertible rational
matrix.  This file uses that exact change of variables to prove the
contragredient covariance of the base coordinate Fourier integral.  For the
symmetric polar matrix `C = 2F`, the two matrix actions in the square of the
specialized Weyl operator cancel, leaving precisely the square of the base
coordinate Fourier transform.

This is only a covariance and reduction theorem.  It does not assert Fourier
inversion, a Fourier-square value, a Bruhat analytic relation, or a generic
Weil representation.
-/

noncomputable section

open Matrix MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private def rationalMatrixFullAdelicMeasurableEquiv
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : Matrix.det M ≠ 0) :
    (Fin n → RationalAdele) ≃ᵐ (Fin n → RationalAdele) where
  toFun := rationalMatrixFullAdelicMulVec M
  invFun := rationalMatrixFullAdelicMulVec M⁻¹
  left_inv x := by
    rw [rationalMatrixFullAdelicMulVec,
      rationalMatrixFullAdelicMulVec, Matrix.mulVec_mulVec,
      ← Matrix.map_mul, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),
      Matrix.map_one, Matrix.one_mulVec] <;> simp
  right_inv x := by
    rw [rationalMatrixFullAdelicMulVec,
      rationalMatrixFullAdelicMulVec, Matrix.mulVec_mulVec,
      ← Matrix.map_mul, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
      Matrix.map_one, Matrix.one_mulVec] <;> simp
  measurable_toFun :=
    (measurePreserving_rationalMatrixFullAdelicMulVec M hM).measurable
  measurable_invFun := by
    have hMinv : Matrix.det M⁻¹ ≠ 0 := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact inv_ne_zero hM
    exact (measurePreserving_rationalMatrixFullAdelicMulVec M⁻¹ hMinv).measurable

private theorem dotProduct_rationalMatrix_inverseTranspose
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : Matrix.det M ≠ 0)
    (x w : Fin n → RationalAdele) :
    dotProduct (rationalMatrixFullAdelicMulVec M x)
        (rationalMatrixFullAdelicMulVec (M⁻¹)ᵀ w) =
      dotProduct x w := by
  let A := M.map (algebraMap ℚ RationalAdele)
  let B := M⁻¹.map (algebraMap ℚ RationalAdele)
  have hBA : B * A = 1 := by
    dsimp only [A, B]
    rw [← Matrix.map_mul,
      Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),
      Matrix.map_one] <;> simp
  change dotProduct (A.mulVec x) ((Bᵀ).mulVec w) = dotProduct x w
  calc
    dotProduct (A.mulVec x) ((Bᵀ).mulVec w) =
        dotProduct (B.mulVec (A.mulVec x)) w := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = dotProduct ((B * A).mulVec x) w := by
      rw [Matrix.mulVec_mulVec]
    _ = dotProduct x w := by rw [hBA, Matrix.one_mulVec]

/-- The base coordinate Fourier integral is contragredient under every
invertible rational matrix.  The global product formula has already cancelled
all real and finite determinant moduli, so no scalar occurs. -/
theorem rationalAdeleCoordinate_fourierIntegral_rationalMatrix
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : Matrix.det M ≠ 0)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
        (rationalAdeleCoordinateAddHaarMeasure n)
        (fun x ↦ Phi (rationalMatrixFullAdelicMulVec M x)) =
      fun w ↦
        Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
          (rationalAdeleCoordinateAddHaarMeasure n) Phi
          (rationalMatrixFullAdelicMulVec (M⁻¹)ᵀ w) := by
  funext w
  simp only [Fourier.fourierIntegral_def]
  let e := rationalMatrixFullAdelicMeasurableEquiv M hM
  let targetIntegrand : (Fin n → RationalAdele) → ℂ :=
    fun x ↦ rationalAdeleCoordinateFourierChar n
        (-(x * rationalMatrixFullAdelicMulVec (M⁻¹)ᵀ w)) • Phi x
  have he : MeasurePreserving e
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) := by
    simpa only [e, rationalMatrixFullAdelicMeasurableEquiv] using
      measurePreserving_rationalMatrixFullAdelicMulVec M hM
  calc
    (∫ x : Fin n → RationalAdele,
        rationalAdeleCoordinateFourierChar n (-(x * w)) •
          Phi (rationalMatrixFullAdelicMulVec M x)
        ∂rationalAdeleCoordinateAddHaarMeasure n) =
        ∫ x, targetIntegrand (e x)
          ∂rationalAdeleCoordinateAddHaarMeasure n := by
      apply integral_congr_ae
      filter_upwards
      intro x
      change rationalAdeleCoordinateFourierChar n (-(x * w)) •
          Phi (rationalMatrixFullAdelicMulVec M x) =
        rationalAdeleCoordinateFourierChar n
            (-((rationalMatrixFullAdelicMulVec M x) *
              rationalMatrixFullAdelicMulVec (M⁻¹)ᵀ w)) •
          Phi (rationalMatrixFullAdelicMulVec M x)
      congr 1
      rw [show -(x * w) = (-x) * w by ext i; simp,
        RationalQuadraticSpaceMatrix.rationalAdeleCoordinateFourierChar_mul_eq_dotProduct,
        show -((rationalMatrixFullAdelicMulVec M x) *
            rationalMatrixFullAdelicMulVec (M⁻¹)ᵀ w) =
          (-(rationalMatrixFullAdelicMulVec M x)) *
            rationalMatrixFullAdelicMulVec (M⁻¹)ᵀ w by ext i; simp,
        RationalQuadraticSpaceMatrix.rationalAdeleCoordinateFourierChar_mul_eq_dotProduct]
      rw [neg_dotProduct, neg_dotProduct]
      rw [dotProduct_rationalMatrix_inverseTranspose M hM x w]
    _ = ∫ x, targetIntegrand x
          ∂rationalAdeleCoordinateAddHaarMeasure n :=
      he.integral_comp' targetIntegrand

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Squaring the specialized polar Weyl operator cancels the two occurrences
of the symmetric rational polar matrix.  What remains is exactly the square
of the base coordinate Fourier transform; no inversion value is asserted. -/
theorem rationalAdeleRankOneWeylOperator_iterate_two_eq_coordinateFourierSquare
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneWeylOperator
        (V.rationalAdeleRankOneWeylOperator Phi) =
      Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
        (rationalAdeleCoordinateAddHaarMeasure n)
        (Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
          (rationalAdeleCoordinateAddHaarMeasure n) Phi) := by
  let C := V.polarMatrix
  let F0 : ((Fin n → RationalAdele) → ℂ) →
      (Fin n → RationalAdele) → ℂ :=
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
      (rationalAdeleCoordinateAddHaarMeasure n)
  have hcov := rationalAdeleCoordinate_fourierIntegral_rationalMatrix C
    V.polarMatrix_det_ne_zero (F0 Phi)
  funext y
  have hfreq : rationalMatrixFullAdelicMulVec (C⁻¹)ᵀ
        (rationalMatrixFullAdelicMulVec C y) = y := by
    have hsymm : Cᵀ = C := V.polarMatrix_isSymm.eq
    rw [show (C⁻¹)ᵀ = C⁻¹ by
      rw [Matrix.transpose_nonsing_inv, hsymm]]
    rw [rationalMatrixFullAdelicMulVec,
      rationalMatrixFullAdelicMulVec, Matrix.mulVec_mulVec,
      ← Matrix.map_mul,
      Matrix.nonsing_inv_mul C
        (isUnit_iff_ne_zero.mpr V.polarMatrix_det_ne_zero),
      Matrix.map_one, Matrix.one_mulVec] <;> simp
  have hpoint := congrFun hcov (rationalMatrixFullAdelicMulVec C y)
  change F0 (fun x ↦ F0 Phi (rationalMatrixFullAdelicMulVec C x))
      (rationalMatrixFullAdelicMulVec C y) = F0 (F0 Phi) y
  rw [hfreq] at hpoint
  exact hpoint

end RationalQuadraticSpaceMatrix

end
