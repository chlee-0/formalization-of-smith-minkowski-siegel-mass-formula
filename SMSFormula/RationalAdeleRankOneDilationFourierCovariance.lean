import SMSFormula.RationalAdeleRationalDilationHaar
import SMSFormula.RationalAdeleRankOneWeilGenerators

/-!
# Rational dilation covariance of the specialized rank-one Fourier operator

This file defines only the rational diagonal action needed by the explicit
rank-one Bruhat factor.  Multiplication by a nonzero rational diagonal is
measure preserving for the fixed full-adelic coordinate Haar, so the polar
Fourier operator satisfies the literal contragredient covariance

```text
W (D q Phi) = D (q^-1) (W Phi).
```

There is no modulus scalar: its real and finite parts have already cancelled
in the full-adelic Haar theorem.  No Weyl functional transformation, generic
Weil representation, or Fourier inversion theorem is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The concrete rational diagonal action on the actual adelic vector test
carrier.  It is defined for every rational parameter; covariance uses a
nonzero parameter. -/
def rationalAdeleRankOneDilationOperator
    (q : ℚ) (Phi : (Fin n → RationalAdele) → ℂ) :
    (Fin n → RationalAdele) → ℂ :=
  fun x ↦ Phi (fun i ↦ algebraMap ℚ RationalAdele q * x i)

@[simp]
theorem rationalAdeleRankOneDilationOperator_apply
    (q : ℚ) (Phi : (Fin n → RationalAdele) → ℂ)
    (x : Fin n → RationalAdele) :
    rationalAdeleRankOneDilationOperator q Phi x =
      Phi (fun i ↦ algebraMap ℚ RationalAdele q * x i) :=
  rfl

@[simp]
theorem rationalAdeleRankOneDilationOperator_one
    (Phi : (Fin n → RationalAdele) → ℂ) :
    rationalAdeleRankOneDilationOperator 1 Phi = Phi := by
  funext x
  simp

@[simp]
theorem rationalAdeleRankOneDilationOperator_zero_apply
    (q : ℚ) (Phi : (Fin n → RationalAdele) → ℂ) :
    rationalAdeleRankOneDilationOperator q Phi 0 = Phi 0 := by
  rw [rationalAdeleRankOneDilationOperator]
  apply congrArg Phi
  funext i
  simp

/-- The rational parameter `-1` is the literal central reflection of the
adelic vector variable. -/
@[simp]
theorem rationalAdeleRankOneDilationOperator_neg_one_apply
    (Phi : (Fin n → RationalAdele) → ℂ)
    (x : Fin n → RationalAdele) :
    rationalAdeleRankOneDilationOperator (-1) Phi x = Phi (-x) := by
  apply congrArg Phi
  funext i
  simp

/-- Rational diagonal operators compose multiplicatively. -/
theorem rationalAdeleRankOneDilationOperator_mul
    (q r : ℚ) (Phi : (Fin n → RationalAdele) → ℂ) :
    rationalAdeleRankOneDilationOperator q
        (rationalAdeleRankOneDilationOperator r Phi) =
      rationalAdeleRankOneDilationOperator (q * r) Phi := by
  funext x
  apply congrArg Phi
  funext i
  simp only [map_mul]
  ring

private theorem fullAdelicPolarMatrix_mulVec_rationalDilation
    (V : RationalQuadraticSpaceMatrix n) (q : ℚ)
    (y : Fin n → RationalAdele) :
    V.fullAdelicPolarMatrix.mulVec
        (fun i ↦ algebraMap ℚ RationalAdele q * y i) =
      fun i ↦ algebraMap ℚ RationalAdele q *
        V.fullAdelicPolarMatrix.mulVec y i := by
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (Matrix.mulVec_smul V.fullAdelicPolarMatrix
      (algebraMap ℚ RationalAdele q) y)

private theorem rationalDilation_mul_inversePolarDilation
    (q : ℚ) (hq : q ≠ 0)
    (x y : Fin n → RationalAdele) :
    (fun i ↦ algebraMap ℚ RationalAdele q * x i) *
        (fun i ↦ algebraMap ℚ RationalAdele q⁻¹ * y i) =
      x * y := by
  funext i
  simp only [Pi.mul_apply]
  have hunit : algebraMap ℚ RationalAdele q *
      algebraMap ℚ RationalAdele q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  calc
    algebraMap ℚ RationalAdele q * x i *
          (algebraMap ℚ RationalAdele q⁻¹ * y i) =
        (algebraMap ℚ RationalAdele q *
          algebraMap ℚ RationalAdele q⁻¹) * (x i * y i) := by ring
    _ = x i * y i := by rw [hunit, one_mul]

/-- The specialized polar Fourier operator is exactly contragredient under a
nonzero rational diagonal.  The full-adelic product formula has already made
the change of variables measure preserving, so no scalar occurs. -/
theorem rationalAdeleRankOneWeylOperator_dilation
    (V : RationalQuadraticSpaceMatrix n)
    (q : ℚ) (hq : q ≠ 0)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneWeylOperator
        (rationalAdeleRankOneDilationOperator q Phi) =
      rationalAdeleRankOneDilationOperator q⁻¹
        (V.rationalAdeleRankOneWeylOperator Phi) := by
  funext y
  simp only [rationalAdeleRankOneWeylOperator,
    rationalAdeleRankOneDilationOperator,
    Fourier.fourierIntegral_def,
    fullAdelicPolarMatrix_mulVec_rationalDilation]
  let dilate : (Fin n → RationalAdele) → (Fin n → RationalAdele) :=
    fun x i ↦ algebraMap ℚ RationalAdele q * x i
  have hdilate : MeasurePreserving dilate
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) := by
    simpa only [dilate] using
      (measurePreserving_rationalAdeleCoordinate_rationalDilation n q hq)
  have hemb : MeasurableEmbedding dilate := by
    simpa only [dilate, Pi.smul_apply, Units.smul_def,
      rationalUnitFullAdelicDiagonalHom] using
      (measurableEmbedding_const_smul
        (c := rationalUnitFullAdelicDiagonalHom (Units.mk0 q hq))
        (α := Fin n → RationalAdele))
  let targetIntegrand : (Fin n → RationalAdele) → ℂ :=
    fun x ↦ rationalAdeleCoordinateFourierChar n
        (-(x * (fun i ↦ algebraMap ℚ RationalAdele q⁻¹ *
          V.fullAdelicPolarMatrix.mulVec y i))) • Phi x
  calc
    (∫ x : Fin n → RationalAdele,
        rationalAdeleCoordinateFourierChar n
            (-(x * V.fullAdelicPolarMatrix.mulVec y)) •
          Phi (fun i ↦ algebraMap ℚ RationalAdele q * x i)
        ∂rationalAdeleCoordinateAddHaarMeasure n) =
        ∫ x, targetIntegrand (dilate x)
          ∂rationalAdeleCoordinateAddHaarMeasure n := by
      apply integral_congr_ae
      filter_upwards
      intro x
      change rationalAdeleCoordinateFourierChar n
            (-(x * V.fullAdelicPolarMatrix.mulVec y)) •
          Phi (dilate x) =
        rationalAdeleCoordinateFourierChar n
            (-((dilate x) *
              (fun i ↦ algebraMap ℚ RationalAdele q⁻¹ *
                V.fullAdelicPolarMatrix.mulVec y i))) •
          Phi (dilate x)
      rw [show
        (dilate x) *
            (fun i ↦ algebraMap ℚ RationalAdele q⁻¹ *
              V.fullAdelicPolarMatrix.mulVec y i) =
          x * V.fullAdelicPolarMatrix.mulVec y by
        exact rationalDilation_mul_inversePolarDilation q hq x
          (V.fullAdelicPolarMatrix.mulVec y)]
    _ = ∫ x, targetIntegrand x
          ∂rationalAdeleCoordinateAddHaarMeasure n :=
      hdilate.integral_comp hemb targetIntegrand

/-- At the cusp value zero, every nonzero rational diagonal factor is
invisible.  This is the exact scalar statement needed for the residual
diagonal in the nonzero Bruhat chart. -/
theorem rationalAdeleRankOneWeylOperator_dilation_zero
    (V : RationalQuadraticSpaceMatrix n)
    (q : ℚ) (hq : q ≠ 0)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneWeylOperator
        (rationalAdeleRankOneDilationOperator q Phi) 0 =
      V.rationalAdeleRankOneWeylOperator Phi 0 := by
  have h := congrFun (V.rationalAdeleRankOneWeylOperator_dilation q hq Phi) 0
  simpa using h

/-- The central reflection commutes with the concrete polar Fourier operator.
The negative Fourier kernel introduces no extra scalar or character. -/
theorem rationalAdeleRankOneWeylOperator_neg_one_dilation
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneWeylOperator
        (rationalAdeleRankOneDilationOperator (-1) Phi) =
      rationalAdeleRankOneDilationOperator (-1)
        (V.rationalAdeleRankOneWeylOperator Phi) := by
  simpa using V.rationalAdeleRankOneWeylOperator_dilation (-1) (by norm_num) Phi

end RationalQuadraticSpaceMatrix

end
