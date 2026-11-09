import SMSFormula.RationalAdeleCompactOpenPoissonFourierForm
import SMSFormula.RationalAdeleRealFiniteTensorOperators
import SMSFormula.RationalCliffordGeneralSpinAllRationalThetaQuotient

/-!
# The compact-open Poisson identity in the repository's own Weyl-operator form

The Fourier form has the dual side as a product of the real and finite coordinate transforms.  The
repository's polar Weyl operator is precisely that product precomposed with the polar matrix, by
the existing tensor factorization.  Since the polar matrix is rational with nonzero determinant,
multiplication by it is a bijection of the rational index set, so the dual sum may be reindexed
along it with no factor at all.

The result is the statement the geometric covariance needs, in the operator the repository already
uses: for the polar Gaussian times a subgroup-carrier indicator with `N Zhat^n subset K subset
Zhat^n`, the rational-diagonal theta of the test equals the rational-diagonal theta of its Weyl
transform.

Negative scope: this is at a carrier inside the integral vectors.  For the translated test the
width and the scaled carrier must still be pushed back, which is where the modulus factor lives;
that step is not done here, and no covariance of either functional is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Multiplication by the polar matrix is a bijection of the rational coordinate space, because
that matrix is rational with nonzero determinant. -/
def polarMulVecEquiv (V : RationalQuadraticSpaceMatrix n) : (Fin n → ℚ) ≃ (Fin n → ℚ) where
  toFun y := V.polarMatrix.mulVec y
  invFun p := V.polarMatrix⁻¹.mulVec p
  left_inv y := by
    show V.polarMatrix⁻¹ *ᵥ (V.polarMatrix *ᵥ y) = y
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr V.polarMatrix_det_ne_zero),
      Matrix.one_mulVec]
  right_inv p := by
    show V.polarMatrix *ᵥ (V.polarMatrix⁻¹ *ᵥ p) = p
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr V.polarMatrix_det_ne_zero),
      Matrix.one_mulVec]

/-- Poisson in the repository's own Weyl form, for a carrier inside the integral vectors. -/
theorem tsum_polarGaussianTensor_subgroupIndicator_poisson_weyl
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0) [NeZero N]
    {K : Set (Fin n → RationalFiniteAdele)}
    (hK : K ⊆ integralFiniteAdeleVectors n)
    (hadd : ∀ {x y : Fin n → RationalFiniteAdele}, x ∈ K → y ∈ K → x + y ∈ K)
    (hneg : ∀ {x : Fin n → RationalFiniteAdele}, x ∈ K → -x ∈ K)
    (hNK : ∀ u ∈ integralFiniteAdeleVectors n, (N • u : Fin n → RationalFiniteAdele) ∈ K) :
    (∑' q : Fin n → ℚ,
        polarRealGaussian L b
            (rationalAdeleVectorRealPart n (rationalAdeleVectorDiagonal n q)) *
          K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
            (rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n q))) =
      ∑' y : Fin n → ℚ,
        L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (fun x ↦ polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
            K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
              (rationalAdeleVectorFinitePart n x))
          (rationalAdeleVectorDiagonal n y) := by
  simp only [rationalAdeleVectorRealPart_rationalDiagonal,
    rationalAdeleVectorFinitePart_diagonal]
  rw [tsum_polarGaussian_subgroupIndicator_poisson_fourier L hb hN hK hadd hneg hNK]
  rw [← (L.rationalQuadraticSpaceMatrix.polarMulVecEquiv).tsum_eq
    (fun p : Fin n → ℚ ↦
      Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
          (rationalRealVector n p) *
        standardFiniteFourier (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
          (rationalFiniteAdeleVectorDiagonal n p))]
  refine tsum_congr fun y ↦ ?_
  rw [rationalAdeleRankOneWeylOperator_realFiniteTensor]
  have hdiag : rationalAdeleVectorDiagonal n
      (L.rationalQuadraticSpaceMatrix.polarMulVecEquiv y) =
      L.rationalQuadraticSpaceMatrix.fullAdelicPolarMatrix.mulVec
        (rationalAdeleVectorDiagonal n y) :=
    (rationalAdeleVectorDiagonal_mulVec L.rationalQuadraticSpaceMatrix.polarMatrix y).symm
  have hreal : rationalRealVector n (L.rationalQuadraticSpaceMatrix.polarMulVecEquiv y) =
      L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec
        (rationalAdeleVectorRealPart n (rationalAdeleVectorDiagonal n y)) := by
    rw [← rationalAdeleVectorRealPart_rationalDiagonal, hdiag,
      rationalAdeleVectorRealPart_fullAdelicPolarMatrix_mulVec]
  have hfin : rationalFiniteAdeleVectorDiagonal n
      (L.rationalQuadraticSpaceMatrix.polarMulVecEquiv y) =
      L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
        (rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n y)) := by
    rw [← rationalAdeleVectorFinitePart_diagonal, hdiag,
      rationalAdeleVectorFinitePart_fullAdelicPolarMatrix_mulVec]
  rw [hreal, hfin, standardFiniteFourier_eq_fourierIntegral]

end RationalQuadraticSpaceMatrix

end
