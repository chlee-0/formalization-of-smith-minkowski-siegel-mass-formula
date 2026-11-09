import SMSFormula.RationalAdeleGaussianWidthScaling

/-!
# The assembly: Poisson in Weyl form at the translated test's own carrier shape

Three closed facts chain into the statement the geometric covariance needs.

* The LHS reindexing: the theta of the Gaussian times `1_K` equals the theta at the transported
  width `b / N^2` and scaled carrier.
* The Weyl-form identity at that scaled data, whose carrier sits inside the integral vectors.
* The dual-side cancellation: the dual factor at the transported data equals the dual factor at the
  original data at the scaled frequency, with no leftover constant, so the same bijection reindexes
  the dual sum back.

The conclusion: for the polar Gaussian times the indicator of any subgroup carrier with
`N Zhat^n subset K subset N^-1 Zhat^n` -- exactly the translated test's shape -- the
rational-diagonal theta of the test equals the rational-diagonal theta of its Weyl transform, at the
original width and carrier.

Negative scope: this is the Poisson identity for such a test.  Turning it into the covariance
`Theta_Phi(g) = Theta_(W Phi)(g)` still needs the translated test to be recognized as one of these,
which is the carrier identification, and the existing intertwining; neither is invoked here.
-/

noncomputable section

open Complex PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

theorem tsum_polarGaussianTensor_wideSandwichCarrier_poisson_weyl
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0) [NeZero (N * N)]
    {K : Set (Fin n → RationalFiniteAdele)}
    (hadd : ∀ {x y : Fin n → RationalFiniteAdele}, x ∈ K → y ∈ K → x + y ∈ K)
    (hneg : ∀ {x : Fin n → RationalFiniteAdele}, x ∈ K → -x ∈ K)
    (hlow : ∀ u ∈ integralFiniteAdeleVectors n,
      (fun i ↦ (N : RationalFiniteAdele) * u i) ∈ K)
    (hhigh : ∀ y ∈ K, (fun i ↦ (N : RationalFiniteAdele) * y i) ∈
      integralFiniteAdeleVectors n) :
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
  have hNR : (0 : ℝ) < ((N : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hb' : 0 < (b / (((N : ℕ) : ℝ) : ℂ) ^ 2).re := by
    have hsq : ((((N : ℕ) : ℝ) : ℂ)) ^ 2 = ((((N : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hsq, Complex.div_ofReal_re]
    exact div_pos hb (by positivity)
  -- Step 1: reindex the left side to the transported width and scaled carrier.
  simp only [rationalAdeleVectorRealPart_rationalDiagonal,
    rationalAdeleVectorFinitePart_diagonal]
  rw [tsum_polarGaussian_indicator_scale L b hN (mem_scaledCarrier_iff hN)]
  -- Step 2: the Weyl-form identity at the scaled data.
  rw [show (∑' p : Fin n → ℚ,
        polarRealGaussian L (b / (((N : ℕ) : ℝ) : ℂ) ^ 2) (rationalRealVector n p) *
          (scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
            (rationalFiniteAdeleVectorDiagonal n p)) =
      ∑' y : Fin n → ℚ,
        L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (fun x ↦ polarRealGaussian L (b / (((N : ℕ) : ℝ) : ℂ) ^ 2)
              (rationalAdeleVectorRealPart n x) *
            (scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
              (rationalAdeleVectorFinitePart n x))
          (rationalAdeleVectorDiagonal n y) from by
    simpa only [rationalAdeleVectorRealPart_rationalDiagonal,
      rationalAdeleVectorFinitePart_diagonal] using
      tsum_polarGaussianTensor_subgroupIndicator_poisson_weyl L hb'
        (Nat.mul_ne_zero hN hN) (scaledCarrier_subset hhigh) (add_mem_scaledCarrier hadd)
        (neg_mem_scaledCarrier hneg) (nsmul_mem_scaledCarrier hlow)]
  -- Step 3: reindex the dual side back, the two scalings cancelling.
  rw [← (rationalScaleEquiv n hN).tsum_eq
    (fun z : Fin n → ℚ ↦
      L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (fun x ↦ polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
          K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
            (rationalAdeleVectorFinitePart n x))
        (rationalAdeleVectorDiagonal n z))]
  refine tsum_congr fun y ↦ ?_
  rw [rationalAdeleRankOneWeylOperator_realFiniteTensor,
    rationalAdeleRankOneWeylOperator_realFiniteTensor]
  have hrealArg : (L.rationalQuadraticSpaceMatrix.realPolarMatrix *ᵥ
        rationalAdeleVectorRealPart n
          (rationalAdeleVectorDiagonal n (rationalScaleEquiv n hN y))) =
      fun i ↦ (((N : ℕ) : ℝ)) * (L.rationalQuadraticSpaceMatrix.realPolarMatrix *ᵥ
        rationalAdeleVectorRealPart n (rationalAdeleVectorDiagonal n y)) i := by
    have hz : rationalAdeleVectorRealPart n
          (rationalAdeleVectorDiagonal n (rationalScaleEquiv n hN y)) =
        (((N : ℕ) : ℝ)) • rationalAdeleVectorRealPart n (rationalAdeleVectorDiagonal n y) := by
      funext i
      simp only [rationalAdeleVectorRealPart_rationalDiagonal, rationalRealVector, Pi.smul_apply,
        smul_eq_mul]
      show (((N : ℚ) * y i : ℚ) : ℝ) = _
      push_cast
      ring
    rw [hz, Matrix.mulVec_smul]
    funext i
    simp [smul_eq_mul]
  have hfinArg : (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix *ᵥ
        rationalAdeleVectorFinitePart n
          (rationalAdeleVectorDiagonal n (rationalScaleEquiv n hN y))) =
      fun i ↦ ((N : RationalFiniteAdele)) *
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix *ᵥ
          rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n y)) i := by
    have hz : rationalAdeleVectorFinitePart n
          (rationalAdeleVectorDiagonal n (rationalScaleEquiv n hN y)) =
        ((N : RationalFiniteAdele)) • rationalAdeleVectorFinitePart n
          (rationalAdeleVectorDiagonal n y) := by
      funext i
      simp only [rationalAdeleVectorFinitePart_diagonal, rationalFiniteAdeleVectorDiagonal,
        Pi.smul_apply, smul_eq_mul]
      show algebraMap ℚ RationalFiniteAdele ((N : ℚ) * y i) = _
      rw [map_mul, map_natCast]
    rw [hz, Matrix.mulVec_smul]
    funext i
    simp [smul_eq_mul]
  show Fourier.fourierIntegral (realCoordinateFourierChar n) volume
        (polarRealGaussian L (b / (((N : ℕ) : ℝ) : ℂ) ^ 2))
        (L.rationalQuadraticSpaceMatrix.realPolarMatrix *ᵥ
          rationalAdeleVectorRealPart n (rationalAdeleVectorDiagonal n y)) *
      Fourier.fourierIntegral (rationalFiniteAdeleCoordinateFourierChar n)
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)
        ((scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix *ᵥ
          rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n y)) =
      Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
          (L.rationalQuadraticSpaceMatrix.realPolarMatrix *ᵥ
            rationalAdeleVectorRealPart n
              (rationalAdeleVectorDiagonal n (rationalScaleEquiv n hN y))) *
        Fourier.fourierIntegral (rationalFiniteAdeleCoordinateFourierChar n)
          (rationalFiniteAdeleCoordinateAddHaarMeasure n)
          (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
          (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix *ᵥ
            rationalAdeleVectorFinitePart n
              (rationalAdeleVectorDiagonal n (rationalScaleEquiv n hN y)))
  rw [hrealArg, hfinArg, ← standardFiniteFourier_eq_fourierIntegral,
    ← standardFiniteFourier_eq_fourierIntegral,
    dualFactor_scaling_cancel L hb hN K
      (L.rationalQuadraticSpaceMatrix.realPolarMatrix *ᵥ
        rationalAdeleVectorRealPart n (rationalAdeleVectorDiagonal n y))
      (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix *ᵥ
        rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n y))]

end RationalQuadraticSpaceMatrix

end
