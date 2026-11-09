import SMSFormula.RationalAdeleRankOneMatrixFourierCovariance
import SMSFormula.RationalAdeleRankOneDilationFourierCovariance
import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier square on the concrete polar Gaussian--lattice test

This file proves Fourier inversion only for the concrete real Gaussian and
finite integral-lattice indicator used by the specialized rational rank-one
argument.  The negative Fourier kernel leaves the reflection visible.  No
generic adelic Fourier inversion or Weil-representation interface is added.
-/

noncomputable section

open Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The coordinate real Fourier integral used here is the usual
finite-dimensional real Fourier transform after the canonical `L²` identification. -/
private theorem realCoordinate_fourierIntegral_eq_euclideanFourier
    (f : (Fin n → ℝ) → ℂ) (w : Fin n → ℝ) :
    Fourier.fourierIntegral (realCoordinateFourierChar n)
        (volume : Measure (Fin n → ℝ)) f w =
      𝓕 (fun x : EuclideanSpace ℝ (Fin n) ↦ f (WithLp.ofLp x))
        (WithLp.toLp 2 w) := by
  rw [Fourier.fourierIntegral_def, Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards
  intro x
  rw [realCoordinateFourierChar_neg_mul_eq_dotProduct]
  congr 2
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp [dotProduct, mul_comm]

/-- Finite-dimensional real Fourier inversion in the coordinate form used
here.  The hypotheses are explicit because this lemma is used only for
the concrete Gaussian below. -/
theorem realCoordinate_fourierIntegral_iterate_two_eq_reflection
    (f : (Fin n → ℝ) → ℂ)
    (hf : Integrable f (volume : Measure (Fin n → ℝ)))
    (hFf : Integrable
      (Fourier.fourierIntegral (realCoordinateFourierChar n)
        (volume : Measure (Fin n → ℝ)) f)
      (volume : Measure (Fin n → ℝ)))
    (hcontinuous : Continuous f) :
    Fourier.fourierIntegral (realCoordinateFourierChar n)
        (volume : Measure (Fin n → ℝ))
        (Fourier.fourierIntegral (realCoordinateFourierChar n)
          (volume : Measure (Fin n → ℝ)) f) =
      fun w ↦ f (-w) := by
  let fE : EuclideanSpace ℝ (Fin n) → ℂ :=
    fun x ↦ f (WithLp.ofLp x)
  have hfE : Integrable fE := by
    change Integrable (f ∘ WithLp.ofLp) volume
    rw [(PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).symm.measurableEmbedding]
    exact hf
  have hbridge :
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        Fourier.fourierIntegral (realCoordinateFourierChar n)
          (volume : Measure (Fin n → ℝ)) f (WithLp.ofLp x)) =
        𝓕 fE := by
    funext x
    rw [realCoordinate_fourierIntegral_eq_euclideanFourier]
  have hFfE : Integrable (𝓕 fE) := by
    rw [← hbridge]
    change Integrable
      (Fourier.fourierIntegral (realCoordinateFourierChar n)
        (volume : Measure (Fin n → ℝ)) f ∘ WithLp.ofLp) volume
    rw [(PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).symm.measurableEmbedding]
    exact hFf
  have hcontinuousE : Continuous fE :=
    hcontinuous.comp (PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ))
  have hinversion := hcontinuousE.fourierInv_fourier_eq hfE hFfE
  funext w
  rw [realCoordinate_fourierIntegral_eq_euclideanFourier]
  rw [hbridge]
  have hw := congrFun hinversion (WithLp.toLp 2 (-w))
  rw [Real.fourierInv_eq_fourier_neg] at hw
  simpa using hw

theorem realCoordinateGaussianFourierProduct_eq_const_mul
    (d : ℕ) (b : ℂ) :
    realCoordinateGaussianFourierProduct d b =
      fun w ↦ (1 / b ^ (1 / 2 : ℂ)) ^ d *
        realCoordinateGaussian d b⁻¹ w := by
  funext w
  rw [realCoordinateGaussianFourierProduct,
    realCoordinateGaussian, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1

private theorem integrable_realCoordinateGaussianFourierProduct_of_pos
    (d : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (realCoordinateGaussianFourierProduct d (a : ℂ))
      (volume : Measure (Fin d → ℝ)) := by
  rw [realCoordinateGaussianFourierProduct_eq_const_mul]
  apply Integrable.const_mul
  apply integrable_realCoordinateGaussian
  simpa using inv_pos.mpr ha

theorem polarReal_fourierIntegral_gaussian_arbitraryFrequency
    {b : ℂ} (hb : 0 < b.re) (L : PositiveDefiniteIntegralLattice n)
    (w : Fin n → ℝ) :
    Fourier.fourierIntegral (realCoordinateFourierChar n)
        (volume : Measure (Fin n → ℝ))
        (polarRealGaussian L b) w =
      polarRealGaussianFourierProduct L b
        (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹.mulVec w) := by
  let C := L.rationalQuadraticSpaceMatrix.realPolarMatrix
  let y := C⁻¹.mulVec w
  have hy : C.mulVec y = w := by
    change C.mulVec (C⁻¹.mulVec w) = w
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv C
        (isUnit_iff_ne_zero.mpr
          L.rationalQuadraticSpaceMatrix.realPolarMatrix_det_ne_zero),
      Matrix.one_mulVec]
  have h := polarReal_fourierIntegral_gaussian hb L y
  rw [hy] at h
  exact h

private theorem integrable_comp_invertible_realMatrix
    (g : (Fin n → ℝ) → ℂ)
    (hg : Integrable g (volume : Measure (Fin n → ℝ)))
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : Matrix.det M ≠ 0) :
    Integrable (fun x ↦ g (M.mulVec x))
      (volume : Measure (Fin n → ℝ)) := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hM
  have hgmap : Integrable g
      (Measure.map (Matrix.toLin' M)
        (volume : Measure (Fin n → ℝ))) := by
    rw [hmap]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  have hmeas : AEMeasurable (Matrix.toLin' M)
      (volume : Measure (Fin n → ℝ)) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable.aemeasurable
  have hcomp :=
    (integrable_map_measure hgmap.aestronglyMeasurable hmeas).mp hgmap
  simpa only [Matrix.toLin'_apply] using hcomp

private theorem integrable_polarReal_fourierIntegral_gaussian_of_pos
    {a : ℝ} (ha : 0 < a) (L : PositiveDefiniteIntegralLattice n) :
    Integrable
      (Fourier.fourierIntegral (realCoordinateFourierChar n)
        (volume : Measure (Fin n → ℝ))
        (polarRealGaussian L (a : ℂ)))
      (volume : Measure (Fin n → ℝ)) := by
  let C := L.rationalQuadraticSpaceMatrix.realPolarMatrix
  let A := L.polarRealSqrtMatrix * C⁻¹
  have hA : Matrix.det A ≠ 0 := by
    change Matrix.det (L.polarRealSqrtMatrix * C⁻¹) ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (ne_of_gt L.polarRealSqrtMatrix_det_pos)
      (inv_ne_zero
        L.rationalQuadraticSpaceMatrix.realPolarMatrix_det_ne_zero)
  have hg := integrable_realCoordinateGaussianFourierProduct_of_pos n ha
  have hcomp := integrable_comp_invertible_realMatrix
    (realCoordinateGaussianFourierProduct n (a : ℂ)) hg A hA
  have heq :
      Fourier.fourierIntegral (realCoordinateFourierChar n)
          (volume : Measure (Fin n → ℝ))
          (polarRealGaussian L (a : ℂ)) =
        fun w ↦ (L.polarRealDeterminantScale : ℂ)⁻¹ *
          realCoordinateGaussianFourierProduct n (a : ℂ) (A.mulVec w) := by
    funext w
    rw [polarReal_fourierIntegral_gaussian_arbitraryFrequency
      (by simpa using ha) L w]
    simp only [polarRealGaussianFourierProduct, A, C,
      Matrix.mulVec_mulVec]
  rw [heq]
  exact hcomp.const_mul _

private theorem rationalAdeleCoordinate_fourierIntegral_realFiniteProduct
    (gr : (Fin n → ℝ) → ℂ)
    (gf : (Fin n → RationalFiniteAdele) → ℂ)
    (w : Fin n → RationalAdele) :
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
        (rationalAdeleCoordinateAddHaarMeasure n)
        (fun x ↦ gr (rationalAdeleVectorRealPart n x) *
          gf (rationalAdeleVectorFinitePart n x)) w =
      Fourier.fourierIntegral (realCoordinateFourierChar n)
          (volume : Measure (Fin n → ℝ)) gr
          (rationalAdeleVectorRealPart n w) *
        Fourier.fourierIntegral
          (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateFourierChar n)
          (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure n)
          gf (rationalAdeleVectorFinitePart n w) := by
  letI : SigmaFinite
      (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  rw [Fourier.fourierIntegral_def]
  let wr := rationalAdeleVectorRealPart n w
  let wf := rationalAdeleVectorFinitePart n w
  let fr : (Fin n → ℝ) → ℂ := fun x ↦
    realCoordinateFourierChar n (-(x * wr)) • gr x
  let ff : (Fin n → RationalFiniteAdele) → ℂ := fun x ↦
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateFourierChar n
      (-(x * wf)) • gf x
  let h : (Fin n → ℝ) × (Fin n → RationalFiniteAdele) → ℂ :=
    fun z ↦ fr z.1 * ff z.2
  have hintegrand :
      (fun v : Fin n → RationalAdele ↦
        rationalAdeleCoordinateFourierChar n (-(v * w)) •
          (gr (rationalAdeleVectorRealPart n v) *
            gf (rationalAdeleVectorFinitePart n v))) =
        fun v ↦ h (rationalAdeleVectorRealFiniteEquiv n v) := by
    funext v
    rw [rationalAdeleCoordinateFourierChar_eq_real_mul_finite,
      rationalAdeleVectorRealPart_neg_mul,
      rationalAdeleVectorFinitePart_neg_mul]
    simp only [rationalAdeleVectorRealFiniteEquiv_apply, h, fr, ff,
      Circle.smul_def, smul_eq_mul, Circle.coe_mul]
    ring
  rw [hintegrand]
  rw [(measurePreserving_rationalAdeleVectorRealFiniteSplit n).integral_comp' h]
  rw [MeasureTheory.integral_prod_mul]
  rw [← Fourier.fourierIntegral_def, ← Fourier.fourierIntegral_def]

private theorem continuous_polarRealGaussian
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    Continuous (polarRealGaussian L b) := by
  exact (continuous_realCoordinateGaussian n b).comp
    (Matrix.toLin' L.polarRealSqrtMatrix).continuous_of_finiteDimensional

/-- The real positive-definite factor has the expected negative-kernel
Fourier square. -/
theorem polarReal_fourierIntegral_iterate_two_eq_reflection
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    Fourier.fourierIntegral (realCoordinateFourierChar n)
        (volume : Measure (Fin n → ℝ))
        (Fourier.fourierIntegral (realCoordinateFourierChar n)
          (volume : Measure (Fin n → ℝ))
          (polarRealGaussian L (a : ℂ))) =
      fun x ↦ polarRealGaussian L (a : ℂ) (-x) := by
  exact realCoordinate_fourierIntegral_iterate_two_eq_reflection
    (polarRealGaussian L (a : ℂ))
    (integrable_polarRealGaussian (by simpa using ha) L)
    (integrable_polarReal_fourierIntegral_gaussian_of_pos ha L)
    (continuous_polarRealGaussian L (a : ℂ))

private theorem rationalAdeleVectorRealPart_neg
    (d : ℕ) (x : Fin d → RationalAdele) :
    rationalAdeleVectorRealPart d (-x) =
      -rationalAdeleVectorRealPart d x := by
  funext i
  change rationalInfiniteAdeleRingEquivReal (-(x i).1) =
    -rationalInfiniteAdeleRingEquivReal (x i).1
  exact map_neg rationalInfiniteAdeleRingEquivReal (x i).1

private theorem rationalAdeleVectorFinitePart_neg
    (d : ℕ) (x : Fin d → RationalAdele) :
    rationalAdeleVectorFinitePart d (-x) =
      -rationalAdeleVectorFinitePart d x := by
  rfl

private theorem rationalFiniteAdeleVectorIntegralIndicator_neg
    (d : ℕ) (x : Fin d → RationalFiniteAdele) :
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator (-x) =
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator x := by
  rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator]
  apply Finset.prod_congr rfl
  intro i _hi
  simp only [Pi.neg_apply, rationalFiniteAdeleIntegralIndicator]
  by_cases hx : x i ∈ integralFiniteAdeleSubring
  · have hneg : -x i ∈ integralFiniteAdeleSubring :=
      integralFiniteAdeleSubring.neg_mem hx
    simp [hx, hneg]
  · have hneg : -x i ∉ integralFiniteAdeleSubring := by
      intro h
      exact hx (by simpa using integralFiniteAdeleSubring.neg_mem h)
    simp [hx, hneg]

/-- The base coordinate Fourier transform squares to literal reflection on
the concrete polar Gaussian--lattice test.  The proof is factorwise: ordinary
real Fourier inversion for the Gaussian and the already certified self-dual
finite integral-lattice indicator. -/
theorem rationalAdeleCoordinate_fourierIntegral_iterate_two_polarGaussianLattice_eq_reflection
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
        (rationalAdeleCoordinateAddHaarMeasure n)
        (Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
          (rationalAdeleCoordinateAddHaarMeasure n)
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))) =
      fun x ↦ rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) (-x) := by
  let Fr : ((Fin n → ℝ) → ℂ) → (Fin n → ℝ) → ℂ :=
    Fourier.fourierIntegral (realCoordinateFourierChar n)
      (volume : Measure (Fin n → ℝ))
  let gf : (Fin n → RationalFiniteAdele) → ℂ :=
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator
  have hfirst :
      Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
          (rationalAdeleCoordinateAddHaarMeasure n)
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) =
        fun w ↦ Fr (polarRealGaussian L (a : ℂ))
            (rationalAdeleVectorRealPart n w) *
          gf (rationalAdeleVectorFinitePart n w) := by
    funext w
    unfold rationalAdeleVectorPolarGaussianLatticeTest
    rw [rationalAdeleCoordinate_fourierIntegral_realFiniteProduct]
    rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinate_fourierIntegral_integralIndicator]
  rw [hfirst]
  funext w
  rw [rationalAdeleCoordinate_fourierIntegral_realFiniteProduct]
  rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinate_fourierIntegral_integralIndicator]
  have hreal := congrFun
    (polarReal_fourierIntegral_iterate_two_eq_reflection L ha)
    (rationalAdeleVectorRealPart n w)
  dsimp only [Fr, gf]
  rw [hreal]
  unfold rationalAdeleVectorPolarGaussianLatticeTest
  rw [
    rationalAdeleVectorRealPart_neg, rationalAdeleVectorFinitePart_neg,
    rationalFiniteAdeleVectorIntegralIndicator_neg]

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- On the concrete polar Gaussian--lattice test, the specialized Weyl
operator squares to the already defined rational central reflection.  No
generic Fourier inversion or Weil relation is asserted. -/
theorem rationalAdeleRankOneWeylOperator_iterate_two_polarGaussianLattice_eq_negOneDilation
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (PositiveDefiniteIntegralLattice.rationalAdeleVectorPolarGaussianLatticeTest
            L (a : ℂ))) =
      rationalAdeleRankOneDilationOperator (-1)
        (PositiveDefiniteIntegralLattice.rationalAdeleVectorPolarGaussianLatticeTest
          L (a : ℂ)) := by
  rw [L.rationalQuadraticSpaceMatrix
    |>.rationalAdeleRankOneWeylOperator_iterate_two_eq_coordinateFourierSquare]
  rw [PositiveDefiniteIntegralLattice.rationalAdeleCoordinate_fourierIntegral_iterate_two_polarGaussianLattice_eq_reflection
    L ha]
  funext x
  exact (rationalAdeleRankOneDilationOperator_neg_one_apply
    (PositiveDefiniteIntegralLattice.rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) x).symm

end RationalQuadraticSpaceMatrix

end
