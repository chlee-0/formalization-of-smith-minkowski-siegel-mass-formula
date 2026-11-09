import SMSFormula.RationalAdeleRankOnePolarGaussianLatticeFourierSquare
import SMSFormula.RationalAdeleRankOneBruhatFactorization

/-!
# Exact analytic reduction of the nonzero rational Bruhat relation

This file reduces the zero-frequency value of `W N(t) W` on the concrete
polar Gaussian--lattice test to its literal real and finite quadratic Gauss
integrals.  The finite factor is taken over the actual polar-dual lattice
which occurs after the first Weyl transform.

No reciprocity formula, Weil index, generic Weil representation, or cusp
functional transformation is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The finite quadratic Gauss integral over the literal polar-dual lattice
which occurs after one application of the concrete Weyl operator. -/
noncomputable def rationalFiniteAdeleDualQuadraticGaussIntegral
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) : ℂ :=
  ∫ x : Fin n → RationalFiniteAdele,
    (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
      V.finitePolarDualLatticeIndicator x
    ∂rationalFiniteAdeleCoordinateAddHaarMeasure n

/-- The real quadratic Gauss integral left after the first Weyl transform of
the positive polar Gaussian. -/
noncomputable def polarRealGaussianFourierBruhatIntegral
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (t : ℚ) : ℂ :=
  ∫ x : Fin n → ℝ,
    (Real.fourierChar
      ((t : ℝ) * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : ℂ) *
      polarRealGaussianFourierProduct L (a : ℂ) x

/-- For positive real scale, the real polar Fourier product is the reciprocal-
scale polar Gaussian times the exact determinant and square-root constant. -/
theorem polarRealGaussianFourierProduct_of_pos_eq_const_mul
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (x : Fin n → ℝ) :
    polarRealGaussianFourierProduct L (a : ℂ) x =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / (Real.sqrt a : ℂ)) ^ n) *
        polarRealGaussian L ((a : ℂ)⁻¹) x := by
  rw [polarRealGaussianFourierProduct,
    realCoordinateGaussianFourierProduct_of_pos n ha,
    polarRealGaussian, realCoordinateGaussian_eq_exp_dotProduct]
  ring_nf

/-- The exact real factor in the zero-frequency value of `W N(t) W`.
The reciprocal Gaussian scale and the quadratic twist remain literal. -/
theorem polarRealGaussianFourierBruhatIntegral_eq
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (t : ℚ) :
    polarRealGaussianFourierBruhatIntegral L a t =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / (Real.sqrt a : ℂ)) ^ n) *
        polarRealGaussianFourierProduct L
          ((a : ℂ)⁻¹ - (t : ℂ) * Complex.I) 0 := by
  unfold polarRealGaussianFourierBruhatIntegral
  rw [show (fun x : Fin n → ℝ ↦
      (Real.fourierChar
        ((t : ℝ) * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : ℂ) *
        polarRealGaussianFourierProduct L (a : ℂ) x) =
      fun x ↦ ((L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / (Real.sqrt a : ℂ)) ^ n) *
        ((Real.fourierChar
          ((t : ℝ) * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : ℂ) *
          polarRealGaussian L ((a : ℂ)⁻¹) x) by
    funext x
    rw [polarRealGaussianFourierProduct_of_pos_eq_const_mul L ha]
    ring]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [show (fun x : Fin n → ℝ ↦
      (Real.fourierChar
        ((t : ℝ) * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : ℂ) *
        polarRealGaussian L ((a : ℂ)⁻¹) x) =
      polarRealGaussian L ((a : ℂ)⁻¹ - (t : ℂ) * Complex.I) by
    funext x
    exact realQuadraticPhase_mul_polarRealGaussian L _ t x]
  have hparam : 0 < (((a : ℂ)⁻¹ - (t : ℂ) * Complex.I)).re := by
    simpa [Complex.inv_re] using inv_pos.mpr ha
  have hreal := polarReal_fourierIntegral_gaussian hparam L (0 : Fin n → ℝ)
  rw [Fourier.fourierIntegral_def] at hreal
  simpa only [Matrix.mulVec_zero, mul_zero, neg_zero,
    AddChar.map_zero_eq_one, one_smul] using hreal

/-- Exact real--finite factorization of the nonzero analytic Bruhat value
after the first Weyl transform.  No scalar has been simplified. -/
theorem rationalAdeleRankOneWeyl_unipotent_weyl_polarGaussianLattice_zero_eq_real_mul_finite
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator
          (algebraMap ℚ RationalAdele t)
          (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
            (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)))) 0 =
      polarRealGaussianFourierBruhatIntegral L a t *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t := by
  letI : SigmaFinite
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  let V := L.rationalQuadraticSpaceMatrix
  rw [rationalAdeleRankOneWeylOperator_polarGaussianLattice L
    (by simpa using ha)]
  rw [rationalAdeleRankOneWeylOperator, Fourier.fourierIntegral_def]
  simp only [Matrix.mulVec_zero, mul_zero, neg_zero,
    rationalAdeleRankOneUnipotentOperator, AddChar.map_zero_eq_one, one_smul]
  let gr : (Fin n → ℝ) → ℂ := fun x ↦
    (Real.fourierChar ((t : ℝ) * V.realQuadraticFormValue x) : ℂ) *
      polarRealGaussianFourierProduct L (a : ℂ) x
  let gf : (Fin n → RationalFiniteAdele) → ℂ := fun x ↦
    (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
      V.finitePolarDualLatticeIndicator x
  let g : (Fin n → ℝ) × (Fin n → RationalFiniteAdele) → ℂ :=
    fun z ↦ gr z.1 * gf z.2
  have hintegrand :
      (fun x : Fin n → RationalAdele ↦
        (V.rationalAdeleRankOneQuadraticPhase
          (algebraMap ℚ RationalAdele t) x : ℂ) *
          rationalAdeleVectorPolarGaussianLatticeFourierProduct L (a : ℂ) x) =
        fun x ↦ g (rationalAdeleVectorRealFiniteEquiv n x) := by
    funext x
    rw [V.rationalAdeleRankOneQuadraticPhase_eq_real_mul_finite]
    simp only [rationalAdeleVectorPolarGaussianLatticeFourierProduct,
      rationalAdeleVectorRealFiniteEquiv_apply, g, gr, gf]
    ring
  rw [hintegrand]
  rw [(measurePreserving_rationalAdeleVectorRealFiniteSplit n).integral_comp' g]
  rw [MeasureTheory.integral_prod_mul]
  rfl

/-- At the zero vector, the visible upper-unipotent and rational diagonal in
the nonzero Bruhat factor disappear.  What remains is exactly the old finite
Bruhat coefficient at `-t⁻¹`. -/
theorem rationalAdeleRankOne_nonzeroBruhatTarget_zero_eq_bruhatCoefficient
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneUnipotentOperator
        (algebraMap ℚ RationalAdele (-t⁻¹))
        (rationalAdeleRankOneDilationOperator (-t⁻¹)
          (V.rationalAdeleRankOneWeylOperator
            (V.rationalAdeleRankOneUnipotentOperator
              (algebraMap ℚ RationalAdele (-t⁻¹)) Phi))) 0 =
      V.rationalAdeleRankOneBruhatCoefficient Phi (-t⁻¹) := by
  rw [rationalAdeleRankOneUnipotentOperator]
  have hphase :
      V.rationalAdeleRankOneQuadraticPhase
        (algebraMap ℚ RationalAdele (-t⁻¹)) 0 = 1 := by
    unfold rationalAdeleRankOneQuadraticPhase
    rw [V.fullAdelicQuadraticFormValue_eq_dotProduct]
    simp
  rw [hphase]
  simp only [Circle.coe_one, one_mul,
    rationalAdeleRankOneDilationOperator_zero_apply]
  rfl

/-- The exact input for the nonzero analytic Bruhat relation on the
concrete polar orbit.  After the proved real Gaussian calculation, the
desired operator value is equivalent to one literal equality between the
real factors and the two finite quadratic Gauss integrals. -/
theorem rationalAdeleRankOne_nonzeroBruhatAnalyticRelation_iff_real_finite
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) {t : ℚ} (_ht : t ≠ 0) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator
          (algebraMap ℚ RationalAdele t)
          (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
            (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)))) 0 =
      L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator
        (algebraMap ℚ RationalAdele (-t⁻¹))
        (rationalAdeleRankOneDilationOperator (-t⁻¹)
          (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
            (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator
              (algebraMap ℚ RationalAdele (-t⁻¹))
              (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))))) 0 ↔
    (((L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / (Real.sqrt a : ℂ)) ^ n) *
          polarRealGaussianFourierProduct L
            ((a : ℂ)⁻¹ - (t : ℂ) * Complex.I) 0) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t =
      polarRealGaussianFourierProduct L
          ((a : ℂ) + (t⁻¹ : ℂ) * Complex.I) 0 *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
          (-t⁻¹) := by
  rw [rationalAdeleRankOne_nonzeroBruhatTarget_zero_eq_bruhatCoefficient]
  rw [rationalAdeleRankOneWeyl_unipotent_weyl_polarGaussianLattice_zero_eq_real_mul_finite
    L ha t]
  rw [polarRealGaussianFourierBruhatIntegral_eq L ha t]
  rw [rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_real_mul_finite
    L (by simpa using ha) (-t⁻¹)]
  push_cast
  ring_nf

end RationalQuadraticSpaceMatrix

end
