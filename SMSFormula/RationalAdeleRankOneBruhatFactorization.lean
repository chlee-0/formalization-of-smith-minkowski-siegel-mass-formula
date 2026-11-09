import SMSFormula.RationalAdeleRankOneWeilGenerators

/-!
# Real--finite factorization of the rank-one Bruhat coefficient

This file exposes the two analytic factors hidden in
`(W (N(t) Phi))(0)` for the concrete polar Gaussian--lattice test.  The real
factor is the exact positive-definite Gaussian with complex parameter
`b - t * I`; the finite factor is the literal quadratic Gauss integral over
the standard integral finite-adelic lattice.

This reduction is deliberately exact.  In particular, it neither bounds the
finite quadratic Gauss integral nor asserts summability over `t : ℚ`.  The
remaining rank-at-least-five input must obtain denominator decay from that
finite factor; archimedean decay alone cannot control the dense rational
index.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped FourierTransform ComplexConjugate

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The real component of the quadratic form after the canonical real--finite
split of the full rational adele carrier. -/
def realQuadraticFormValue
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (V.realFormMatrix.mulVec x)

/-- The finite-adelic component of the quadratic form after the canonical
real--finite split. -/
def finiteAdelicQuadraticFormValue
    (V : RationalQuadraticSpaceMatrix n)
    (x : Fin n → RationalFiniteAdele) : RationalFiniteAdele :=
  dotProduct x (V.finiteAdelicFormMatrix.mulVec x)

/-- The finite quadratic phase on the standard integral lattice. -/
def rationalFiniteAdeleQuadraticPhase
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (x : Fin n → RationalFiniteAdele) : Circle :=
  rationalFiniteAdeleFourierChar
    (algebraMap ℚ RationalFiniteAdele t * V.finiteAdelicQuadraticFormValue x)

/-- The exact finite quadratic Gauss integral which supplies the denominator
decay in the Bruhat series. -/
noncomputable def rationalFiniteAdeleQuadraticGaussIntegral
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) : ℂ :=
  ∫ x : Fin n → RationalFiniteAdele,
    (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
      rationalFiniteAdeleVectorIntegralIndicator x
    ∂rationalFiniteAdeleCoordinateAddHaarMeasure n

/-- On the integral lattice, the finite quadratic phase is periodic under an
integer shift of the rational parameter.  This is the exact first reduction
from a rational parameter to its denominator data. -/
theorem rationalFiniteAdeleQuadraticPhase_add_intCast_mul_indicator
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (z : ℤ)
    (x : Fin n → RationalFiniteAdele) :
    (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase
        (t + (z : ℚ)) x : ℂ) * rationalFiniteAdeleVectorIntegralIndicator x =
      (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase
        t x : ℂ) * rationalFiniteAdeleVectorIntegralIndicator x := by
  by_cases hx : x ∈ integralFiniteAdeleVectors n
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hx]
    simp only [mul_one]
    unfold rationalFiniteAdeleQuadraticPhase
    rw [map_add, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
    have hq :
        L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x ∈
          integralFiniteAdeleSubring := by
      simpa [finiteAdelicQuadraticFormValue] using
        L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring x x hx hx
    have hz :
        algebraMap ℚ RationalFiniteAdele (z : ℚ) *
            L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x ∈
          integralFiniteAdeleSubring := by
      apply Subring.mul_mem integralFiniteAdeleSubring
      · exact integer_mem_integralFiniteAdeleSubring z
      · exact hq
    rw [rationalFiniteAdeleFourierChar_eq_one_of_mem_integral _ hz]
    simp
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx]
    simp

/-- The finite quadratic Gauss integral is periodic under integer shifts of
its rational parameter. -/
theorem rationalFiniteAdeleQuadraticGaussIntegral_add_intCast
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (z : ℤ) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
        (t + (z : ℚ)) =
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t := by
  unfold rationalFiniteAdeleQuadraticGaussIntegral
  apply integral_congr_ae
  filter_upwards
  intro x
  exact
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase_add_intCast_mul_indicator
      L t z x

/-- The real part of the full adelic quadratic value is the real quadratic
form evaluated on the canonical real coordinates. -/
theorem rationalAdeleVectorRealPart_fullAdelicQuadraticFormValue
    (V : RationalQuadraticSpaceMatrix n)
    (x : Fin n → RationalAdele) :
    rationalInfiniteAdeleContinuousAddEquivReal
        (V.fullAdelicQuadraticFormValue x).1 =
      V.realQuadraticFormValue (rationalAdeleVectorRealPart n x) := by
  let h : RationalAdele →+* ℝ :=
    rationalInfiniteAdeleRingEquivReal.toRingHom.comp
      (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
  simp only [fullAdelicQuadraticFormValue_eq_dotProduct,
    realQuadraticFormValue, dotProduct, Matrix.mulVec,
    rationalAdeleVectorRealPart]
  change h (∑ i, x i * ∑ j, V.fullAdelicFormMatrix i j * x j) =
    ∑ i, h (x i) * ∑ j, V.realFormMatrix i j * h (x j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_mul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_mul]
  congr 1
  exact rationalInfiniteAdeleContinuousAddEquivReal_algebraMap _

/-- The finite part of the full adelic quadratic value is the finite-adelic
quadratic form evaluated on the canonical finite coordinates. -/
theorem rationalAdeleVectorFinitePart_fullAdelicQuadraticFormValue
    (V : RationalQuadraticSpaceMatrix n)
    (x : Fin n → RationalAdele) :
    (V.fullAdelicQuadraticFormValue x).2 =
      V.finiteAdelicQuadraticFormValue (rationalAdeleVectorFinitePart n x) := by
  let h : RationalAdele →+* RationalFiniteAdele :=
    RingHom.snd RationalInfiniteAdele RationalFiniteAdele
  simp only [fullAdelicQuadraticFormValue_eq_dotProduct,
    finiteAdelicQuadraticFormValue, dotProduct, Matrix.mulVec,
    rationalAdeleVectorFinitePart]
  change h (∑ i, x i * ∑ j, V.fullAdelicFormMatrix i j * x j) =
    ∑ i, h (x i) * ∑ j, V.finiteAdelicFormMatrix i j * h (x j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_mul, map_sum]
  congr 1

/-- On a rational parameter, the global quadratic phase splits exactly into
its real phase and finite quadratic phase. -/
theorem rationalAdeleRankOneQuadraticPhase_eq_real_mul_finite
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (x : Fin n → RationalAdele) :
    (V.rationalAdeleRankOneQuadraticPhase
        (algebraMap ℚ RationalAdele t) x : ℂ) =
      (Real.fourierChar
          ((t : ℝ) * V.realQuadraticFormValue
            (rationalAdeleVectorRealPart n x)) : ℂ) *
        (V.rationalFiniteAdeleQuadraticPhase t
          (rationalAdeleVectorFinitePart n x) : ℂ) := by
  let hreal : RationalAdele →+* ℝ :=
    rationalInfiniteAdeleRingEquivReal.toRingHom.comp
      (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
  let hfinite : RationalAdele →+* RationalFiniteAdele :=
    RingHom.snd RationalInfiniteAdele RationalFiniteAdele
  have hsnd : (algebraMap ℚ RationalAdele t).2 =
      algebraMap ℚ RationalFiniteAdele t := by
    exact DFunLike.congr_fun
      (RingHom.ext_rat
        ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp
          (algebraMap ℚ RationalAdele))
        (algebraMap ℚ RationalFiniteAdele)) t
  have hfst : (algebraMap ℚ RationalAdele t).1 =
      algebraMap ℚ RationalInfiniteAdele t := by
    exact DFunLike.congr_fun
      (RingHom.ext_rat
        ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
          (algebraMap ℚ RationalAdele))
        (algebraMap ℚ RationalInfiniteAdele)) t
  have hrealArg :
      rationalInfiniteAdeleContinuousAddEquivReal
          (algebraMap ℚ RationalAdele t *
            V.fullAdelicQuadraticFormValue x).1 =
        (t : ℝ) * V.realQuadraticFormValue
          (rationalAdeleVectorRealPart n x) := by
    change hreal (algebraMap ℚ RationalAdele t *
      V.fullAdelicQuadraticFormValue x) = _
    rw [map_mul]
    change rationalInfiniteAdeleContinuousAddEquivReal
      (algebraMap ℚ RationalAdele t).1 *
        rationalInfiniteAdeleContinuousAddEquivReal
          (V.fullAdelicQuadraticFormValue x).1 = _
    rw [hfst, V.rationalAdeleVectorRealPart_fullAdelicQuadraticFormValue,
      rationalInfiniteAdeleContinuousAddEquivReal_algebraMap]
    congr 1
  have hfiniteArg :
      (algebraMap ℚ RationalAdele t *
          V.fullAdelicQuadraticFormValue x).2 =
        algebraMap ℚ RationalFiniteAdele t *
          V.finiteAdelicQuadraticFormValue
            (rationalAdeleVectorFinitePart n x) := by
    change hfinite (algebraMap ℚ RationalAdele t *
      V.fullAdelicQuadraticFormValue x) = _
    rw [map_mul]
    change (algebraMap ℚ RationalAdele t).2 *
      (V.fullAdelicQuadraticFormValue x).2 = _
    rw [hsnd, V.rationalAdeleVectorFinitePart_fullAdelicQuadraticFormValue]
  unfold rationalAdeleRankOneQuadraticPhase rationalFiniteAdeleQuadraticPhase
  rw [rationalAdeleFourierChar_apply,
    rationalAdeleArchimedeanFourierChar_apply,
    hrealArg, hfiniteArg, Circle.coe_mul]

/-- Multiplying the real polar Gaussian by the real quadratic phase merely
replaces its complex scale `b` by `b - t * I`. -/
theorem realQuadraticPhase_mul_polarRealGaussian
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (t : ℚ) (x : Fin n → ℝ) :
    (Real.fourierChar
        ((t : ℝ) *
          L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : ℂ) *
      polarRealGaussian L b x =
        polarRealGaussian L (b - (t : ℂ) * Complex.I) x := by
  rw [polarRealGaussian, polarRealGaussian,
    realCoordinateGaussian_eq_exp_dotProduct,
    realCoordinateGaussian_eq_exp_dotProduct,
    L.dotProduct_polarRealSqrtMatrix_mulVec]
  have hpolar : L.rationalQuadraticSpaceMatrix.realPolarMatrix =
      (2 : ℝ) • L.rationalQuadraticSpaceMatrix.realFormMatrix := by
    ext i j
    simp [RationalQuadraticSpaceMatrix.realPolarMatrix,
      RationalQuadraticSpaceMatrix.realFormMatrix,
      RationalQuadraticSpaceMatrix.polarMatrix]
  rw [hpolar]
  simp only [realQuadraticFormValue, Matrix.smul_mulVec, dotProduct_smul]
  rw [Real.fourierChar_apply]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At zero frequency the real factor is the reciprocal determinant scale
times one complex square-root factor in each coordinate. -/
theorem polarRealGaussianFourierProduct_zero
    (L : PositiveDefiniteIntegralLattice n) (c : ℂ) :
    polarRealGaussianFourierProduct L c 0 =
      (L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / c ^ (1 / 2 : ℂ)) ^ n := by
  simp [polarRealGaussianFourierProduct,
    realCoordinateGaussianFourierProduct]

/-- Exact real--finite factorization of the concrete Bruhat coefficient.
The finite factor is left completely visible because it is the source of the
rational-denominator decay needed for rank-at-least-five summability. -/
theorem rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_real_mul_finite
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L b) t =
      polarRealGaussianFourierProduct L (b - (t : ℂ) * Complex.I) 0 *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t := by
  letI : SigmaFinite
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  let V := L.rationalQuadraticSpaceMatrix
  let gr : (Fin n → ℝ) → ℂ := fun x ↦
    polarRealGaussian L (b - (t : ℂ) * Complex.I) x
  let gf : (Fin n → RationalFiniteAdele) → ℂ := fun x ↦
    (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
      rationalFiniteAdeleVectorIntegralIndicator x
  let g : (Fin n → ℝ) × (Fin n → RationalFiniteAdele) → ℂ :=
    fun z ↦ gr z.1 * gf z.2
  have hparam : 0 < (b - (t : ℂ) * Complex.I).re := by
    simpa using hb
  have hintegrand :
      (fun x : Fin n → RationalAdele ↦
        (V.rationalAdeleRankOneQuadraticPhase
          (algebraMap ℚ RationalAdele t) x : ℂ) *
          rationalAdeleVectorPolarGaussianLatticeTest L b x) =
        fun x ↦ g (rationalAdeleVectorRealFiniteEquiv n x) := by
    funext x
    rw [V.rationalAdeleRankOneQuadraticPhase_eq_real_mul_finite]
    simp only [rationalAdeleVectorPolarGaussianLatticeTest]
    simp only [g, gr, gf, rationalAdeleVectorRealFiniteEquiv_apply]
    rw [← RationalQuadraticSpaceMatrix.realQuadraticPhase_mul_polarRealGaussian L]
    ring
  rw [rationalAdeleRankOneBruhatCoefficient,
    rationalAdeleRankOneWeylOperator, Fourier.fourierIntegral_def]
  simp only [Matrix.mulVec_zero, mul_zero, neg_zero,
    rationalAdeleRankOneUnipotentOperator]
  rw [AddChar.map_zero_eq_one]
  simp only [one_smul]
  rw [hintegrand]
  rw [(measurePreserving_rationalAdeleVectorRealFiniteSplit n).integral_comp' g]
  rw [MeasureTheory.integral_prod_mul]
  change
    (∫ x : Fin n → ℝ, gr x ∂(volume : Measure (Fin n → ℝ))) *
      (∫ x : Fin n → RationalFiniteAdele, gf x
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) = _
  have hreal := polarReal_fourierIntegral_gaussian hparam L (0 : Fin n → ℝ)
  rw [Fourier.fourierIntegral_def] at hreal
  have hreal' :
      (∫ x : Fin n → ℝ, gr x ∂(volume : Measure (Fin n → ℝ))) =
        polarRealGaussianFourierProduct L
          (b - (t : ℂ) * Complex.I) 0 := by
    simpa only [gr, Matrix.mulVec_zero, mul_zero, neg_zero,
      AddChar.map_zero_eq_one, one_smul] using hreal
  rw [hreal']
  rfl

/-- Fully explicit archimedean factor in the concrete Bruhat coefficient.
All remaining arithmetic cancellation is concentrated in the finite
quadratic Gauss integral. -/
theorem rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finite
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L b) t =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / (b - (t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t := by
  rw [rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_real_mul_finite
    L hb t]
  rw [polarRealGaussianFourierProduct_zero]

end RationalQuadraticSpaceMatrix

end
