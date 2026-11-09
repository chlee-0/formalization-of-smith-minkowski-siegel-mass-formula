import SMSFormula.RationalAdeleRankOneBruhatFactorization
import SMSFormula.RationalAdeleRankOneFiniteOnlyDilationBruhat

/-!
# Real--finite factorization at an arbitrary adelic Bruhat parameter

Finite-only dilation takes a rational diagonal unipotent parameter to a
genuinely adelic one.  This file extends the existing exact Bruhat
factorization only as far as that orbit requires.  For an arbitrary
`a : RationalAdele`, the zero-frequency term splits into a real Gaussian at
the literal real component of `a` and a finite quadratic Gauss integral at
the literal finite component of `a`.

No sum over adelic parameters, finite strong-approximation choice, estimate,
shell identity, or Eisenstein comparison is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped FourierTransform ComplexConjugate

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The finite quadratic phase with a literal finite-adelic, rather than
rational-diagonal, parameter. -/
def rationalFiniteAdeleQuadraticPhaseAt
    (V : RationalQuadraticSpaceMatrix n) (s : RationalFiniteAdele)
    (x : Fin n → RationalFiniteAdele) : Circle :=
  rationalFiniteAdeleFourierChar (s * V.finiteAdelicQuadraticFormValue x)

/-- The corresponding finite quadratic Gauss integral on the standard
integral finite-adelic lattice. -/
noncomputable def rationalFiniteAdeleQuadraticGaussIntegralAt
    (V : RationalQuadraticSpaceMatrix n) (s : RationalFiniteAdele) : ℂ :=
  ∫ x : Fin n → RationalFiniteAdele,
    (V.rationalFiniteAdeleQuadraticPhaseAt s x : ℂ) *
      rationalFiniteAdeleVectorIntegralIndicator x
    ∂rationalFiniteAdeleCoordinateAddHaarMeasure n

/-- The arbitrary finite-adelic definition restricts literally to the old
rational-parameter phase. -/
@[simp]
theorem rationalFiniteAdeleQuadraticPhaseAt_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (x : Fin n → RationalFiniteAdele) :
    V.rationalFiniteAdeleQuadraticPhaseAt
        (algebraMap ℚ RationalFiniteAdele t) x =
      V.rationalFiniteAdeleQuadraticPhase t x :=
  rfl

/-- The arbitrary finite-adelic integral restricts literally to the old
rational quadratic Gauss integral. -/
@[simp]
theorem rationalFiniteAdeleQuadraticGaussIntegralAt_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    V.rationalFiniteAdeleQuadraticGaussIntegralAt
        (algebraMap ℚ RationalFiniteAdele t) =
      V.rationalFiniteAdeleQuadraticGaussIntegral t :=
  rfl

/-- The real scalar carried by the infinite component of a rational adele. -/
def rationalAdeleRealScalar (a : RationalAdele) : ℝ :=
  rationalInfiniteAdeleContinuousAddEquivReal a.1

/-- The global quadratic phase at an arbitrary adelic parameter splits into
its actual real and finite components. -/
theorem rationalAdeleRankOneQuadraticPhase_eq_real_mul_finiteAt
    (V : RationalQuadraticSpaceMatrix n) (a : RationalAdele)
    (x : Fin n → RationalAdele) :
    (V.rationalAdeleRankOneQuadraticPhase a x : ℂ) =
      (Real.fourierChar
          (rationalAdeleRealScalar a * V.realQuadraticFormValue
            (rationalAdeleVectorRealPart n x)) : ℂ) *
        (V.rationalFiniteAdeleQuadraticPhaseAt a.2
          (rationalAdeleVectorFinitePart n x) : ℂ) := by
  let hreal : RationalAdele →+* ℝ :=
    rationalInfiniteAdeleRingEquivReal.toRingHom.comp
      (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
  let hfinite : RationalAdele →+* RationalFiniteAdele :=
    RingHom.snd RationalInfiniteAdele RationalFiniteAdele
  have hrealArg :
      rationalInfiniteAdeleContinuousAddEquivReal
          (a * V.fullAdelicQuadraticFormValue x).1 =
        rationalAdeleRealScalar a * V.realQuadraticFormValue
          (rationalAdeleVectorRealPart n x) := by
    change hreal (a * V.fullAdelicQuadraticFormValue x) = _
    rw [map_mul]
    change rationalInfiniteAdeleContinuousAddEquivReal a.1 *
        rationalInfiniteAdeleContinuousAddEquivReal
          (V.fullAdelicQuadraticFormValue x).1 = _
    rw [V.rationalAdeleVectorRealPart_fullAdelicQuadraticFormValue]
    rfl
  have hfiniteArg :
      (a * V.fullAdelicQuadraticFormValue x).2 =
        a.2 * V.finiteAdelicQuadraticFormValue
          (rationalAdeleVectorFinitePart n x) := by
    change hfinite (a * V.fullAdelicQuadraticFormValue x) = _
    rw [map_mul]
    change a.2 * (V.fullAdelicQuadraticFormValue x).2 = _
    rw [V.rationalAdeleVectorFinitePart_fullAdelicQuadraticFormValue]
  unfold rationalAdeleRankOneQuadraticPhase
    rationalFiniteAdeleQuadraticPhaseAt
  rw [rationalAdeleFourierChar_apply,
    rationalAdeleArchimedeanFourierChar_apply,
    hrealArg, hfiniteArg, Circle.coe_mul]

/-- Multiplication by a real quadratic phase at any real parameter changes
only the imaginary part of the polar Gaussian scale. -/
theorem realQuadraticPhase_mul_polarRealGaussian_real
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (s : ℝ) (x : Fin n → ℝ) :
    (Real.fourierChar
        (s * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : ℂ) *
      polarRealGaussian L b x =
        polarRealGaussian L (b - (s : ℂ) * Complex.I) x := by
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
  ring

/-- Exact real--finite factorization of the arbitrary-adelic Bruhat
coefficient for the concrete polar Gaussian--lattice test. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice_eq_real_mul_finiteAt
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (a : RationalAdele) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L b) a =
      polarRealGaussianFourierProduct L
          (b - (rationalAdeleRealScalar a : ℂ) * Complex.I) 0 *
        (L.rationalQuadraticSpaceMatrix
          |>.rationalFiniteAdeleQuadraticGaussIntegralAt a.2) := by
  letI : SigmaFinite
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  let V := L.rationalQuadraticSpaceMatrix
  let s := rationalAdeleRealScalar a
  let gr : (Fin n → ℝ) → ℂ := fun x ↦
    polarRealGaussian L (b - (s : ℂ) * Complex.I) x
  let gf : (Fin n → RationalFiniteAdele) → ℂ := fun x ↦
    (V.rationalFiniteAdeleQuadraticPhaseAt a.2 x : ℂ) *
      rationalFiniteAdeleVectorIntegralIndicator x
  let g : (Fin n → ℝ) × (Fin n → RationalFiniteAdele) → ℂ :=
    fun z ↦ gr z.1 * gf z.2
  have hparam : 0 < (b - (s : ℂ) * Complex.I).re := by
    norm_num [Complex.mul_re]
    exact hb
  have hintegrand :
      (fun x : Fin n → RationalAdele ↦
        (V.rationalAdeleRankOneQuadraticPhase a x : ℂ) *
          rationalAdeleVectorPolarGaussianLatticeTest L b x) =
        fun x ↦ g (rationalAdeleVectorRealFiniteEquiv n x) := by
    funext x
    rw [V.rationalAdeleRankOneQuadraticPhase_eq_real_mul_finiteAt]
    simp only [rationalAdeleVectorPolarGaussianLatticeTest]
    simp only [g, gr, gf, s, rationalAdeleVectorRealFiniteEquiv_apply]
    rw [← RationalQuadraticSpaceMatrix.realQuadraticPhase_mul_polarRealGaussian_real L]
    ring
  rw [rationalAdeleRankOneAdelicBruhatCoefficient,
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
          (b - (s : ℂ) * Complex.I) 0 := by
    simpa only [gr, Matrix.mulVec_zero, mul_zero, neg_zero,
      AddChar.map_zero_eq_one, one_smul] using hreal
  rw [hreal']
  rfl

/-- The arbitrary-adelic factorization with the archimedean zero-frequency
factor evaluated explicitly. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finiteAt
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (a : RationalAdele) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L b) a =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / (b - (rationalAdeleRealScalar a : ℂ) * Complex.I) ^
          (1 / 2 : ℂ)) ^ n) *
        (L.rationalQuadraticSpaceMatrix
          |>.rationalFiniteAdeleQuadraticGaussIntegralAt a.2) := by
  rw [rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice_eq_real_mul_finiteAt
    L hb a]
  rw [polarRealGaussianFourierProduct_zero]

end RationalQuadraticSpaceMatrix

end
