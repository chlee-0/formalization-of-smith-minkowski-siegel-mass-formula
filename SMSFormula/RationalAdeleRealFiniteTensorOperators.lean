import SMSFormula.RationalAdeleRankOneAdelicBruhatFactorization

/-!
# Actual global generators on supplied real--finite tensors

This extends the Gaussian--lattice factorization to supplied factors,
without selecting a global test family. Fourier and phase use their actual
existing definitions. Convergence is proved for L1 input; Fourier output L1,
finite-place product assembly, Poisson and common Theta/E covariance are separate.
-/
noncomputable section
open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped FourierTransform

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The actual global Fourier integrand is L1 for every L1 test and frequency,
with its native negative sign and the existing coordinate Haar. -/
theorem integrable_rationalAdeleRankOneWeylIntegrand
    (test : (Fin n → RationalAdele) → ℂ)
    (htest : Integrable test (rationalAdeleCoordinateAddHaarMeasure n))
    (frequency : Fin n → RationalAdele) :
    Integrable (fun x ↦ rationalAdeleCoordinateFourierChar n
      (-(x * V.fullAdelicPolarMatrix.mulVec frequency)) • test x)
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  have hc : Continuous (fun x : Fin n → RationalAdele ↦
      rationalAdeleCoordinateFourierChar n (-(x * V.fullAdelicPolarMatrix.mulVec frequency))) :=
    (continuous_rationalAdeleCoordinateFourierChar n).comp (by fun_prop)
  rw [← integrable_norm_iff (hc.aestronglyMeasurable.smul htest.aestronglyMeasurable)]
  simpa only [Circle.norm_smul] using htest.norm

/-- The finite Fourier integrand is genuinely L1 under the existing finite Haar. -/
theorem integrable_rationalFiniteAdelePolarFourierIntegrand
    {test : (Fin n → RationalFiniteAdele) → ℂ}
    (htest : Integrable test (rationalFiniteAdeleCoordinateAddHaarMeasure n))
    (frequency : Fin n → RationalFiniteAdele) :
    Integrable (fun x ↦ rationalFiniteAdeleCoordinateFourierChar n
      (-(x * V.finiteAdelicPolarMatrix.mulVec frequency)) • test x)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  have hc : Continuous (fun x : Fin n → RationalFiniteAdele ↦
      rationalFiniteAdeleCoordinateFourierChar n (-(x * V.finiteAdelicPolarMatrix.mulVec frequency))) := by
    simp only [rationalFiniteAdeleCoordinateFourierChar_apply]
    apply continuous_finset_prod
    intro i hi
    apply continuous_rationalFiniteAdeleFourierChar.comp
    exact (continuous_apply i).comp
      (continuous_neg.comp (continuous_id.mul continuous_const))
  rw [← integrable_norm_iff (hc.aestronglyMeasurable.smul htest.aestronglyMeasurable)]
  simpa only [Circle.norm_smul] using htest.norm

/-- A literal finite-adelic phase parameter preserves L1 for an arbitrary finite test. -/
theorem integrable_rationalFiniteAdeleQuadraticPhaseAt_mul
    (a : RationalFiniteAdele) {test : (Fin n → RationalFiniteAdele) → ℂ}
    (htest : Integrable test (rationalFiniteAdeleCoordinateAddHaarMeasure n)) :
    Integrable (fun x ↦ (V.rationalFiniteAdeleQuadraticPhaseAt a x : ℂ) * test x)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  apply htest.bdd_mul
  · have hc : Continuous (V.rationalFiniteAdeleQuadraticPhaseAt a) := by
      unfold rationalFiniteAdeleQuadraticPhaseAt finiteAdelicQuadraticFormValue
      apply continuous_rationalFiniteAdeleFourierChar.comp
      fun_prop
    exact hc.subtype_val.aestronglyMeasurable
  · filter_upwards with x
    exact le_of_eq (Circle.norm_coe _)

/-- Both finite operations in the tensor formula have actual input convergence. -/
theorem integrable_rationalFiniteAdelePolarFourierPhaseIntegrand
    (a : RationalFiniteAdele) {test : (Fin n → RationalFiniteAdele) → ℂ}
    (htest : Integrable test (rationalFiniteAdeleCoordinateAddHaarMeasure n))
    (frequency : Fin n → RationalFiniteAdele) :
    Integrable (fun x ↦ rationalFiniteAdeleCoordinateFourierChar n
      (-(x * V.finiteAdelicPolarMatrix.mulVec frequency)) •
      ((V.rationalFiniteAdeleQuadraticPhaseAt a x : ℂ) * test x))
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
  V.integrable_rationalFiniteAdelePolarFourierIntegrand
    (V.integrable_rationalFiniteAdeleQuadraticPhaseAt_mul a htest) frequency

/-- The real factor of the phase/Fourier formula is also genuinely convergent
for an L1 real test, with the native negative Fourier kernel. -/
theorem integrable_realPolarFourierPhaseIntegrand (a : ℝ)
    {test : (Fin n → ℝ) → ℂ} (htest : Integrable test volume)
    (frequency : Fin n → ℝ) :
    Integrable (fun x ↦ realCoordinateFourierChar n
      (-(x * V.realPolarMatrix.mulVec frequency)) •
      ((Real.fourierChar (a * V.realQuadraticFormValue x) : ℂ) * test x)) volume := by
  have hp : Integrable (fun x ↦
      (Real.fourierChar (a * V.realQuadraticFormValue x) : ℂ) * test x) volume := by
    apply htest.bdd_mul
    · have hc : Continuous (fun x ↦ Real.fourierChar (a * V.realQuadraticFormValue x)) := by
        apply Real.continuous_fourierChar.comp
        unfold realQuadraticFormValue
        fun_prop
      exact hc.subtype_val.aestronglyMeasurable
    · filter_upwards with x
      exact le_of_eq (Circle.norm_coe _)
  have hc : Continuous (fun x : Fin n → ℝ ↦
      realCoordinateFourierChar n (-(x * V.realPolarMatrix.mulVec frequency))) :=
    (continuous_realCoordinateFourierChar n).comp (by fun_prop)
  rw [← integrable_norm_iff (hc.aestronglyMeasurable.smul hp.aestronglyMeasurable)]
  simpa only [Circle.norm_smul] using hp.norm

/-- The existing global Weyl operator acts on a tensor by the literal real and
finite Fourier operators. No arbitrary transformed test is introduced. -/
theorem rationalAdeleRankOneWeylOperator_realFiniteTensor
    (realTest : (Fin n → ℝ) → ℂ) (finiteTest : (Fin n → RationalFiniteAdele) → ℂ) :
    V.rationalAdeleRankOneWeylOperator
      (fun x ↦ realTest (rationalAdeleVectorRealPart n x) *
        finiteTest (rationalAdeleVectorFinitePart n x)) =
      fun y ↦ Fourier.fourierIntegral (realCoordinateFourierChar n) volume realTest
        (V.realPolarMatrix.mulVec (rationalAdeleVectorRealPart n y)) *
      Fourier.fourierIntegral (rationalFiniteAdeleCoordinateFourierChar n)
        (rationalFiniteAdeleCoordinateAddHaarMeasure n) finiteTest
        (V.finiteAdelicPolarMatrix.mulVec (rationalAdeleVectorFinitePart n y)) := by
  funext y
  exact rationalAdeleVectorPolar_fourierIntegral_realFiniteTensor V realTest finiteTest y

/-- The same supplied tensor has an explicit transformed tensor under the
actual phase operator at every adelic parameter. -/
theorem rationalAdeleRankOneUnipotentOperator_realFiniteTensor
    (a : RationalAdele) (realTest : (Fin n → ℝ) → ℂ)
    (finiteTest : (Fin n → RationalFiniteAdele) → ℂ) :
    V.rationalAdeleRankOneUnipotentOperator a
      (fun x ↦ realTest (rationalAdeleVectorRealPart n x) *
        finiteTest (rationalAdeleVectorFinitePart n x)) =
      fun x ↦ ((Real.fourierChar (rationalAdeleRealScalar a *
        V.realQuadraticFormValue (rationalAdeleVectorRealPart n x)) : ℂ) *
        realTest (rationalAdeleVectorRealPart n x)) *
        ((V.rationalFiniteAdeleQuadraticPhaseAt a.2 (rationalAdeleVectorFinitePart n x) : ℂ) *
          finiteTest (rationalAdeleVectorFinitePart n x)) := by
  funext x
  simp only [rationalAdeleRankOneUnipotentOperator,
    rationalAdeleRankOneQuadraticPhase_eq_real_mul_finiteAt]
  ring

/-- Applying the actual phase and then actual Fourier has the explicit product
of phase-twisted Fourier integrals, at every frequency. -/
theorem rationalAdeleRankOneWeylUnipotent_realFiniteTensor
    (a : RationalAdele) (realTest : (Fin n → ℝ) → ℂ)
    (finiteTest : (Fin n → RationalFiniteAdele) → ℂ)
    (y : Fin n → RationalAdele) :
    V.rationalAdeleRankOneWeylOperator
      (V.rationalAdeleRankOneUnipotentOperator a
        (fun x ↦ realTest (rationalAdeleVectorRealPart n x) *
          finiteTest (rationalAdeleVectorFinitePart n x))) y =
    Fourier.fourierIntegral (realCoordinateFourierChar n) volume
      (fun x ↦ (Real.fourierChar (rationalAdeleRealScalar a * V.realQuadraticFormValue x) : ℂ) * realTest x)
      (V.realPolarMatrix.mulVec (rationalAdeleVectorRealPart n y)) *
    Fourier.fourierIntegral (rationalFiniteAdeleCoordinateFourierChar n)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n)
      (fun x ↦ (V.rationalFiniteAdeleQuadraticPhaseAt a.2 x : ℂ) * finiteTest x)
      (V.finiteAdelicPolarMatrix.mulVec (rationalAdeleVectorFinitePart n y)) := by
  rw [rationalAdeleRankOneUnipotentOperator_realFiniteTensor]
  exact rationalAdeleVectorPolar_fourierIntegral_realFiniteTensor V
    (fun x ↦ (Real.fourierChar (rationalAdeleRealScalar a * V.realQuadraticFormValue x) : ℂ) * realTest x)
    (fun x ↦ (V.rationalFiniteAdeleQuadraticPhaseAt a.2 x : ℂ) * finiteTest x) y

/-- L1 real/finite inputs make the phase-twisted global Fourier integral genuinely
convergent. This is input convergence, not Fourier-output L1 closure. -/
theorem integrable_rationalAdeleRankOneWeylUnipotent_tensorIntegrand
    (a : RationalAdele) {realTest : (Fin n → ℝ) → ℂ}
    {finiteTest : (Fin n → RationalFiniteAdele) → ℂ}
    (hr : Integrable realTest volume)
    (hf : Integrable finiteTest (rationalFiniteAdeleCoordinateAddHaarMeasure n))
    (y : Fin n → RationalAdele) :
    Integrable (fun x ↦ rationalAdeleCoordinateFourierChar n
      (-(x * V.fullAdelicPolarMatrix.mulVec y)) •
      V.rationalAdeleRankOneUnipotentOperator a
        (fun z ↦ realTest (rationalAdeleVectorRealPart n z) *
          finiteTest (rationalAdeleVectorFinitePart n z)) x)
      (rationalAdeleCoordinateAddHaarMeasure n) :=
  V.integrable_rationalAdeleRankOneWeylIntegrand _
    (V.integrable_rationalAdeleRankOneUnipotentOperator a _
      (integrable_rationalAdeleVector_realFiniteTensor hr hf)) y

/-- On the centered Gaussian real factor, the phase/Fourier step is evaluated
at every frequency while the finite test remains arbitrary. The determinant
factor stays literally in the existing real Fourier product. -/
theorem rationalAdeleRankOneWeylUnipotent_gaussianTensor
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (a : RationalAdele)
    (finiteTest : (Fin n → RationalFiniteAdele) → ℂ) (y : Fin n → RationalAdele) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
      (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator a
        (fun x ↦ polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
          finiteTest (rationalAdeleVectorFinitePart n x))) y =
      polarRealGaussianFourierProduct L (b - (rationalAdeleRealScalar a : ℂ) * Complex.I)
        (rationalAdeleVectorRealPart n y) *
      Fourier.fourierIntegral (rationalFiniteAdeleCoordinateFourierChar n)
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)
        (fun x ↦ (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt a.2 x : ℂ) * finiteTest x)
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
          (rationalAdeleVectorFinitePart n y)) := by
  rw [rationalAdeleRankOneWeylUnipotent_realFiniteTensor]
  have hphase : (fun x ↦ (Real.fourierChar (rationalAdeleRealScalar a *
      L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : ℂ) * polarRealGaussian L b x) =
      polarRealGaussian L (b - (rationalAdeleRealScalar a : ℂ) * Complex.I) := by
    funext x
    exact realQuadraticPhase_mul_polarRealGaussian_real L b _ x
  rw [hphase, polarReal_fourierIntegral_gaussian (by simpa using hb)]

end RationalQuadraticSpaceMatrix
