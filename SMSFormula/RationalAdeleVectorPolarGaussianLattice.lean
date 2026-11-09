import SMSFormula.RationalAdeleVectorPolarGaussian
import SMSFormula.RationalFiniteAdeleVectorPolarDualLattice
import SMSFormula.RationalAdeleCoordinateElementaryFourier
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Full rational-adelic polar Gaussian--lattice Fourier transform

This file canonically splits the native vector carrier
`Fin n → RationalAdele` into its real and finite coordinate vectors.  The
split is the existing real--finite product together with the repository's
fixed infinite-adelic equivalence to `ℝ`; Mathlib's
`arrowProdEquivProdArrow` proves that it carries the normalized coordinate
Haar to the literal real/finite product measure.

Fubini then combines the determinant-normalized real polar Gaussian with the
finite standard-lattice indicator.  The exact polar Fourier integral has the
reciprocal real determinant scale and support on the intrinsic finite
`C`-dual lattice.  This is a Fourier-transform statement only: rational
lattice Poisson summation still requires the separate Euclidean
positive-definite matrix/lattice theorem.  No chosen chart, inverse matrix,
shell decomposition, orbital distribution, or Tamagawa-number assertion is
introduced.
-/

noncomputable section

open MeasureTheory

open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

/-- Real coordinates of a native rational-adelic vector, using the existing
canonical infinite-adelic equivalence to `ℝ`. -/
def rationalAdeleVectorRealPart (d : ℕ) (x : Fin d → RationalAdele) :
    Fin d → ℝ :=
  fun i => rationalInfiniteAdeleContinuousAddEquivReal (x i).1

/-- Finite coordinates of a native rational-adelic vector. -/
def rationalAdeleVectorFinitePart (d : ℕ) (x : Fin d → RationalAdele) :
    Fin d → RationalFiniteAdele :=
  fun i => (x i).2

/-- Canonical measurable real--finite split of the native vector carrier. -/
noncomputable def rationalAdeleVectorRealFiniteEquiv (d : ℕ) :
    (Fin d → RationalAdele) ≃ᵐ
      (Fin d → ℝ) × (Fin d → RationalFiniteAdele) :=
  (MeasurableEquiv.arrowProdEquivProdArrow
    RationalInfiniteAdele RationalFiniteAdele (Fin d)).trans
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.piCongrRight fun _ : Fin d =>
          rationalInfiniteAdeleContinuousAddEquivReal.toHomeomorph.toMeasurableEquiv)
        (MeasurableEquiv.refl (Fin d → RationalFiniteAdele)))

@[simp]
theorem rationalAdeleVectorRealFiniteEquiv_apply
    (d : ℕ) (x : Fin d → RationalAdele) :
    rationalAdeleVectorRealFiniteEquiv d x =
      (rationalAdeleVectorRealPart d x, rationalAdeleVectorFinitePart d x) :=
  rfl

/-- The canonical vector split sends the existing normalized coordinate Haar
to standard real coordinate volume times literal finite product Haar. -/
theorem measurePreserving_rationalAdeleVectorRealFiniteSplit (d : ℕ) :
    MeasurePreserving (rationalAdeleVectorRealFiniteEquiv d)
      (rationalAdeleCoordinateAddHaarMeasure d)
      ((volume : Measure (Fin d → ℝ)).prod
        (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure d)) := by
  letI : SigmaFinite
      (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure d) := by
    rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  have hinf : MeasurePreserving rationalInfiniteAdeleContinuousAddEquivReal
      rationalInfiniteAdeleAddHaarMeasure (volume : Measure ℝ) :=
    ⟨rationalInfiniteAdeleContinuousAddEquivReal.measurable,
      rationalInfiniteAdeleAddHaarMeasure_map_eq_volume⟩
  have hinfPi : MeasurePreserving
      (fun x : Fin d → RationalInfiniteAdele =>
        fun i => rationalInfiniteAdeleContinuousAddEquivReal (x i))
      (Measure.pi (fun _ : Fin d => rationalInfiniteAdeleAddHaarMeasure))
      (volume : Measure (Fin d → ℝ)) := by
    rw [volume_pi]
    exact measurePreserving_pi
      (fun _ : Fin d => rationalInfiniteAdeleAddHaarMeasure)
      (fun _ : Fin d => (volume : Measure ℝ))
      (fun _ => hinf)
  have hfinite : MeasurePreserving
      (id : (Fin d → RationalFiniteAdele) → (Fin d → RationalFiniteAdele))
      (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure d)
      (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure d) :=
    MeasurePreserving.id _
  have hsplit := measurePreserving_arrowProdEquivProdArrow
    RationalInfiniteAdele RationalFiniteAdele (Fin d)
    (fun _ : Fin d => rationalInfiniteAdeleAddHaarMeasure)
    (fun _ : Fin d => rationalFiniteAdeleAddHaarMeasure)
  have hprod := hinfPi.prod hfinite
  have hcomp := hprod.comp hsplit
  rw [rationalAdeleCoordinateAddHaarMeasure_eq_pi]
  simp_rw [rationalAdeleAddHaarMeasure_eq_prod]
  simpa [rationalAdeleVectorRealFiniteEquiv, Function.comp_def,
    rationalAdeleVectorRealPart, rationalAdeleVectorFinitePart,
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure]
    using hcomp

/-! ## Compatibility with the global polar frequency and character -/

theorem rationalAdeleVectorRealPart_fullAdelicPolarMatrix_mulVec
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (y : Fin n → RationalAdele) :
    rationalAdeleVectorRealPart n (V.fullAdelicPolarMatrix.mulVec y) =
      V.realPolarMatrix.mulVec (rationalAdeleVectorRealPart n y) := by
  funext i
  let h : RationalAdele →+* ℝ :=
    rationalInfiniteAdeleRingEquivReal.toRingHom.comp
      (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
  change h (∑ j, algebraMap ℚ RationalAdele (V.polarMatrix i j) * y j) =
    ∑ j, (V.polarMatrix i j : ℝ) * h (y j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_mul]
  congr 1
  exact rationalInfiniteAdeleContinuousAddEquivReal_algebraMap _

theorem rationalAdeleVectorFinitePart_fullAdelicPolarMatrix_mulVec
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (y : Fin n → RationalAdele) :
    rationalAdeleVectorFinitePart n (V.fullAdelicPolarMatrix.mulVec y) =
      V.finiteAdelicPolarMatrix.mulVec (rationalAdeleVectorFinitePart n y) := by
  funext i
  let h : RationalAdele →+* RationalFiniteAdele :=
    RingHom.snd RationalInfiniteAdele RationalFiniteAdele
  change h (∑ j, algebraMap ℚ RationalAdele (V.polarMatrix i j) * y j) =
    ∑ j, algebraMap ℚ RationalFiniteAdele (V.polarMatrix i j) * h (y j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp [h]

theorem rationalAdeleCoordinateFourierChar_eq_real_mul_finite
    (d : ℕ) (x : Fin d → RationalAdele) :
    rationalAdeleCoordinateFourierChar d x =
      realCoordinateFourierChar d (rationalAdeleVectorRealPart d x) *
        RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateFourierChar d
          (rationalAdeleVectorFinitePart d x) := by
  simp only [rationalAdeleCoordinateFourierChar_apply,
    rationalAdeleFourierChar_apply,
    rationalAdeleArchimedeanFourierChar_apply,
    realCoordinateFourierChar,
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateFourierChar_apply,
    rationalAdeleVectorFinitePart]
  change (∏ i, Real.fourierChar
      (rationalInfiniteAdeleContinuousAddEquivReal (x i).1) *
        rationalFiniteAdeleFourierChar (x i).2) =
    (∏ i, Real.fourierChar
      (rationalInfiniteAdeleContinuousAddEquivReal (x i).1)) *
      ∏ i, rationalFiniteAdeleFourierChar (x i).2
  rw [Finset.prod_mul_distrib]

theorem rationalAdeleVectorRealPart_neg_mul
    (d : ℕ) (x y : Fin d → RationalAdele) :
    rationalAdeleVectorRealPart d (-(x * y)) =
      -(rationalAdeleVectorRealPart d x * rationalAdeleVectorRealPart d y) := by
  funext i
  change rationalInfiniteAdeleRingEquivReal (-((x i).1 * (y i).1)) =
    -(rationalInfiniteAdeleRingEquivReal (x i).1 *
      rationalInfiniteAdeleRingEquivReal (y i).1)
  simp

theorem rationalAdeleVectorFinitePart_neg_mul
    (d : ℕ) (x y : Fin d → RationalAdele) :
    rationalAdeleVectorFinitePart d (-(x * y)) =
      -(rationalAdeleVectorFinitePart d x * rationalAdeleVectorFinitePart d y) := by
  funext i
  rfl

/-- The full test is the positive-definite real polar Gaussian times the
indicator of the standard finite coordinate lattice. -/
def rationalAdeleVectorPolarGaussianLatticeTest
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    (x : Fin n → RationalAdele) : ℂ :=
  polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator
      (rationalAdeleVectorFinitePart n x)

theorem integrable_rationalFiniteAdeleVectorIntegralIndicator (d : ℕ) :
    Integrable
      (RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator :
        (Fin d → RationalFiniteAdele) → ℂ)
      (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure d) := by
  rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure]
  exact Integrable.fintype_prod (ι := Fin d) fun _ =>
    integrable_rationalFiniteAdeleIntegralIndicator

/-- Integrable real and finite factors give an integrable test on the native
adelic carrier and coordinate Haar. No new test-family choice is made. -/
theorem integrable_rationalAdeleVector_realFiniteTensor {n : ℕ}
    {realTest : (Fin n → ℝ) → ℂ} {finiteTest : (Fin n → RationalFiniteAdele) → ℂ}
    (hr : Integrable realTest volume)
    (hf : Integrable finiteTest
      (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure n)) :
    Integrable (fun x ↦ realTest (rationalAdeleVectorRealPart n x) *
      finiteTest (rationalAdeleVectorFinitePart n x))
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  have hg := hr.mul_prod hf
  have hcomp := ((measurePreserving_rationalAdeleVectorRealFiniteSplit n).integrable_comp
    hg.aestronglyMeasurable).2 hg
  simpa [Function.comp_def] using hcomp

/-- The full native Gaussian--lattice test is integrable for the existing
coordinate Haar. -/
theorem integrable_rationalAdeleVectorPolarGaussianLatticeTest
    {n : ℕ} {b : ℂ} (hb : 0 < b.re) (L : PositiveDefiniteIntegralLattice n) :
    Integrable (rationalAdeleVectorPolarGaussianLatticeTest L b)
      (rationalAdeleCoordinateAddHaarMeasure n) :=
  integrable_rationalAdeleVector_realFiniteTensor
    (integrable_polarRealGaussian hb L) (integrable_rationalFiniteAdeleVectorIntegralIndicator n)

/-- The exact expected Fourier value: reciprocal real determinant scale times
the standard Gaussian Fourier product, supported on the intrinsic polar-dual
finite lattice. -/
noncomputable def rationalAdeleVectorPolarGaussianLatticeFourierProduct
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    (y : Fin n → RationalAdele) : ℂ :=
  polarRealGaussianFourierProduct L b (rationalAdeleVectorRealPart n y) *
    L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator
      (rationalAdeleVectorFinitePart n y)

/-- Exact integral-level real--finite tensor Fourier compatibility on the
split and Haars. This identity of Bochner integrals alone makes no convergence
claim; integrable factors have genuine convergence by the separate L1 theorem. -/
theorem rationalAdeleVectorPolar_fourierIntegral_realFiniteTensor
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (realTest : (Fin n → ℝ) → ℂ) (finiteTest : (Fin n → RationalFiniteAdele) → ℂ)
    (y : Fin n → RationalAdele) :
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
      (rationalAdeleCoordinateAddHaarMeasure n)
      (fun x ↦ realTest (rationalAdeleVectorRealPart n x) *
        finiteTest (rationalAdeleVectorFinitePart n x))
      (V.fullAdelicPolarMatrix.mulVec y) =
    Fourier.fourierIntegral (realCoordinateFourierChar n) volume realTest
      (V.realPolarMatrix.mulVec (rationalAdeleVectorRealPart n y)) *
    Fourier.fourierIntegral (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateFourierChar n)
      (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure n) finiteTest
      (V.finiteAdelicPolarMatrix.mulVec (rationalAdeleVectorFinitePart n y)) := by
  letI : SigmaFinite
      (RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  rw [Fourier.fourierIntegral_def]
  let wr := rationalAdeleVectorRealPart n y
  let wf := rationalAdeleVectorFinitePart n y
  let gr : (Fin n → ℝ) → ℂ := fun x =>
    realCoordinateFourierChar n
        (-(x * V.realPolarMatrix.mulVec wr)) •
      realTest x
  let gf : (Fin n → RationalFiniteAdele) → ℂ := fun x =>
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateFourierChar n
        (-(x * V.finiteAdelicPolarMatrix.mulVec wf)) •
      finiteTest x
  let g : (Fin n → ℝ) × (Fin n → RationalFiniteAdele) → ℂ :=
    fun z => gr z.1 * gf z.2
  have hintegrand :
      (fun v : Fin n → RationalAdele =>
        rationalAdeleCoordinateFourierChar n
            (-(v * V.fullAdelicPolarMatrix.mulVec y)) •
          (realTest (rationalAdeleVectorRealPart n v) * finiteTest (rationalAdeleVectorFinitePart n v))) =
      fun v => g (rationalAdeleVectorRealFiniteEquiv n v) := by
    funext v
    rw [rationalAdeleCoordinateFourierChar_eq_real_mul_finite]
    rw [rationalAdeleVectorRealPart_neg_mul,
      rationalAdeleVectorFinitePart_neg_mul,
      rationalAdeleVectorRealPart_fullAdelicPolarMatrix_mulVec,
      rationalAdeleVectorFinitePart_fullAdelicPolarMatrix_mulVec]
    simp only [rationalAdeleVectorRealFiniteEquiv_apply, g, gr, gf,
      Circle.smul_def, smul_eq_mul, Circle.coe_mul]
    ring
  rw [hintegrand]
  rw [(measurePreserving_rationalAdeleVectorRealFiniteSplit n).integral_comp' g]
  rw [MeasureTheory.integral_prod_mul]
  rw [← Fourier.fourierIntegral_def, ← Fourier.fourierIntegral_def]

/-- Exact full polar Fourier formula on the native rational-adelic vector
carrier.  The reciprocal determinant scale is contained literally in
`polarRealGaussianFourierProduct`; the finite Haar is not rescaled. -/
theorem rationalAdeleVectorPolar_fourierIntegral_gaussianLattice
    {n : ℕ} {b : ℂ} (hb : 0 < b.re) (L : PositiveDefiniteIntegralLattice n)
    (y : Fin n → RationalAdele) :
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
        (rationalAdeleCoordinateAddHaarMeasure n)
        (rationalAdeleVectorPolarGaussianLatticeTest L b)
        (L.rationalQuadraticSpaceMatrix.fullAdelicPolarMatrix.mulVec y) =
      rationalAdeleVectorPolarGaussianLatticeFourierProduct L b y := by
  change Fourier.fourierIntegral _ _
    (fun x ↦ polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator
        (rationalAdeleVectorFinitePart n x)) _ = _
  rw [rationalAdeleVectorPolar_fourierIntegral_realFiniteTensor,
    polarReal_fourierIntegral_gaussian hb,
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorPolar_fourierIntegral_integralIndicator]
  rfl

end PositiveDefiniteIntegralLattice
