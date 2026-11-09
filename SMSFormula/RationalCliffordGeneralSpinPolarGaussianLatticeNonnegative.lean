import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeSummability
import SMSFormula.RationalCliffordGeneralSpinAllRationalThetaCalibration

/-!
# The nonnegative polar Gaussian--lattice test

For a real scale, the existing complex polar Gaussian--lattice test is
pointwise a nonnegative real number.  This file records its literal
`ENNReal` norm, proves measurability through the existing real--finite adelic
split, and identifies the complex test with the finite real coercion of that
nonnegative test.

This is the exact bridge from the concrete rank-one Fourier test to the
already calibrated nonnegative quotient-theta measure identities.  It adds
no test class, quotient section, measure normalization, complement, or
presentation.
-/

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The existing finite standard-lattice indicator is measurable on the
literal finite adelic vector carrier. -/
theorem measurable_rationalFiniteAdeleVectorIntegralIndicator (d : ℕ) :
    Measurable
      (RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator :
        (Fin d → RationalFiniteAdele) → ℂ) := by
  unfold RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator
  apply Finset.measurable_prod
  intro i _hi
  unfold rationalFiniteAdeleIntegralIndicator
  exact (measurable_const.indicator
    isOpen_integralFiniteAdeleSubring.measurableSet).comp (measurable_pi_apply i)

/-- The real polar Gaussian is measurable for every complex scale. -/
theorem measurable_polarRealGaussian
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    Measurable (polarRealGaussian L b) := by
  unfold polarRealGaussian
  exact (continuous_realCoordinateGaussian n b).measurable.comp
    (Matrix.toLin' L.polarRealSqrtMatrix).continuous_of_finiteDimensional.measurable

/-- The concrete polar Gaussian--lattice test is measurable on the actual
full rational-adelic vector carrier. -/
theorem measurable_rationalAdeleVectorPolarGaussianLatticeTest
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    Measurable (rationalAdeleVectorPolarGaussianLatticeTest L b) := by
  let split := rationalAdeleVectorRealFiniteEquiv n
  let f : (Fin n → ℝ) × (Fin n → RationalFiniteAdele) → ℂ := fun z =>
    polarRealGaussian L b z.1 *
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator z.2
  have hf : Measurable f :=
    ((L.measurable_polarRealGaussian b).comp measurable_fst).mul
      ((measurable_rationalFiniteAdeleVectorIntegralIndicator n).comp measurable_snd)
  simpa [f, split, rationalAdeleVectorPolarGaussianLatticeTest] using
    hf.comp split.measurable

/-- At a real scale, the complex polar Gaussian is literally the coercion of
its positive real exponential. -/
theorem polarRealGaussian_ofReal
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (x : Fin n → ℝ) :
    polarRealGaussian L (a : ℂ) x =
      (Real.exp (-Real.pi * a *
        dotProduct (L.polarRealSqrtMatrix.mulVec x)
          (L.polarRealSqrtMatrix.mulVec x)) : ℂ) := by
  rw [polarRealGaussian, realCoordinateGaussian_eq_exp_dotProduct]
  rw [Complex.ofReal_exp]
  congr 1
  norm_cast

/-- At a real scale, the full complex test is a nonnegative real number and
therefore equals the real coercion of its complex norm. -/
theorem rationalAdeleVectorPolarGaussianLatticeTest_ofReal_eq_coe_norm
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) x =
      (‖rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) x‖ : ℂ) := by
  by_cases hx : rationalAdeleVectorFinitePart n x ∈
      integralFiniteAdeleVectors n
  · rw [rationalAdeleVectorPolarGaussianLatticeTest,
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_mem hx,
      mul_one, L.polarRealGaussian_ofReal]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · rw [rationalAdeleVectorPolarGaussianLatticeTest,
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx,
      mul_zero, norm_zero, Complex.ofReal_zero]

/-- The literal nonnegative version of the existing concrete complex test.
It is its `ENNReal` norm, not a second test-function choice. -/
def rationalAdeleVectorPolarGaussianLatticeTestENNReal
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (x : Fin n → RationalAdele) : ℝ≥0∞ :=
  ENNReal.ofReal
    ‖rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) x‖

/-- The nonnegative concrete test is measurable. -/
theorem measurable_rationalAdeleVectorPolarGaussianLatticeTestENNReal
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) :
    Measurable (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) := by
  exact
    (L.measurable_rationalAdeleVectorPolarGaussianLatticeTest (a : ℂ)).norm.ennreal_ofReal

/-- Every pointwise value of the nonnegative concrete test is finite. -/
theorem rationalAdeleVectorPolarGaussianLatticeTestENNReal_ne_top
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianLatticeTestENNReal L a x ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top

/-- The original complex test is exactly the complex coercion of the finite
real value of its nonnegative version. -/
theorem rationalAdeleVectorPolarGaussianLatticeTestENNReal_toReal
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (x : Fin n → RationalAdele) :
    ((rationalAdeleVectorPolarGaussianLatticeTestENNReal L a x).toReal : ℂ) =
      rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) x := by
  rw [rationalAdeleVectorPolarGaussianLatticeTestENNReal,
    ENNReal.toReal_ofReal (norm_nonneg _)]
  exact
    (L.rationalAdeleVectorPolarGaussianLatticeTest_ofReal_eq_coe_norm a x).symm

/-- A summable family of values of the complex concrete test gives a finite
`ENNReal` sum of the corresponding nonnegative test values. -/
theorem tsum_rationalAdeleVectorPolarGaussianLatticeTestENNReal_ne_top
    {ι : Type*} (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (y : ι → (Fin n → RationalAdele))
    (h : Summable (fun i ↦
      rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) (y i))) :
    (∑' i,
      rationalAdeleVectorPolarGaussianLatticeTestENNReal L a (y i)) ≠ ⊤ := by
  let fc : ι → ℂ := fun i ↦
    rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) (y i)
  let fr : ι → ℝ := fun i ↦ ‖fc i‖
  have hr : Summable fr := by simpa [fr, fc] using h.norm
  have hsum := ENNReal.ofReal_tsum_of_nonneg
    (fun i ↦ norm_nonneg (fc i)) hr
  change (∑' i, ENNReal.ofReal (fr i)) ≠ ⊤
  rw [← hsum]
  exact ENNReal.ofReal_ne_top

/-- Under the same exact summability condition, the complex sum is literally
the complex coercion of the real value of the nonnegative `ENNReal` sum. -/
theorem tsum_rationalAdeleVectorPolarGaussianLatticeTestENNReal_toReal
    {ι : Type*} (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (y : ι → (Fin n → RationalAdele))
    (h : Summable (fun i ↦
      rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) (y i))) :
    (((∑' i,
      rationalAdeleVectorPolarGaussianLatticeTestENNReal L a (y i)).toReal : ℝ) : ℂ) =
      ∑' i, rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) (y i) := by
  let fc : ι → ℂ := fun i ↦
    rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) (y i)
  let fr : ι → ℝ := fun i ↦ ‖fc i‖
  have hr : Summable fr := by simpa [fr, fc] using h.norm
  have hsum := ENNReal.ofReal_tsum_of_nonneg
    (fun i ↦ norm_nonneg (fc i)) hr
  have hcomplex : ((∑' i, fr i : ℝ) : ℂ) = ∑' i, fc i := by
    change Complex.ofRealCLM (∑' i, fr i) = ∑' i, fc i
    rw [Complex.ofRealCLM.map_tsum hr]
    apply tsum_congr
    intro i
    exact
      (L.rationalAdeleVectorPolarGaussianLatticeTest_ofReal_eq_coe_norm
        a (y i)).symm
  change ((∑' i, ENNReal.ofReal (fr i)).toReal : ℂ) = ∑' i, fc i
  rw [← hsum, ENNReal.toReal_ofReal
    (tsum_nonneg fun i ↦ norm_nonneg (fc i))]
  exact hcomplex

/-- The ordinary concrete nonnegative theta is finite at every actual
full-adelic `GSpin` point. -/
theorem fullAdelicCliffordGeneralSpinPolarGaussianLatticeTheta_ne_top
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinTheta
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) g ≠ ⊤ := by
  let V := L.rationalQuadraticSpaceMatrix
  simpa [RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinTheta,
    RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand,
    V] using
    L.tsum_rationalAdeleVectorPolarGaussianLatticeTestENNReal_ne_top a
      (fun x : Fin n → ℚ ↦
        V.fullAdelicCliffordGeneralSpinRationalVectorAction g x)
      (by
        simpa [V] using
          L.summable_rationalAdeleVectorPolarGaussianLatticeTest_fullAdelicCliffordGeneralSpin
            ha g)

/-- The complex ordinary concrete theta is exactly the coercion of the real
value of its finite nonnegative theta. -/
theorem fullAdelicCliffordGeneralSpinPolarGaussianLatticeTheta_toReal
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    ((L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinTheta
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) g).toReal : ℂ) =
      ∑' x : Fin n → ℚ,
        rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
          (L.rationalQuadraticSpaceMatrix
            |>.fullAdelicCliffordGeneralSpinRationalVectorAction g x) := by
  let V := L.rationalQuadraticSpaceMatrix
  simpa [RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinTheta,
    RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand,
    V] using
    L.tsum_rationalAdeleVectorPolarGaussianLatticeTestENNReal_toReal a
      (fun x : Fin n → ℚ ↦
        V.fullAdelicCliffordGeneralSpinRationalVectorAction g x)
      (by
        simpa [V] using
          L.summable_rationalAdeleVectorPolarGaussianLatticeTest_fullAdelicCliffordGeneralSpin
            ha g)

/-- The represented-norm concrete nonnegative theta is finite at every actual
full-adelic `GSpin` point. -/
theorem fullAdelicCliffordGeneralSpinPolarGaussianLatticeRepresentedNormTheta_ne_top
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    (L.rationalQuadraticSpaceMatrix
      |>.fullAdelicCliffordGeneralSpinRepresentedNormTheta b
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) g) ≠ ⊤ := by
  let V := L.rationalQuadraticSpaceMatrix
  have hAll :=
    L.summable_rationalAdeleVectorPolarGaussianLatticeTest_fullAdelicCliffordGeneralSpin
      ha g
  have hFiber : Summable (fun x : b.rationalVectorFiber V ↦
      rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
        (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x.1)) := by
    simpa [Function.comp_def] using hAll.comp_injective Subtype.val_injective
  simpa [RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRepresentedNormTheta,
    RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand,
    V] using
    L.tsum_rationalAdeleVectorPolarGaussianLatticeTestENNReal_ne_top a
      (fun x : b.rationalVectorFiber V ↦
        V.fullAdelicCliffordGeneralSpinRationalVectorAction g x.1) hFiber

/-- On every represented norm fiber, the complex theta is exactly the
coercion of the finite nonnegative theta's real value. -/
theorem fullAdelicCliffordGeneralSpinPolarGaussianLatticeRepresentedNormTheta_toReal
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    ((L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinRepresentedNormTheta b
          (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) g).toReal : ℂ) =
      (L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinComplexRepresentedNormTheta b
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) g) := by
  let V := L.rationalQuadraticSpaceMatrix
  have hAll :=
    L.summable_rationalAdeleVectorPolarGaussianLatticeTest_fullAdelicCliffordGeneralSpin
      ha g
  have hFiber : Summable (fun x : b.rationalVectorFiber V ↦
      rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
        (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x.1)) := by
    simpa [Function.comp_def] using hAll.comp_injective Subtype.val_injective
  simpa [RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRepresentedNormTheta,
    RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand,
    RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexRepresentedNormTheta,
    RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand,
    V] using
    L.tsum_rationalAdeleVectorPolarGaussianLatticeTestENNReal_toReal a
      (fun x : b.rationalVectorFiber V ↦
        V.fullAdelicCliffordGeneralSpinRationalVectorAction g x.1) hFiber

/-- The finite nonnegative represented-norm theta remains finite after its
section-free descent to the existing `GSpin` quotient. -/
theorem fullAdelicCliffordGeneralSpinPolarGaussianLatticeRepresentedNormThetaOnLeftQuotient_ne_top
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (Z : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient) :
    (L.rationalQuadraticSpaceMatrix
      |>.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient b
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) Z) ≠ ⊤ := by
  induction Z using Quot.inductionOn with
  | _ g =>
      exact
        L.fullAdelicCliffordGeneralSpinPolarGaussianLatticeRepresentedNormTheta_ne_top
          ha b g

/-- The complex/nonnegative represented-norm identification descends
section-freely to the existing `GSpin` quotient. -/
theorem fullAdelicCliffordGeneralSpinPolarGaussianLatticeRepresentedNormThetaOnLeftQuotient_toReal
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (Z : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient) :
    ((L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient b
          (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) Z).toReal : ℂ) =
      (L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinComplexRepresentedNormThetaOnLeftQuotient b
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) Z) := by
  induction Z using Quot.inductionOn with
  | _ g =>
      exact
        L.fullAdelicCliffordGeneralSpinPolarGaussianLatticeRepresentedNormTheta_toReal
          ha b g

end PositiveDefiniteIntegralLattice

end
