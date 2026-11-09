import SMSFormula.RationalAdeleValuePushforwardDensity

/-!
# The value density is a positive linear functional

The abstract Riesz layer (`CoareaRieszInvariance`) -- the invariance transfer, the support
statement, and the local bound -- applies to the value-density map once it is a positive linear
functional. This file supplies the linearity and the positivity in the repository's own
objects, at a fixed adelic value.

The complex-test density is the Fourier transform of the adelic Bruhat coefficient, exactly as in
the nonnegative case but with the test complex from the start, so that linearity can be stated at
all. On the `L1` class it is additive -- the coefficient is additive there, and the Fourier
integral is additive on integrable functions -- and it is homogeneous with no hypothesis, because
the coefficient already is and the Fourier integral is linear.

At a fixed value the real part is therefore an additive, homogeneous, real-valued map on the class,
and it is nonnegative on the tests coming from nonnegative ones -- that last fact is the existing
rank-free nonnegativity theorem, restated here as the positivity half.

What this is and is not.  It is the positive linear functional property, for the value density, in
the repository's own terms.  It is not a `C_c` functional on a shell: the domain here is the
adelic `L1` class, not compactly supported continuous functions on `X_a`, and producing the latter
is the coarea construction itself, which is not done here.  So the abstract Riesz layer does not
apply directly -- this file gives linearity and sign only.

Negative scope: no fiber measure is constructed, no `C_c` space is exhibited, nothing is evaluated,
and the additivity genuinely needs class membership on both summands -- a Fourier integral of a
non-integrable function is zero, so dropping it would make the statement vacuous rather than false.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The value density of a complex test: the Fourier transform of its adelic Bruhat coefficient.
For a test of the form `toComplexTest Phi` this is the existing `valueFourierDensity`. -/
def complexValueFourierDensity (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) : RationalAdele → ℂ :=
  Fourier.fourierIntegral rationalAdeleFourierChar rationalAdeleAddHaarMeasure
    (V.rationalAdeleRankOneAdelicBruhatCoefficient Phi)

theorem complexValueFourierDensity_toComplexTest (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) :
    V.complexValueFourierDensity (toComplexTest Phi) = V.valueFourierDensity Phi := rfl

/-- Additivity on the `L1` class: the coefficient is additive there, and the Fourier integral is
additive on integrable functions. -/
theorem complexValueFourierDensity_add (V : RationalQuadraticSpaceMatrix n)
    {Phi Psi : (Fin n → RationalAdele) → ℂ} (hPhi : V.IsAdelicBruhatL1 Phi)
    (hPsi : V.IsAdelicBruhatL1 Psi) :
    V.complexValueFourierDensity (Phi + Psi) =
      V.complexValueFourierDensity Phi + V.complexValueFourierDensity Psi := by
  have hmul : Continuous fun pair : RationalAdele × RationalAdele ↦ pair.1 * pair.2 := by fun_prop
  unfold complexValueFourierDensity
  rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_add hPhi.1 hPsi.1]
  exact VectorFourier.fourierIntegral_add continuous_rationalAdeleFourierChar hmul hPhi.2 hPsi.2

/-- Homogeneity, with no hypothesis: the coefficient is already homogeneous and the Fourier integral
is linear. -/
theorem complexValueFourierDensity_const_smul (V : RationalQuadraticSpaceMatrix n) (c : ℂ)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.complexValueFourierDensity (c • Phi) = c • V.complexValueFourierDensity Phi := by
  unfold complexValueFourierDensity
  rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_const_smul]
  exact Fourier.fourierIntegral_const_smul rationalAdeleFourierChar rationalAdeleAddHaarMeasure _ c

/-- At a fixed value the real part is additive on the class. -/
theorem re_complexValueFourierDensity_add (V : RationalQuadraticSpaceMatrix n)
    {Phi Psi : (Fin n → RationalAdele) → ℂ} (hPhi : V.IsAdelicBruhatL1 Phi)
    (hPsi : V.IsAdelicBruhatL1 Psi) (value : RationalAdele) :
    (V.complexValueFourierDensity (Phi + Psi) value).re =
      (V.complexValueFourierDensity Phi value).re +
        (V.complexValueFourierDensity Psi value).re := by
  rw [V.complexValueFourierDensity_add hPhi hPsi]
  simp

/-- At a fixed value the real part is homogeneous for real scalars, with no hypothesis. -/
theorem re_complexValueFourierDensity_real_smul (V : RationalQuadraticSpaceMatrix n) (c : ℝ)
    (Phi : (Fin n → RationalAdele) → ℂ) (value : RationalAdele) :
    (V.complexValueFourierDensity ((c : ℂ) • Phi) value).re =
      c * (V.complexValueFourierDensity Phi value).re := by
  rw [V.complexValueFourierDensity_const_smul]
  simp

/-- Positivity: at every adelic value the real part is nonnegative on the tests coming from
nonnegative ones.  This is the existing rank-free nonnegativity theorem, restated as the positivity
half of the positive-linear-functional property. -/
theorem re_complexValueFourierDensity_nonneg (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hclass : V.IsAdelicBruhatL1 (toComplexTest Phi)) (value : RationalAdele) :
    0 ≤ (V.complexValueFourierDensity (toComplexTest Phi) value).re :=
  (V.valueFourierDensity_real_nonnegative hmeas hfin hclass value).2

end RationalQuadraticSpaceMatrix
