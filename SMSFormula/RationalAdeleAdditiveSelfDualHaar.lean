import SMSFormula.RationalFiniteAdeleAdditiveCharacter
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The standard self-dual additive normalization on the rational adeles

This file records the exact bilinear kernel attached to the already fixed
global additive character and certifies the finite Haar scale by one explicit
Fourier transform.  The everywhere-integral finite adeles are their own
annihilator, and their indicator is fixed by the finite Fourier integral when
that compact open has volume one.

Together with `rationalAdeleAddHaarMeasure_eq_prod`, this is the elementary
normalization statement needed before constructing adelic Poisson tests.  No
abstract Pontryagin-dual or self-dual-Haar interface is introduced.
-/

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

/-! ## The exact bilinear kernel -/

/-- The multiplicative bilinear kernel built from the fixed global additive
character. -/
def rationalAdeleFourierKernel
    (x y : RationalAdele) : Circle :=
  rationalAdeleFourierChar (x * y)

/-- The global bilinear kernel is jointly continuous. -/
theorem continuous_uncurry_rationalAdeleFourierKernel :
    Continuous (Function.uncurry rationalAdeleFourierKernel) := by
  exact continuous_rationalAdeleFourierChar.comp
    (continuous_fst.mul continuous_snd)

/-! ## The finite standard lattice -/

/-- The complex-valued indicator of the everywhere-integral finite adeles. -/
def rationalFiniteAdeleIntegralIndicator
    (x : RationalFiniteAdele) : ℂ :=
  (integralFiniteAdeleSubring : Set RationalFiniteAdele).indicator
    (fun _ => 1) x

@[simp]
theorem rationalFiniteAdeleIntegralIndicator_of_mem
    {x : RationalFiniteAdele}
    (hx : x ∈ integralFiniteAdeleSubring) :
    rationalFiniteAdeleIntegralIndicator x = 1 := by
  simp [rationalFiniteAdeleIntegralIndicator, hx]

@[simp]
theorem rationalFiniteAdeleIntegralIndicator_of_not_mem
    {x : RationalFiniteAdele}
    (hx : x ∉ integralFiniteAdeleSubring) :
    rationalFiniteAdeleIntegralIndicator x = 0 := by
  simp [rationalFiniteAdeleIntegralIndicator, hx]

/-- Translation by an integral finite adele fixes the standard indicator. -/
theorem rationalFiniteAdeleIntegralIndicator_add_of_mem
    (x u : RationalFiniteAdele)
    (hu : u ∈ integralFiniteAdeleSubring) :
    rationalFiniteAdeleIntegralIndicator (x + u) =
      rationalFiniteAdeleIntegralIndicator x := by
  have hmem : x + u ∈ integralFiniteAdeleSubring ↔
      x ∈ integralFiniteAdeleSubring := by
    constructor
    · intro hxu
      simpa using integralFiniteAdeleSubring.sub_mem hxu hu
    · intro hx
      exact integralFiniteAdeleSubring.add_mem hx hu
  by_cases hx : x ∈ integralFiniteAdeleSubring
  · have hxu : x + u ∈ integralFiniteAdeleSubring := hmem.mpr hx
    simp [rationalFiniteAdeleIntegralIndicator, hx, hxu]
  · have hxu : x + u ∉ integralFiniteAdeleSubring :=
      fun h => hx (hmem.mp h)
    simp [rationalFiniteAdeleIntegralIndicator, hx, hxu]

/-- The finite character annihilator of the standard integral lattice is
exactly that lattice. -/
theorem rationalFiniteAdele_integral_annihilator_iff
    (y : RationalFiniteAdele) :
    (∀ x : RationalFiniteAdele,
      x ∈ integralFiniteAdeleSubring →
        rationalFiniteAdeleFourierChar (x * y) = 1) ↔
      y ∈ integralFiniteAdeleSubring := by
  constructor
  · intro h
    have hy := h 1 integralFiniteAdeleSubring.one_mem
    have hy' : rationalFiniteAdeleFourierChar y = 1 := by
      simpa only [one_mul] using hy
    exact (rationalFiniteAdeleFourierChar_eq_one_iff y).mp hy'
  · intro hy x hx
    apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
    exact integralFiniteAdeleSubring.mul_mem hx hy

/-- The standard finite-lattice indicator is integrable for the normalized
finite Haar measure. -/
theorem integrable_rationalFiniteAdeleIntegralIndicator :
    Integrable rationalFiniteAdeleIntegralIndicator
      rationalFiniteAdeleAddHaarMeasure := by
  refine (integrableOn_const (C := (1 : ℂ)) ?_).integrable_indicator ?_
  · simp
  · exact isOpen_integralFiniteAdeleSubring.measurableSet

/-! ## The finite self-dual Fourier certificate -/

/-- At an integral frequency, the Fourier integral of the standard finite
lattice indicator is one. -/
theorem rationalFiniteAdele_fourierIntegral_integralIndicator_of_mem
    (w : RationalFiniteAdele)
    (hw : w ∈ integralFiniteAdeleSubring) :
    Fourier.fourierIntegral rationalFiniteAdeleFourierChar
        rationalFiniteAdeleAddHaarMeasure
        rationalFiniteAdeleIntegralIndicator w = 1 := by
  rw [Fourier.fourierIntegral_def]
  have hintegrand :
      (fun v : RationalFiniteAdele =>
        rationalFiniteAdeleFourierChar (-(v * w)) •
          rationalFiniteAdeleIntegralIndicator v) =
        rationalFiniteAdeleIntegralIndicator := by
    funext v
    by_cases hv : v ∈ integralFiniteAdeleSubring
    · have hvw : -(v * w) ∈ integralFiniteAdeleSubring :=
        integralFiniteAdeleSubring.neg_mem
          (integralFiniteAdeleSubring.mul_mem hv hw)
      rw [rationalFiniteAdeleFourierChar_eq_one_of_mem_integral _ hvw]
      simp
    · simp [rationalFiniteAdeleIntegralIndicator_of_not_mem hv]
  rw [hintegrand]
  change (∫ v : RationalFiniteAdele,
      (integralFiniteAdeleSubring : Set RationalFiniteAdele).indicator
        (fun _ => (1 : ℂ)) v ∂rationalFiniteAdeleAddHaarMeasure) = 1
  rw [integral_indicator_const (1 : ℂ)
    isOpen_integralFiniteAdeleSubring.measurableSet]
  simp [measureReal_def, rationalFiniteAdeleAddHaarMeasure_integral]

/-- At a nonintegral frequency, translation by one forces the Fourier
integral of the standard finite-lattice indicator to vanish. -/
theorem rationalFiniteAdele_fourierIntegral_integralIndicator_of_not_mem
    (w : RationalFiniteAdele)
    (hw : w ∉ integralFiniteAdeleSubring) :
    Fourier.fourierIntegral rationalFiniteAdeleFourierChar
        rationalFiniteAdeleAddHaarMeasure
        rationalFiniteAdeleIntegralIndicator w = 0 := by
  have htranslate :
      rationalFiniteAdeleIntegralIndicator ∘
          (fun v : RationalFiniteAdele => v + 1) =
        rationalFiniteAdeleIntegralIndicator := by
    funext v
    exact rationalFiniteAdeleIntegralIndicator_add_of_mem v 1
      integralFiniteAdeleSubring.one_mem
  have hfourier := congrFun
    (Fourier.fourierIntegral_comp_add_right
      rationalFiniteAdeleFourierChar
      rationalFiniteAdeleAddHaarMeasure
      rationalFiniteAdeleIntegralIndicator (1 : RationalFiniteAdele)) w
  rw [htranslate] at hfourier
  simp only [one_mul, Circle.smul_def] at hfourier
  have hchar : rationalFiniteAdeleFourierChar w ≠ 1 := by
    intro h
    exact hw (rationalFiniteAdeleFourierChar_eq_one_iff w |>.mp h)
  have hcharCoe : (rationalFiniteAdeleFourierChar w : ℂ) ≠ 1 := by
    intro h
    exact hchar (Circle.ext (by simpa using h))
  have hzero :
      (1 - (rationalFiniteAdeleFourierChar w : ℂ)) *
          Fourier.fourierIntegral rationalFiniteAdeleFourierChar
            rationalFiniteAdeleAddHaarMeasure
            rationalFiniteAdeleIntegralIndicator w = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    exact hfourier
  exact (mul_eq_zero.mp hzero).resolve_left
    (sub_ne_zero.mpr hcharCoe.symm)

/-- With the compact-open volume fixed to one, the finite Fourier transform
of the standard integral-lattice indicator is literally the same indicator. -/
@[simp]
theorem rationalFiniteAdele_fourierIntegral_integralIndicator
    (w : RationalFiniteAdele) :
    Fourier.fourierIntegral rationalFiniteAdeleFourierChar
        rationalFiniteAdeleAddHaarMeasure
        rationalFiniteAdeleIntegralIndicator w =
      rationalFiniteAdeleIntegralIndicator w := by
  by_cases hw : w ∈ integralFiniteAdeleSubring
  · rw [rationalFiniteAdele_fourierIntegral_integralIndicator_of_mem w hw,
      rationalFiniteAdeleIntegralIndicator_of_mem hw]
  · rw [rationalFiniteAdele_fourierIntegral_integralIndicator_of_not_mem w hw,
      rationalFiniteAdeleIntegralIndicator_of_not_mem hw]

end PositiveDefiniteIntegralLattice
