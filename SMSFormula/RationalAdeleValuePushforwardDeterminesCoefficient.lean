import SMSFormula.RationalAdeleAdelicBruhatL1Class
import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeNonnegative
import SMSFormula.RationalAdeleRankOneFiniteOnlyDilationBruhat
import SMSFormula.RationalAdeleElementaryGaussianFourier

/-!
# The value pushforward determines the adelic Bruhat coefficient

The construction of the value density is entirely about the measure `nu_Phi = map Q (Phi mu)` on the
value line.  This file proves that for a nonnegative test the coefficient sees the test only through
that measure: `A_Phi` is the Fourier--STIELTJES transform of `nu_Phi`.

The repository already had this at the polar Gaussian--lattice test
(`integral_fourierChar_rationalAdeleQuadraticValueGaussianMeasure`).  Here the test is abstracted,
and the consequences are drawn:

* two tests with the same value pushforward have the same coefficient, at every parameter;
* the total mass of the pushforward is the `lintegral` of the test, so integrability of the test is
  also a property of the pushforward alone;
* hence membership in the L1 class is, for nonnegative tests, a property of `nu_Phi` and nothing
  else.

So whether the L1 class contains a determining positive-bump space
is a question about which measures on the value line arise as value pushforwards, not about
which formulas the tests are written with.

`valuePushforward` is not a new measure: it is the existing construction with the test abstracted,
and the consistency lemma below checks that at the polar Gaussian--lattice test it is literally the
existing `rationalAdeleQuadraticValueGaussianMeasure`.

Negative scope: no disintegration, coarea kernel or fiber measure is constructed; the pushforward
is not evaluated; and nothing here says which measures occur.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The value pushforward of a nonnegative test against the coordinate Haar. -/
def valuePushforward (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) : Measure RationalAdele :=
  Measure.map V.fullAdelicQuadraticFormValue
    ((rationalAdeleCoordinateAddHaarMeasure n).withDensity Phi)

/-- The identity: the coefficient of the real test attached to a nonnegative one is the
Fourier--STIELTJES transform of its value pushforward. -/
theorem integral_fourierChar_valuePushforward (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi)
    (hfin : ∀ x, Phi x ≠ ⊤) (a : RationalAdele) :
    ∫ t, (rationalAdeleFourierChar (a * t) : ℂ) ∂(V.valuePushforward Phi) =
      V.rationalAdeleRankOneAdelicBruhatCoefficient
        (fun x ↦ (((Phi x).toReal : ℝ) : ℂ)) a := by
  have hchar : AEStronglyMeasurable
      (fun t : RationalAdele ↦ ((rationalAdeleFourierChar (a * t) : Circle) : ℂ))
      (V.valuePushforward Phi) :=
    (continuous_rationalAdeleFourierChar.comp
      (continuous_const.mul continuous_id)).subtype_val.aestronglyMeasurable
  rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral, valuePushforward,
    integral_map V.continuous_fullAdelicQuadraticFormValue.measurable.aemeasurable hchar,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall fun x ↦ lt_top_iff_ne_top.mpr (hfin x))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  show ((Phi x).toReal : ℝ) • ((rationalAdeleFourierChar
      (a * V.fullAdelicQuadraticFormValue x) : Circle) : ℂ) = _
  rw [Complex.real_smul]
  rfl

/-- Equal pushforwards give equal coefficients. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_eq_of_valuePushforward_eq
    (V : RationalQuadraticSpaceMatrix n)
    {Phi Psi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hPhi : Measurable Phi) (hPhifin : ∀ x, Phi x ≠ ⊤)
    (hPsi : Measurable Psi) (hPsifin : ∀ x, Psi x ≠ ⊤)
    (hpush : V.valuePushforward Phi = V.valuePushforward Psi) :
    V.rationalAdeleRankOneAdelicBruhatCoefficient (fun x ↦ (((Phi x).toReal : ℝ) : ℂ)) =
      V.rationalAdeleRankOneAdelicBruhatCoefficient
        (fun x ↦ (((Psi x).toReal : ℝ) : ℂ)) := by
  funext a
  rw [← V.integral_fourierChar_valuePushforward hPhi hPhifin a,
    ← V.integral_fourierChar_valuePushforward hPsi hPsifin a, hpush]

/-- The total mass of the pushforward is the `lintegral` of the test. -/
theorem valuePushforward_univ (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) :
    V.valuePushforward Phi Set.univ =
      ∫⁻ x, Phi x ∂(rationalAdeleCoordinateAddHaarMeasure n) := by
  rw [valuePushforward,
    Measure.map_apply V.continuous_fullAdelicQuadraticFormValue.measurable MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- A finite pushforward makes the attached complex test integrable. -/
theorem integrable_toReal_of_valuePushforward_ne_top (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi)
    (hmass : V.valuePushforward Phi Set.univ ≠ ⊤) :
    Integrable (fun x ↦ (((Phi x).toReal : ℝ) : ℂ))
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  rw [V.valuePushforward_univ hmeas] at hmass
  exact (integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hmass).ofReal

/-- Conversely, integrability of the attached test makes the pushforward finite. -/
theorem valuePushforward_ne_top_of_integrable_toReal (V : RationalQuadraticSpaceMatrix n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞} (hmeas : Measurable Phi) (hfin : ∀ x, Phi x ≠ ⊤)
    (hint : Integrable (fun x ↦ (((Phi x).toReal : ℝ) : ℂ))
      (rationalAdeleCoordinateAddHaarMeasure n)) :
    V.valuePushforward Phi Set.univ ≠ ⊤ := by
  rw [V.valuePushforward_univ hmeas]
  have hnorm : ∀ x, ‖(((Phi x).toReal : ℝ) : ℂ)‖ₑ = Phi x := by
    intro x
    have hstep : ‖(((Phi x).toReal : ℝ) : ℂ)‖ = (Phi x).toReal := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [← ofReal_norm_eq_enorm, hstep, ENNReal.ofReal_toReal (hfin x)]
  have := hint.hasFiniteIntegral
  rw [HasFiniteIntegral] at this
  simp only [hnorm] at this
  exact this.ne

/-- The conclusion: for nonnegative tests, membership in the L1 class is a property of the value
pushforward and of nothing else. -/
theorem isAdelicBruhatL1_of_valuePushforward_eq (V : RationalQuadraticSpaceMatrix n)
    {Phi Psi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hPhi : Measurable Phi) (hPhifin : ∀ x, Phi x ≠ ⊤)
    (hPsi : Measurable Psi) (hPsifin : ∀ x, Psi x ≠ ⊤)
    (hpush : V.valuePushforward Phi = V.valuePushforward Psi)
    (hmem : V.IsAdelicBruhatL1 (fun x ↦ (((Phi x).toReal : ℝ) : ℂ))) :
    V.IsAdelicBruhatL1 (fun x ↦ (((Psi x).toReal : ℝ) : ℂ)) := by
  refine ⟨?_, ?_⟩
  · refine V.integrable_toReal_of_valuePushforward_ne_top hPsi ?_
    rw [← hpush]
    exact V.valuePushforward_ne_top_of_integrable_toReal hPhi hPhifin hmem.1
  · rw [← V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_of_valuePushforward_eq
      hPhi hPhifin hPsi hPsifin hpush]
    exact hmem.2

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {rank : ℕ}

end PositiveDefiniteIntegralLattice

end
