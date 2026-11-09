import SMSFormula.RationalCliffordGeneralSpinVerticalFiberKernelDescent

/-!
# Binding translated vertical Spin fibers over rational idele classes

The descended vertical Spin kernel can be bound directly against the
independently chosen rational idele-class Haar measure.  The resulting measure
lives on the rational adelic `GSpin` quotient.  Its measurable-set and
nonnegative-integral formulas involve the translated raw Spin fibers,
and its logarithmic cutoff integral is exactly the
vertical crossed integral.

Only pointwise s-finiteness of the descended fibers is used.  No uniform
`IsSFiniteKernel` instance, measurable representative, comparison with the
common horizontal quotient, or ambient Haar scalar is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2000000

/-- Bind the genuine idele-class-indexed vertical Spin fibers against the
independently selected rational idele-class Haar measure. -/
noncomputable def verticalSpinFiberHaarBoundMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Measure.bind rationalIdeleClassHaarMeasure
    (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj)

/-- The vertical bound measure of a measurable set is the idele-class Haar
integral of the literal translated Spin-fiber masses. -/
theorem verticalSpinFiberHaarBoundMeasure_apply
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    {s : Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient}
    (hs : MeasurableSet s) :
    D.verticalSpinFiberHaarBoundMeasure L hn hsurj s =
      ∫⁻ c : RationalIdeleClassGroup,
        D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj c s
          ∂rationalIdeleClassHaarMeasure := by
  rw [verticalSpinFiberHaarBoundMeasure,
    Measure.bind_apply hs
      (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj).aemeasurable]
  rfl

/-- Full nonnegative measurable-integrand formula for the class-Haar bind of
the translated vertical Spin fibers. -/
theorem lintegral_verticalSpinFiberHaarBoundMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f :
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient →
        ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z, f z ∂D.verticalSpinFiberHaarBoundMeasure L hn hsurj =
      ∫⁻ c : RationalIdeleClassGroup,
        ∫⁻ z, f z
          ∂D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj c
        ∂rationalIdeleClassHaarMeasure := by
  rw [verticalSpinFiberHaarBoundMeasure,
    Measure.lintegral_bind
      (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj).aemeasurable
      hf.aemeasurable]
  rfl

/-- Integrating a logarithmic cutoff against the vertical bound
measure is definitionally the vertical crossed
integral. -/
theorem verticalSpinFiberHaarBoundMeasure_lintegral_logCutoff
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
          z)
      ∂D.verticalSpinFiberHaarBoundMeasure L hn hsurj =
      D.verticalCrossedLogCutoffLIntegral
        L.rationalQuadraticSpaceMatrix hsurj f := by
  change
    ∫⁻ z,
        (f ∘
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule)
          z ∂D.verticalSpinFiberHaarBoundMeasure L hn hsurj = _
  rw [D.lintegral_verticalSpinFiberHaarBoundMeasure L hn hsurj _
    (hf.comp
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable)]
  rfl

/-- The bound logarithmic cutoff therefore has the already proved product
formula: common idele cutoff times literal raw Spin quotient mass. -/
theorem verticalSpinFiberHaarBoundMeasure_lintegral_logCutoff_eq
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
          z)
      ∂D.verticalSpinFiberHaarBoundMeasure L hn hsurj =
      rationalIdeleClassLogCutoffLIntegral f *
        D.spinTamagawaNumberENNReal := by
  rw [D.verticalSpinFiberHaarBoundMeasure_lintegral_logCutoff L hn hsurj f hf,
    D.verticalCrossedLogCutoffLIntegral_eq
      L.rationalQuadraticSpaceMatrix hsurj f hf]

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
