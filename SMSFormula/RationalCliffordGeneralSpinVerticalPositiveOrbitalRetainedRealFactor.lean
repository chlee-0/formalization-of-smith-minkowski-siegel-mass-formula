import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedOriginPreimage
import SMSFormula.RationalCliffordSpinCandidatePlacewiseUnimodular

/-!
# Evaluation of the retained real Spin-orbit factor

On the retained identity branch, the inverse image of the real `GSpin`
central-fiber chart under the intrinsic Spin embedding is exactly the
real Spin identity-chart source.  Thus the retained real orbital factor is a
right-translation preimage of that source, and right invariance of the raw
real Spin Haar measure evaluates its mass with coefficient one.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The identity square branch removes the possible central scalar `-1`, so
the real Spin embedding sees precisely the retained Spin identity source. -/
theorem preimage_cliffordSpinCandidateToCliffordGeneralSpinHom_realCentralFiberIdentityChart :
    V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ ⁻¹'
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source =
      V.realCliffordSpinCandidateIdentityChart.source := by
  ext s
  constructor
  · intro hs
    change V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ s ∈
      V.realCliffordGeneralSpinCentralSpinIdentityChart.target at hs
    rcases hs with ⟨p, hp, hps⟩
    have hsq : p.1 ^ 2 = (1 : ℝˣ) := by
      simpa using congrArg
        (fun z : V.RealCliffordGeneralSpinGroup => z.similitude) hps
    have hcases : p.1 = 1 ∨ p.1 = -1 := by
      apply Rat.eq_one_or_neg_one_of_unitSquareMonoidHom_real_eq_one p.1
      simpa [Rat.unitSquareMonoidHom] using hsq
    have hpone : p.1 = 1 := by
      rcases hcases with h | h
      · exact h
      · exfalso
        exact Rat.neg_one_not_mem_unitSquareIdentityChart_source ℝ (h ▸ hp.1)
    have hspin : p.2 = s := by
      apply V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective ℝ
      simpa [RationalQuadraticSpaceMatrix.cliffordGeneralSpinCentralSpinMultiplication,
        hpone] using hps
    simpa [hspin] using hp.2
  · intro hs
    change V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ s ∈
      V.realCliffordGeneralSpinCentralSpinIdentityChart.target
    refine ⟨(1, s), ⟨Rat.one_mem_unitSquareIdentityChart_source ℝ, hs⟩, ?_⟩
    simp [RationalQuadraticSpaceMatrix.cliffordGeneralSpinCentralSpinMultiplication]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance retainedRealFactorDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-- The retained real orbital factor is the right-translation preimage of the
real Spin identity-chart source. -/
theorem cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage_eq_preimage_mul
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x =
      (fun y : L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup =>
        y * x.1) ⁻¹'
          L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChart.source := by
  let V := L.rationalQuadraticSpaceMatrix
  ext y
  change V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ y *
      V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ x.1 ∈
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source ↔
      y * x.1 ∈ V.realCliffordSpinCandidateIdentityChart.source
  rw [← map_mul]
  exact Set.ext_iff.mp
    (V.preimage_cliffordSpinCandidateToCliffordGeneralSpinHom_realCentralFiberIdentityChart)
    (y * x.1)

/-- Right invariance evaluates the retained real orbital factor with no
additional scalar. -/
theorem realCliffordSpinCandidateChartGluedMeasure_retainedRealSpinOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateChartGluedMeasure
        (L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x) =
      L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateChartGluedMeasure
        L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChart.source := by
  rw [L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage_eq_preimage_mul S x]
  let V := L.rationalQuadraticSpaceMatrix
  let μ := V.realCliffordSpinCandidateChartGluedMeasure
  let rightMul := fun y : V.RealCliffordSpinCandidateGroup => y * x.1
  have hright : Measurable rightMul :=
    (continuous_id.mul continuous_const).measurable
  have hmap : Measure.map rightMul μ = μ := by
    exact MeasureTheory.map_mul_right_eq_self μ x.1
  have hsource := congrArg
    (fun ν : Measure V.RealCliffordSpinCandidateGroup =>
      ν V.realCliffordSpinCandidateIdentityChart.source) hmap
  change (Measure.map rightMul μ)
      V.realCliffordSpinCandidateIdentityChart.source =
    μ V.realCliffordSpinCandidateIdentityChart.source at hsource
  rw [Measure.map_apply hright
    V.realCliffordSpinCandidateIdentityChart.open_source.measurableSet] at hsource
  exact hsource

/-- After evaluation of the real factor, the retained orbital-kernel mass is
the real Spin identity-chart mass times the still-explicit finite factor. -/
theorem positiveSpinOrbitalKernel_fullSOChartGSpinOrigin_identityChart_eq_realSpin_mul_finite
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let g := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
    L.positiveSpinOrbitalKernel hr D
        (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g)
        (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E) =
      V.realCliffordSpinCandidateChartGluedMeasure
          V.realCliffordSpinCandidateIdentityChart.source *
        V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
          D.spinFiniteScale
          (L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x) := by
  dsimp only
  rw [L.positiveSpinOrbitalKernel_fullSOChartGSpinOrigin_identityChart hr D S x]
  rw [L.realCliffordSpinCandidateChartGluedMeasure_retainedRealSpinOrbitPreimage S x]

end PositiveDefiniteIntegralLattice

end
