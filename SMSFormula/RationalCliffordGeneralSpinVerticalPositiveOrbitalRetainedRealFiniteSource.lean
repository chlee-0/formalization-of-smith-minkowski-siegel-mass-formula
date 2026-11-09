import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedFiniteEvaluation

/-!
# Retained real--finite Spin orbit source

The existing real Spin identity-chart source is translated into the retained
real orbit fiber.  Right invariance identifies the raw real Haar comap with
the chart-source measure.  Pairing this identity with the translated finite
block source gives the exact raw real--finite comap: its only scalar is
`spinFiniteScale * spinBlockWeight(B)`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance retainedRealSourceDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedRealSourceFiniteGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedRealSourceFiniteGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedRealSourceExceptionalSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedRealSourceExceptionalBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  Pi.borelSpace

local instance retainedRealSourceIntegralFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedRealSourceIntegralFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  Subtype.borelSpace _

local instance retainedRealSourceTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedRealSourceTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  Pi.borelSpace

/-- The existing real Spin identity-chart source, translated into the real
orbit preimage at the retained origin. -/
def retainedRealSpinSourceToOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChart.source →
      L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  fun u => u.1 *
    (x.1 : L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup)⁻¹

theorem measurableEmbedding_retainedRealSpinSourceToOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    MeasurableEmbedding (L.retainedRealSpinSourceToOrbitPreimage S x) := by
  exact (Homeomorph.mulRight
    (x.1 : L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup)⁻¹
      |>.measurableEmbedding).comp
    (MeasurableEmbedding.subtype_coe
      L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChart.open_source.measurableSet)

theorem realCliffordSpinCandidateChartGluedMeasure_comap_retainedRealSpinSource
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateChartGluedMeasure.comap
        (L.retainedRealSpinSourceToOrbitPreimage S x) =
      L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let μ := V.realCliffordSpinCandidateChartGluedMeasure
  let t : V.RealCliffordSpinCandidateGroup := x.1
  let f := Homeomorph.mulRight t
  let j := L.retainedRealSpinSourceToOrbitPreimage S x
  let i : V.realCliffordSpinCandidateIdentityChart.source →
      V.RealCliffordSpinCandidateGroup := Subtype.val
  have hf : MeasurableEmbedding f := f.measurableEmbedding
  have hj : MeasurableEmbedding j :=
    L.measurableEmbedding_retainedRealSpinSourceToOrbitPreimage S x
  have hi : MeasurableEmbedding i :=
    MeasurableEmbedding.subtype_coe
      V.realCliffordSpinCandidateIdentityChart.open_source.measurableSet
  have hsource : μ.comap i = V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
    apply hi.map_injective
    rw [map_comap_subtype_coe
      V.realCliffordSpinCandidateIdentityChart.open_source.measurableSet]
    exact V.restrict_realCliffordSpinCandidateChartGluedMeasure_identitySource
  have hmap : Measure.map f μ = μ := by
    exact MeasureTheory.map_mul_right_eq_self μ t
  have hcomap : μ.comap f = μ := by
    calc
      μ.comap f = (Measure.map f μ).comap f :=
        congrArg (fun ν : Measure _ => ν.comap f) hmap.symm
      _ = μ := hf.comap_map μ
  have hfji : f ∘ j = i := by
    funext u
    change (u.1 * t⁻¹) * t = u.1
    simp
  change μ.comap j = _
  calc
    μ.comap j = (μ.comap f).comap j :=
      congrArg (fun ν : Measure _ => ν.comap j) hcomap.symm
    _ = μ.comap (f ∘ j) := by
      rw [Measure.comap_comap hj.measurableSet_image' hf.injective hf.measurableSet_image']
    _ = μ.comap i := by rw [hfji]
    _ = _ := hsource

set_option backward.isDefEq.respectTransparency false in
/-- Pulling the raw real--finite Spin product back to the paired translated
sources preserves the real chart measure and contributes only the normalized
finite block coefficient. -/
theorem cliffordSpinCandidateRealFiniteRawMeasure_comap_retainedOrbitPreimageSources
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    (L.cliffordSpinCandidateRealFiniteRawMeasure D).comap
        (Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
          (L.retainedSpinBlockSourceToOrbitPreimage S x)) =
      V.realCliffordSpinCandidateIdentityChartSourceMeasure.prod
        ((↑D.spinFiniteScale *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) •
            V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μR := V.realCliffordSpinCandidateChartGluedMeasure
  let μF := V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure D.spinFiniteScale
  let jR := L.retainedRealSpinSourceToOrbitPreimage S x
  let jF := L.retainedSpinBlockSourceToOrbitPreimage S x
  have hjR : MeasurableEmbedding jR :=
    L.measurableEmbedding_retainedRealSpinSourceToOrbitPreimage S x
  have hjF : MeasurableEmbedding jF :=
    L.measurableEmbedding_retainedSpinBlockSourceToOrbitPreimage S x
  have hR : μR.comap jR = V.realCliffordSpinCandidateIdentityChartSourceMeasure :=
    L.realCliffordSpinCandidateChartGluedMeasure_comap_retainedRealSpinSource S x
  have hF : μF.comap jF =
      ((↑D.spinFiniteScale *
        V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) •
          V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B) :=
    L.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_comap_retainedOrbitPreimageSource
      S D.spinFiniteScale x
  letI : IsLocallyFiniteMeasure μR :=
    V.realCliffordSpinCandidateChartGluedMeasure_isLocallyFinite
  letI : SigmaFinite μR := sigmaFinite_of_locallyFinite
  letI : SigmaFinite μF := by
    unfold μF
      RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
    change SigmaFinite
      (D.spinFiniteScale • V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure)
    infer_instance
  let realSpinChart := V.realCliffordSpinCandidateIdentityChart
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe realSpinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact realSpinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite (μR.comap jR) := by
    rw [hR]
    infer_instance
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite B
  letI : IsProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability B
  letI : IsFiniteMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) := by
    infer_instance
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B) :=
    by
      unfold
        RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
      infer_instance
  let c : ℝ≥0∞ := ↑D.spinFiniteScale *
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B
  have hc : c ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_top B)
  letI : SigmaFinite
      (c • V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B) := by
    rw [← ENNReal.coe_toNNReal hc]
    change SigmaFinite
      (c.toNNReal •
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B)
    infer_instance
  letI : SigmaFinite (μF.comap jF) := by
    rw [hF]
    change SigmaFinite
      (c • V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B)
    infer_instance
  unfold cliffordSpinCandidateRealFiniteRawMeasure
  rw [Measure.comap_prodMap_cliffordSpinCandidate hjR hjF μR μF, hR, hF]

end PositiveDefiniteIntegralLattice

end
