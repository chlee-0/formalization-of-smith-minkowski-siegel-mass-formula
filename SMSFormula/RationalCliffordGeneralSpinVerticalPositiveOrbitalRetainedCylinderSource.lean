import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedRealFiniteRestriction

/-!
# The retained vertical square--Spin cylinder source

The literal differential idèle square source is paired here with the already
restricted translated real--finite Spin source.  The raw Spin block scalar is
pulled completely outside this product.  What remains is a named normalized
source whose carrier is exactly the full real Spin chart times the retained
finite identity cylinder.

This file performs only source-measure algebra.  In particular, it does not
replace the good-tail central-fiber kernel by a Cartesian presentation and
does not introduce a representative or a new chart.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance retainedCylinderSourceDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedCylinderSourceRealGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance retainedCylinderSourceRealGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedCylinderSourceFiniteGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedCylinderSourceFiniteGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedCylinderSourceExceptionalSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedCylinderSourceExceptionalBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  Pi.borelSpace

local instance retainedCylinderSourceIntegralFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedCylinderSourceIntegralFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  Subtype.borelSpace _

local instance retainedCylinderSourceTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedCylinderSourceTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  Pi.borelSpace

local instance retainedCylinderSourceExceptionalSigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B) :=
  L.rationalQuadraticSpaceMatrix
    |>.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite B

local instance retainedCylinderSourceTailProbability
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsProbabilityMeasure
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) :=
  L.rationalQuadraticSpaceMatrix
    |>.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability B

local instance retainedCylinderSourceTailFinite
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsFiniteMeasure
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) := by
  infer_instance

local instance retainedCylinderSourceTailSigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) :=
  IsFiniteMeasure.toSigmaFinite _

local instance retainedCylinderSourceExceptionalTailSigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B) := by
  unfold
    RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  infer_instance

local instance retainedCylinderSourceRealInvariantSigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    SigmaFinite L.rationalQuadraticSpaceMatrix.realInvariantDifferentialGroupMeasure :=
  PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
    L.rationalQuadraticSpaceMatrix.pairingMatrix
    L.rationalQuadraticSpaceMatrix.form_symm
    L.rationalQuadraticSpaceMatrix.form_det_ne_zero

set_option backward.isDefEq.respectTransparency false in
local instance retainedCylinderSourceRealTargetSigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    SigmaFinite
      L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartTargetMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let chart := V.realCliffordSpinCandidateIdentityChart
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
  rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartTargetMeasure,
    map_comap_subtype_coe chart.open_target.measurableSet]
  infer_instance

local instance retainedCylinderSourceRealSourceSigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    SigmaFinite
      L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let chart := V.realCliffordSpinCandidateIdentityChart
  rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure]
  exact chart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map

/-- The source type left after restricting the scalar variable to the full
square chart and the translated Spin variable to the literal retained orbit
carrier. -/
abbrev CliffordGeneralSpinVerticalRetainedCylinderSource
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource B ×
    (V.realCliffordSpinCandidateIdentityChart.source ×
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B))

/-- The normalized retained vertical source.  Its finite Spin coordinate is
still the genuine exceptional/tail source, restricted to the exact identity
cylinder; the raw block coefficient is deliberately not included. -/
def cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (L.CliffordGeneralSpinVerticalRetainedCylinderSource S) :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure B).prod
    ((V.realCliffordSpinCandidateIdentityChartSourceMeasure.prod
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B)).restrict
        (Set.univ ×ˢ V.retainedSpinExceptionalTailIdentityCylinder B))

/-- The named normalized source is literally the square source, the real Spin
chart source, the restricted exceptional Spin identity source, and the
unchanged normalized integral Spin tail. -/
theorem cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure_eq_split
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure S =
      (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure B).prod
        (V.realCliffordSpinCandidateIdentityChartSourceMeasure.prod
          (((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
              (V.retainedSpinExceptionalIdentityCarrier B)).prod
            (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B))) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μR := V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let μE := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B
  let μT := V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B
  let CE := V.retainedSpinExceptionalIdentityCarrier B
  unfold cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure
    RationalQuadraticSpaceMatrix.retainedSpinExceptionalTailIdentityCylinder
    RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  change
    (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure B).prod
        ((μR.prod (μE.prod μT)).restrict (Set.univ ×ˢ (CE ×ˢ Set.univ))) =
      (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure B).prod
        (μR.prod ((μE.restrict CE).prod μT))
  rw [← Measure.prod_restrict (μ := μR) (ν := μE.prod μT), Measure.restrict_univ]
  rw [← Measure.prod_restrict (μ := μE) (ν := μT), Measure.restrict_univ]

set_option backward.isDefEq.respectTransparency false in
/-- Pairing differential square Haar with raw Spin Haar restricted to the
literal retained orbit carrier contributes exactly the already extracted raw
finite block coefficient and no other scalar. -/
theorem rationalIdeleSquare_prod_rawSpinRestrict_comap_retainedSources
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure B).prod
      (((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict
        (L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
          L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x)).comap
        (Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
          (L.retainedSpinBlockSourceToOrbitPreimage S x))) =
      ((D.spinFiniteScale : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) •
        L.cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure S := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μR := V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let μF :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B
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
  letI : SigmaFinite μF := by
    unfold μF
      RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
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
  letI : SigmaFinite μR := by
    unfold μR
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact realSpinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  let C : Set (V.realCliffordSpinCandidateIdentityChart.source ×
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)) :=
    Set.univ ×ˢ V.retainedSpinExceptionalTailIdentityCylinder B
  letI : SigmaFinite ((μR.prod μF).restrict C) := by infer_instance
  rw [L.cliffordSpinCandidateRealFiniteRawMeasure_restrict_retainedOrbitPreimage_comap_sources
    D S x]
  rw [Measure.prod_smul_right, Measure.restrict_smul, Measure.prod_smul_right]
  unfold cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure
  rfl

end PositiveDefiniteIntegralLattice

end
