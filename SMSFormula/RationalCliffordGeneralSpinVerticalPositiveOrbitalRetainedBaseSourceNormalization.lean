import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedBaseKernelSubstitution

/-!
# Normalize the retained-base raw Spin source

The translated raw real--finite Spin source appearing after retained-base
disintegration looks dependent on the horizontal origin.  Its
source-comap identity shows that this dependence is only in the embedding:
the source measure itself is a fixed normalized retained Spin source multiplied
by `spinFiniteScale * spinBlockWeight(B)`.

This file names that Spin-only source and records its product with the
differential square source.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance retainedBaseSourceNormalizationDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedBaseSourceNormalizationRealSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance retainedBaseSourceNormalizationRealSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedBaseSourceNormalizationFiniteSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedBaseSourceNormalizationFiniteSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedBaseSourceNormalizationExceptionalSigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B) :=
  L.rationalQuadraticSpaceMatrix
    |>.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite B

local instance retainedBaseSourceNormalizationTailProbability
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsProbabilityMeasure
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) :=
  L.rationalQuadraticSpaceMatrix
    |>.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability B

local instance retainedBaseSourceNormalizationTailFinite
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsFiniteMeasure
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) := by
  infer_instance

local instance retainedBaseSourceNormalizationTailSigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B) :=
  IsFiniteMeasure.toSigmaFinite _

local instance retainedBaseSourceNormalizationExceptionalTailSigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B) := by
  unfold
    RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  infer_instance

/-- The Spin-only factor of the normalized retained vertical cylinder. -/
abbrev CliffordGeneralSpinVerticalRetainedSpinSource
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  V.realCliffordSpinCandidateIdentityChart.source ×
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)

/-- The fixed normalized retained Spin source.  Its exceptional coordinate is
restricted to the identity carrier and its integral tail is the probability
source. -/
def cliffordGeneralSpinVerticalRetainedSpinSourceMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (L.CliffordGeneralSpinVerticalRetainedSpinSource S) :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  (V.realCliffordSpinCandidateIdentityChartSourceMeasure.prod
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B)).restrict
      (Set.univ ×ˢ V.retainedSpinExceptionalTailIdentityCylinder B)

/-- The raw source measure at every retained horizontal origin is the same
normalized Spin source multiplied by the unique raw finite block coefficient. -/
theorem cliffordSpinCandidateRealFiniteRawMeasure_restrict_retainedOrbitPreimage_comap_sources_eq_smul_normalized
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict
        (L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
          L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x)).comap
      (Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
        (L.retainedSpinBlockSourceToOrbitPreimage S x)) =
      ((D.spinFiniteScale : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) •
        L.cliffordGeneralSpinVerticalRetainedSpinSourceMeasure S := by
  dsimp only
  rw [L.cliffordSpinCandidateRealFiniteRawMeasure_restrict_retainedOrbitPreimage_comap_sources
    D S x]
  rw [Measure.prod_smul_right, Measure.restrict_smul]
  rfl

/-- The existing normalized cylinder source is literally differential square
source times the normalized Spin-only source. -/
theorem cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure_eq_square_prod_spinSource
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure S =
      (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure B).prod
        (L.cliffordGeneralSpinVerticalRetainedSpinSourceMeasure S) := by
  rfl

/-- The complete retained-base orbital integral has exactly the raw finite
block coefficient times the same ordered integral over the fixed normalized
Spin source.  No measurability of the definition-only good-tail lift is needed:
finiteness of the coefficient suffices to pull it through the iterated
nonnegative integrals. -/
theorem lintegral_positiveSpinOrbitalKernelRestrictIdentityChart_retainedBase_eq_block_mul_normalized
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let c : ℝ≥0∞ := (D.spinFiniteScale : ℝ≥0∞) *
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B
    let μRE :=
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure B)
    let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
    let μScalar :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
    let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S
    let ν := L.cliffordGeneralSpinVerticalRetainedSpinSourceMeasure S
    (∫⁻ b, ∫⁻ w, f w
        ∂L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S b
      ∂(RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure.restrict
        (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier B))) =
      c * ∫⁻ z, ∫⁻ q, ∫⁻ a, ∫⁻ u,
        f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
          ((z.1, z.2, a), u))
        ∂ν ∂μScalar ∂μSO ∂μRE := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let c : ℝ≥0∞ := (D.spinFiniteScale : ℝ≥0∞) *
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B
  let μRE :=
    RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
      (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure B)
  let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
  let μScalar :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
  let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S
  let ν := L.cliffordGeneralSpinVerticalRetainedSpinSourceMeasure S
  have hc : c ≠ ∞ := ENNReal.mul_ne_top (by simp)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_top B)
  rw [L.lintegral_positiveSpinOrbitalKernelRestrictIdentityChart_retainedBase_disintegration
    hr D S f hf]
  let j := fun q => Prod.map (L.retainedRealSpinSourceToOrbitPreimage S (x q))
    (L.retainedSpinBlockSourceToOrbitPreimage S (x q))
  let C := fun q => L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S (x q) ×ˢ
    L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S (x q)
  have hsource (q : V.FiniteAdelicSpecialOrthogonalIntegralTail B) :
      ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict (C q)).comap (j q) =
        c • ν := by
    exact
      L.cliffordSpinCandidateRealFiniteRawMeasure_restrict_retainedOrbitPreimage_comap_sources_eq_smul_normalized
        D S (x q)
  calc
    (∫⁻ z, ∫⁻ q, ∫⁻ a, ∫⁻ u,
        f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
          ((z.1, z.2, a), u))
        ∂((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict (C q)).comap (j q)
      ∂μScalar ∂μSO ∂μRE) =
        ∫⁻ z, ∫⁻ q, ∫⁻ a,
          c * ∫⁻ u,
            f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
              ((z.1, z.2, a), u)) ∂ν
        ∂μScalar ∂μSO ∂μRE := by
      apply lintegral_congr
      intro z
      apply lintegral_congr
      intro q
      apply lintegral_congr
      intro a
      rw [hsource q, lintegral_smul_measure]
      simp only [smul_eq_mul]
    _ = ∫⁻ z, ∫⁻ q,
          c * ∫⁻ a, ∫⁻ u,
            f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
              ((z.1, z.2, a), u)) ∂ν ∂μScalar
        ∂μSO ∂μRE := by
      apply lintegral_congr
      intro z
      apply lintegral_congr
      intro q
      exact lintegral_const_mul' c _ hc
    _ = ∫⁻ z, c * ∫⁻ q, ∫⁻ a, ∫⁻ u,
            f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
              ((z.1, z.2, a), u)) ∂ν ∂μScalar ∂μSO
        ∂μRE := by
      apply lintegral_congr
      intro z
      exact lintegral_const_mul' c _ hc
    _ = c * ∫⁻ z, ∫⁻ q, ∫⁻ a, ∫⁻ u,
          f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
            ((z.1, z.2, a), u))
        ∂ν ∂μScalar ∂μSO ∂μRE :=
      lintegral_const_mul' c _ hc

end PositiveDefiniteIntegralLattice

end
