import SMSFormula.SpecialOrthogonalAdelicDifferentialNormalizationCertificate
import SMSFormula.SpecialOrthogonalRationalAdelicDifferentialHaar
import SMSFormula.SpecialOrthogonalFullAdelicDifferentialHaar

/-!
# Ambient-only differential normalization on the rational adelic carrier

The sound Weil datum fixes a quotient measure as well as the ambient Haar
measure.  The present module separates the ambient normalization from that
quotient construction.

The compact-open normalization set is the inverse carrier image of the
identity coset of the concrete real/unrestricted, finite/integral stabilizer.
Its mass is the literal real differential mass times the finite differential
stabilizer volume.  This finite nonzero mass proves that the ambient
normalization certificate is rigid under scalar rescaling.

No quotient measure, fundamental domain, genus mass, Tamagawa value, or
reference Haar measure occurs in the certificate.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The chosen identity coset of the concrete compact-open real/finite
stabilizer. -/
def fullAdelicRealFiniteLatticeStabilizerIdentityCoset
    (L : PositiveDefiniteIntegralLattice n) :
    Set L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  L.fullAdelicRealFiniteLatticeStabilizerCoset
    ((1 : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
      L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)

/-- The compact-open normalization set on the general rational
quadratic-space carrier. -/
def rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
    (L : PositiveDefiniteIntegralLattice n) :
    Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm ''
    L.fullAdelicRealFiniteLatticeStabilizerIdentityCoset

@[simp]
theorem
    preimage_rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
    (L : PositiveDefiniteIntegralLattice n) :
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm ⁻¹'
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet =
      L.fullAdelicRealFiniteLatticeStabilizerIdentityCoset := by
  ext g
  simp [
    rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
  ]

/-- The general-carrier normalization set is open. -/
theorem
    isOpen_rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
    (L : PositiveDefiniteIntegralLattice n) :
    IsOpen
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet := by
  apply
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm.toHomeomorph.isOpenMap
  exact
    L.isOpen_fullAdelicRealFiniteLatticeStabilizerCoset
      ((1 : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
        L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)

/-- The general-carrier normalization set is measurable. -/
theorem
    measurableSet_rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSet
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet :=
  L.isOpen_rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet.measurableSet

/-- The general-carrier normalization set is compact. -/
theorem
    isCompact_rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
    (L : PositiveDefiniteIntegralLattice n) :
    IsCompact
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet := by
  exact
    (L.isCompact_fullAdelicRealFiniteLatticeStabilizerCoset
      ((1 : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
        L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)).image
      (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm.continuous

/-- The compact-open normalization set has the exact internally constructed
real-times-finite differential mass. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_normalizationSet
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  rw [
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure,
    Measure.map_apply
      (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm.measurable
      L.measurableSet_rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
  ]
  change
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        ((L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm ⁻¹'
          L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet) =
      _
  rw [
    L.preimage_rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
  ]
  exact
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_coset_eq_real_mul_finite
      hP
      ((1 : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
        L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)

/-- The compact-open normalization set has nonzero differential mass. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_normalizationSet_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet ≠
      0 := by
  rw [
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_normalizationSet
      hP
  ]
  exact mul_ne_zero
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero P)

/-- The compact-open normalization set has finite differential mass. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_normalizationSet_ne_top
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet ≠
      ⊤ := by
  rw [
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_normalizationSet
      hP
  ]
  exact ENNReal.mul_ne_top
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_top
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_top hP)

/-- Ambient-only evidence that a measure on the general rational adelic
carrier is the measure assembled from the fixed invariant differential.

This proposition deliberately contains no quotient datum, fundamental
domain, double-coset finiteness assumption, genus mass, or Tamagawa value. -/
structure
    RationalQuadraticSpaceMatrixFullAdelicAmbientDifferentialNormalizationCertificate
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] (P : ℝ)
    (μ :
      Measure
        L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    Prop where
  measure_eq :
    μ = L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P
  tangentCoordinateMeasure_eq :
    L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentCoordinateMeasure =
      Measure.map
        L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentCoordinateContinuousLinearEquiv
        L.rationalQuadraticSpaceMatrix.invariantDifferentialAdeleCoordinateNormalization.measure
  tangentStandardParallelotope_eq_one :
    L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentCoordinateMeasure
        L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentStandardParallelotope =
      1
  finiteInverseVolumeProduct_tendsto :
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
        P)

namespace
  RationalQuadraticSpaceMatrixFullAdelicAmbientDifferentialNormalizationCertificate

/-- An actual cutoff convergence certificate produces the ambient-only
differential normalization certificate. -/
def of_massLocalInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] {P : ℝ}
    (hconv : massLocalInverseProductTendsTo L P) :
    RationalQuadraticSpaceMatrixFullAdelicAmbientDifferentialNormalizationCertificate
      L P (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P) :=
  { measure_eq := rfl
    tangentCoordinateMeasure_eq :=
      L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentCoordinateMeasure_eq_map_continuousLinearEquiv
    tangentStandardParallelotope_eq_one :=
      L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentCoordinateMeasure_standardParallelotope
    finiteInverseVolumeProduct_tendsto :=
      L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo_finiteStabilizerInverseVolume_of_massLocalInverseProductTendsTo
        hconv }

/-- The ambient differential normalization excludes every nontrivial scalar
rescaling.  The proof uses the finite nonzero mass of the compact-open
normalization set rather than any quotient volume. -/
theorem smul_normalized_iff
    {L : PositiveDefiniteIntegralLattice n} [NeZero n]
    {P : ℝ} (hP : 0 < P)
    {μ :
      Measure
        L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup}
    (C :
      RationalQuadraticSpaceMatrixFullAdelicAmbientDifferentialNormalizationCertificate
        L P μ)
    (c : ℝ≥0∞) :
    RationalQuadraticSpaceMatrixFullAdelicAmbientDifferentialNormalizationCertificate
        L P (c • μ) ↔
      c = 1 := by
  constructor
  · intro Cc
    have hmeasure : c • μ = μ :=
      Cc.measure_eq.trans C.measure_eq.symm
    have hmass := congrArg
      (fun ν :
        Measure
          L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup =>
        ν L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet)
      hmeasure
    change
      (c • μ)
          L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet =
        μ L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
      at hmass
    rw [Measure.smul_apply, smul_eq_mul] at hmass
    let m :=
      μ L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
    have hm0 : m ≠ 0 := by
      change
        μ L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet ≠
          0
      rw [C.measure_eq]
      exact
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_normalizationSet_ne_zero
          hP
    have hmtop : m ≠ ⊤ := by
      change
        μ L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet ≠
          ⊤
      rw [C.measure_eq]
      exact
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_normalizationSet_ne_top
          hP
    change c * m = m at hmass
    calc
      c = c * (m * m⁻¹) := by
        rw [ENNReal.mul_inv_cancel hm0 hmtop, mul_one]
      _ = (c * m) * m⁻¹ := by ac_rfl
      _ = m * m⁻¹ := by rw [hmass]
      _ = 1 := ENNReal.mul_inv_cancel hm0 hmtop
  · rintro rfl
    simpa using C

end
  RationalQuadraticSpaceMatrixFullAdelicAmbientDifferentialNormalizationCertificate

end PositiveDefiniteIntegralLattice
