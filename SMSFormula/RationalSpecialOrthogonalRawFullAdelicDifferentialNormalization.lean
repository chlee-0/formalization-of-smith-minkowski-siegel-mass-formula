import SMSFormula.RationalSpecialOrthogonalLatticeGeneralDifferentialMeasureComparison
import SMSFormula.SpecialOrthogonalAdelicAmbientDifferentialNormalization

/-!
# Raw full-adelic invariant-differential normalization

The finite restricted-product Haar measure constructed for an arbitrary
rational quadratic space gives every integral local factor probability mass
one.  A raw rational invariant differential therefore also needs the global
finite scale supplied by the convergent product of the literal local
differential volumes.

This module records that scale carrier-independently.  It relates a
full-adelic measure simultaneously to the rational tangent-coordinate
normalization, the raw real differential factor, the raw local p-adic volume
product, and the probability-normalized finite restricted-product factor.
No quotient measure, Tamagawa value, genus mass, local density, or reference
Haar measure occurs.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped BigOperators ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The literal invariant-differential volume of the integral local factor,
indexed directly by the subtype of rational primes. -/
def padicInvariantDifferentialIntegralVolumeAtPrime
    (V : RationalQuadraticSpaceMatrix n)
    (q : {p : ℕ // Nat.Prime p}) : ℝ≥0∞ :=
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  V.padicInvariantDifferentialGroupMeasure q.1
    ((localPadicIntegralMatrixUnitsSubgroup q.1 n).comap
        ((formPreservingMatrixSubgroup
            (V.pairingMatrix.map (algebraMap ℚ ℚ_[q.1]))).subtype.comp
          (specialFormPreservingMatrixSubgroup
            (V.pairingMatrix.map (algebraMap ℚ ℚ_[q.1]))).subtype) :
      Set (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[q.1]))))

/-- For a lattice form, the carrier-independent integral local volume is
the corrected differential stabilizer volume of the lattice. -/
theorem padicInvariantDifferentialIntegralVolumeAtPrime_eq_lattice
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    (L.rationalQuadraticSpaceMatrix
        |>.padicInvariantDifferentialIntegralVolumeAtPrime q) =
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold padicInvariantDifferentialIntegralVolumeAtPrime
  unfold PositiveDefiniteIntegralLattice.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime
  unfold PositiveDefiniteIntegralLattice.localPadicSpecialOrthogonalDifferentialStabilizerVolume
  unfold padicInvariantDifferentialGroupMeasure
  unfold PositiveDefiniteIntegralLattice.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
  simp only [PositiveDefiniteIntegralLattice.rationalQuadraticSpaceMatrix_pairingMatrix] <;> rfl

/-- The inverse product of the literal integral local differential volumes
over the rational primes bounded by `N`. -/
def padicInvariantDifferentialIntegralInverseVolumePartialProduct
    (V : RationalQuadraticSpaceMatrix n) (N : ℕ) : ℝ≥0∞ :=
  (∏ q ∈ rationalPrimesUpTo N,
    V.padicInvariantDifferentialIntegralVolumeAtPrime q)⁻¹

/-- Convergence of the carrier-independent raw local inverse-volume products. -/
def PadicInvariantDifferentialIntegralInverseVolumeProductTendsTo
    (V : RationalQuadraticSpaceMatrix n) (a : ℝ≥0∞) : Prop :=
  Filter.Tendsto
    (fun N : ℕ ↦
      V.padicInvariantDifferentialIntegralInverseVolumePartialProduct N)
    Filter.atTop (nhds a)

/-- On a lattice form, every carrier-independent inverse-volume cutoff is
the lattice cutoff product. -/
theorem padicInvariantDifferentialIntegralInverseVolumePartialProduct_eq_lattice
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) :
    (L.rationalQuadraticSpaceMatrix
        |>.padicInvariantDifferentialIntegralInverseVolumePartialProduct N) =
      L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
        N := by
  unfold padicInvariantDifferentialIntegralInverseVolumePartialProduct
  unfold
    PositiveDefiniteIntegralLattice.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
  congr 1

/-- On a lattice form, carrier-independent raw convergence is exactly the
lattice differential convergence predicate. -/
theorem padicInvariantDifferentialIntegralInverseVolumeProductTendsTo_iff_lattice
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ≥0∞) :
    (L.rationalQuadraticSpaceMatrix
        |>.PadicInvariantDifferentialIntegralInverseVolumeProductTendsTo a) ↔
      L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo
        a := by
  unfold PadicInvariantDifferentialIntegralInverseVolumeProductTendsTo
  unfold
    PositiveDefiniteIntegralLattice.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo
  simp only [
    padicInvariantDifferentialIntegralInverseVolumePartialProduct_eq_lattice]

local instance rawNormalizationRealMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.RealSpecialOrthogonalGroup :=
  V.fullAdelicDifferentialProductRealCarrierMeasurableSpace

local instance rawNormalizationRealUnderlyingMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  V.fullAdelicDifferentialProductRealMeasurableSpace

local instance rawNormalizationFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  V.fullAdelicDifferentialProductFiniteMeasurableSpace

/-- Carrier-independent evidence that a full-adelic Haar measure has the
raw scale of the single rational invariant top differential.

The finite restricted-product factor is the already constructed
probability-normalized Haar.  The field `finiteScale` restores the raw scale;
its inverse is required to be the limit of the finite products of the
p-adic integral volumes.  Thus the placewise raw measures and the
finite factor are connected rather than recorded independently. -/
structure IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale
    (V : RationalQuadraticSpaceMatrix n)
    (finiteScale : ℝ≥0∞)
    (mu : Measure V.FullAdelicSpecialOrthogonalGroup) : Prop where
  finiteScale_ne_zero : finiteScale ≠ 0
  finiteScale_ne_top : finiteScale ≠ ⊤
  inverseVolumeProduct_tendsto :
    V.PadicInvariantDifferentialIntegralInverseVolumeProductTendsTo
      finiteScale⁻¹
  tangentCoordinateMeasure_eq :
    V.fullAdelicSkewAdjointTangentCoordinateMeasure =
      Measure.map
        V.fullAdelicSkewAdjointTangentCoordinateContinuousLinearEquiv
        V.invariantDifferentialAdeleCoordinateNormalization.measure
  tangentStandardParallelotope_eq_one :
    V.fullAdelicSkewAdjointTangentCoordinateMeasure
        V.fullAdelicSkewAdjointTangentStandardParallelotope =
      1
  map_realFinite_eq :
    Measure.map
        V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toHomeomorph
        mu =
      V.realInvariantDifferentialGroupMeasure.prod
        (finiteScale • V.finiteAdelicInvariantDifferentialGroupMeasure)
  ne_zero : mu ≠ 0
  sigmaFinite : SigmaFinite mu
  isHaarMeasure : Measure.IsHaarMeasure mu
  isMulLeftInvariant : Measure.IsMulLeftInvariant mu
  regular : Measure.Regular mu

/-- A full-adelic measure has the raw rational invariant-differential
normalization when it has some positive finite scale certified by the raw
local inverse-volume product. -/
def IsRawInvariantDifferentialFullAdelicGroupMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (mu : Measure V.FullAdelicSpecialOrthogonalGroup) : Prop :=
  ∃ finiteScale : ℝ≥0∞,
    V.IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale finiteScale mu

namespace IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale

/-- The lattice ambient normalization certificate supplies the corrected raw
carrier-independent interface with the literal finite stabilizer-volume
scale. -/
def of_latticeAmbientCertificate
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    {P : ℝ} (hP : 0 < P)
    {mu :
      Measure
        L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup}
    (C :
      PositiveDefiniteIntegralLattice.RationalQuadraticSpaceMatrixFullAdelicAmbientDifferentialNormalizationCertificate
        L P mu) :
    (L.rationalQuadraticSpaceMatrix
        |>.IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale
          (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P)
          mu) := by
  let V := L.rationalQuadraticSpaceMatrix
  let a :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
  refine
    { finiteScale_ne_zero :=
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero P
      finiteScale_ne_top :=
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_top hP
      inverseVolumeProduct_tendsto := ?_
      tangentCoordinateMeasure_eq := C.tangentCoordinateMeasure_eq
      tangentStandardParallelotope_eq_one :=
        C.tangentStandardParallelotope_eq_one
      map_realFinite_eq := ?_
      ne_zero := ?_
      sigmaFinite := ?_
      isHaarMeasure := ?_
      isMulLeftInvariant := ?_
      regular := ?_ }
  · apply
      (padicInvariantDifferentialIntegralInverseVolumeProductTendsTo_iff_lattice
        L a⁻¹).2
    rw [←
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_eq_inv_volume]
    exact C.finiteInverseVolumeProduct_tendsto
  · rw [C.measure_eq]
    rw [
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_eq_stabilizerVolume_smul_general
        hP,
      Measure.map_smul,
      V.map_fullAdelicInvariantDifferentialGroupMeasure_realFinite,
      Measure.prod_smul_right]
    rfl
  · rw [C.measure_eq]
    exact
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_ne_zero hP
  · rw [C.measure_eq]
    exact
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_sigmaFinite hP
  · rw [C.measure_eq]
    exact
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_isHaarMeasure hP
  · rw [C.measure_eq]
    exact
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_isMulLeftInvariant hP
  · rw [C.measure_eq]
    exact
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_regular hP

end IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale

namespace IsRawInvariantDifferentialFullAdelicGroupMeasure

/-- The lattice ambient certificate supplies the existential corrected raw
normalization predicate, with the finite stabilizer volume as its explicit
witness. -/
def of_latticeAmbientCertificate
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    {P : ℝ} (hP : 0 < P)
    {mu :
      Measure
        L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup}
    (C :
      PositiveDefiniteIntegralLattice.RationalQuadraticSpaceMatrixFullAdelicAmbientDifferentialNormalizationCertificate
        L P mu) :
    (L.rationalQuadraticSpaceMatrix
        |>.IsRawInvariantDifferentialFullAdelicGroupMeasure mu) :=
  ⟨L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P,
    IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale.of_latticeAmbientCertificate
      L hP C⟩

end IsRawInvariantDifferentialFullAdelicGroupMeasure

end RationalQuadraticSpaceMatrix
