import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberSupport
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Global Haar scale of the normalized ambient central-fiber bind

The normalized ambient differential central-fiber bind and the fixed
horizontal adelic `GSpin` Haar are compared on the same
identity-chart carrier.  That carrier is open and nonempty.  Local compactness
therefore supplies a compact set with nonempty interior inside it.  The exact
cylinder restriction makes the ambient bind finite and positive on this set,
so its global left invariance upgrades to a Haar measure.

Haar uniqueness is then calibrated on the same compact set.  The resulting
global scalar is exactly the absolute differential `SO` block weight divided
by the differential cylinder scale.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open TopologicalSpace
open scoped ENNReal NNReal Finset

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalAmbientCentralFiberHaarScaleDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalAmbientCentralFiberHaarScaleFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalAmbientCentralFiberHaarScaleFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalAmbientCentralFiberHaarScaleFiniteAdeleT2 :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance horizontalAmbientCentralFiberHaarScaleInfiniteAdeleT2 :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance horizontalAmbientCentralFiberHaarScaleAdeleT2 :
    T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

local instance horizontalAmbientCentralFiberHaarScaleFullGSpinT2
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    T2Space
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinIntrinsicPointT2Space RationalAdele

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

/-! ## The explicit scalar on the calibrated cylinder -/

/-- The positive finite scalar from fixed horizontal adelic Haar to the
carrier-independent normalized ambient differential central-fiber bind. -/
noncomputable def fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0 :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  (V.finiteAdelicSpecialOrthogonalBlockWeight B *
    (L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S)⁻¹).toNNReal

@[simp]
theorem coe_fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S : ℝ≥0∞) =
      let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.finiteAdelicSpecialOrthogonalBlockWeight B *
        (L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S)⁻¹ := by
  dsimp only [fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar]
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  exact ENNReal.coe_toNNReal
    (ENNReal.mul_ne_top
      (V.finiteAdelicSpecialOrthogonalBlockWeight_ne_top B)
      (ENNReal.inv_ne_top.mpr
        (L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale_ne_zero S)))

/-- The global ambient-to-horizontal scalar is strictly positive. -/
theorem fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar_pos
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    0 < L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S := by
  unfold fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar
  apply ENNReal.toNNReal_pos
  · exact mul_ne_zero
      (L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalBlockWeight_ne_zero _)
      (ENNReal.inv_ne_zero.mpr
        (L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale_ne_top S))
  · exact ENNReal.mul_ne_top
      (L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalBlockWeight_ne_top _)
      (ENNReal.inv_ne_top.mpr
        (L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale_ne_zero S))

/-- On the exact calibrated carrier, the normalized ambient bind is already
the named explicit scalar times fixed horizontal Haar. -/
theorem
    fullAdelicInvariantDifferentialCentralFiberBoundMeasure_restrict_identityChart_eq_scalar_smul_horizontal
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure.restrict
        (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E) =
      L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S •
        V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
          (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let w := V.finiteAdelicSpecialOrthogonalBlockWeight B
  let c := L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S
  let ξ :=
    L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S
  let ν := V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  rw [L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure_restrict_identityChart S]
  rw [L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure_eq_inv_scale_smul_haar_restrict
    S]
  rw [smul_smul]
  change
    (V.finiteAdelicSpecialOrthogonalBlockWeight B * c⁻¹) • ν.restrict C =
      (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S : ℝ≥0∞) •
        ν.restrict C
  rw [L.coe_fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S]

/-! ## A compact calibration neighborhood -/

/-- Local compactness supplies a compact set with nonempty interior inside
the exact open identity carrier. -/
theorem exists_compact_nonemptyInterior_subset_identityChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    ∃ K : Set V.FullAdelicCliffordGeneralSpinGroup,
      IsCompact K ∧ (interior K).Nonempty ∧
        K ⊆ V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  obtain ⟨x, hx⟩ :=
    V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier_nonempty E
  obtain ⟨K, hK, hxK, hKC⟩ := exists_compact_subset
    (V.isOpen_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E) hx
  exact ⟨K, hK, ⟨x, hxK⟩, hKC⟩

/-! ## Haar regularity and global uniqueness -/

/-- The normalized ambient differential central-fiber bind is a genuine Haar
measure.  Positivity and compact finiteness are calibrated inside the exact
identity cylinder rather than asserted from the descended kernel alone. -/
theorem fullAdelicInvariantDifferentialCentralFiberBoundMeasure_isHaarMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  let μ := L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure
  let ν := V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let a := L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S
  letI : Measure.IsHaarMeasure ν :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  letI : Measure.IsMulLeftInvariant μ :=
    L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure_isMulLeftInvariant
  obtain ⟨K, hK, hKint, hKC⟩ :=
    L.exists_compact_nonemptyInterior_subset_identityChart S
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hlocal := congrArg (fun ρ : Measure V.FullAdelicCliffordGeneralSpinGroup => ρ K)
    (L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure_restrict_identityChart_eq_scalar_smul_horizontal
      S)
  have hmass : μ K = (a : ℝ≥0∞) * ν K := by
    change (μ.restrict C) K = (a • ν.restrict C) K at hlocal
    rw [Measure.restrict_apply hKmeas, Measure.smul_apply,
      Measure.restrict_apply hKmeas] at hlocal
    rw [Set.inter_eq_left.mpr hKC] at hlocal
    simpa only [ENNReal.smul_def, smul_eq_mul] using hlocal
  have hnu0 : ν K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior ν hKint).ne'
  have hnutop : ν K ≠ ∞ := hK.measure_ne_top
  have hmu0 : μ K ≠ 0 := by
    rw [hmass]
    exact mul_ne_zero
      (ENNReal.coe_ne_zero.mpr
        (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar_pos S).ne')
      hnu0
  have hmutop : μ K ≠ ∞ := by
    rw [hmass]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hnutop
  exact Measure.isHaarMeasure_of_isCompact_nonempty_interior μ K hK hKint hmu0 hmutop

/-- The normalized ambient bind is globally the explicit positive finite
scalar multiple of fixed horizontal adelic Haar. -/
theorem fullAdelicInvariantDifferentialCentralFiberBoundMeasure_eq_scalar_smul_horizontal
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure =
      L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S •
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  let μ := L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure
  let ν := V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let a := L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S
  letI : SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology
  letI : Measure.IsHaarMeasure ν :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  letI : Measure.IsHaarMeasure μ :=
    L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure_isHaarMeasure S
  letI : Measure.IsMulLeftInvariant μ := by infer_instance
  let q := Measure.haarScalarFactor μ ν
  have hunique : μ = q • ν :=
    Measure.isMulLeftInvariant_eq_smul μ ν
  obtain ⟨K, hK, hKint, hKC⟩ :=
    L.exists_compact_nonemptyInterior_subset_identityChart S
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hlocal := congrArg (fun ρ : Measure V.FullAdelicCliffordGeneralSpinGroup => ρ K)
    (L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure_restrict_identityChart_eq_scalar_smul_horizontal
      S)
  have hmass : μ K = (a : ℝ≥0∞) * ν K := by
    change (μ.restrict C) K = (a • ν.restrict C) K at hlocal
    rw [Measure.restrict_apply hKmeas, Measure.smul_apply,
      Measure.restrict_apply hKmeas] at hlocal
    rw [Set.inter_eq_left.mpr hKC] at hlocal
    simpa only [ENNReal.smul_def, smul_eq_mul] using hlocal
  have huniqueMass := congrArg
    (fun ρ : Measure V.FullAdelicCliffordGeneralSpinGroup => ρ K) hunique
  have hqmass : μ K = (q : ℝ≥0∞) * ν K := by
    simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using huniqueMass
  have hnu0 : ν K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior ν hKint).ne'
  have hnutop : ν K ≠ ∞ := hK.measure_ne_top
  have hqa : q = a := by
    have hmul : ν K * (q : ℝ≥0∞) = ν K * (a : ℝ≥0∞) := by
      calc
        ν K * (q : ℝ≥0∞) = (q : ℝ≥0∞) * ν K := mul_comm _ _
        _ = μ K := hqmass.symm
        _ = (a : ℝ≥0∞) * ν K := hmass
        _ = ν K * (a : ℝ≥0∞) := mul_comm _ _
    exact ENNReal.coe_injective ((ENNReal.mul_right_inj hnu0 hnutop).mp hmul)
  rw [hqa] at hunique
  exact hunique

/-- Restoring the lattice normalization multiplies the calibrated global Haar
scalar by the literal finite stabilizer volume.  This factor is not absorbed
by the differential cylinder calibration. -/
theorem fullAdelicDifferentialCentralFiberBoundMeasure_eq_stabilizerVolume_mul_scalar_smul_horizontal
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.fullAdelicDifferentialCentralFiberBoundMeasure P =
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
          (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S : ℝ≥0∞)) •
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  rw [L.fullAdelicDifferentialCentralFiberBoundMeasure_eq_stabilizerVolume_smul hP,
    L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure_eq_scalar_smul_horizontal S]
  change
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
        ((L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S : ℝ≥0∞) •
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      _
  rw [smul_smul]

end PositiveDefiniteIntegralLattice
