import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderHaarRestriction
import SMSFormula.RationalCliffordGeneralSpinHorizontalDifferentialHaarConversion
import SMSFormula.RationalSpecialOrthogonalLatticeGeneralDifferentialMeasureComparison

/-!
# The finite stabilizer scale in the ambient central-fiber bind

The lattice differential `SO` measure used in the crossed-cutoff argument is
not the probability-normalized finite restricted-product Haar.  It is the
carrier-independent invariant-differential Haar multiplied by the
finite stabilizer volume attached to the cutoff-product limit `P`.

Binding either measure against the same descended differential central fiber
therefore preserves exactly that scalar.  In particular, restriction to a
calibrating identity-chart cylinder also retains it.  This separates the
normalized ambient disintegration from the lattice scale,
which must survive into the raw `SO` mass; it prevents incorrectly asserting
that the `P`-dependent bind itself restricts to the scalar-one horizontal
cylinder.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalAmbientCentralFiberScaleFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalAmbientCentralFiberScaleFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalAmbientCentralFiberScaleFullSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  borel _

local instance horizontalAmbientCentralFiberScaleFullSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

/-! ## Carrier-independent normalized bind -/

/-- Bind the descended differential central fibers against the fixed
carrier-independent invariant-differential `SO` Haar.  This is the normalized
ambient measure whose identity-chart restriction is to be compared with the
fixed horizontal `GSpin` cylinder. -/
noncomputable def fullAdelicInvariantDifferentialCentralFiberBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  Measure.bind
    L.rationalQuadraticSpaceMatrix.fullAdelicInvariantDifferentialGroupMeasure
    L.fullAdelicDifferentialCentralFiberKernelAtSO

/-- The `P`-dependent lattice bind is exactly the finite stabilizer volume
times the carrier-independent normalized bind. -/
theorem fullAdelicDifferentialCentralFiberBoundMeasure_eq_stabilizerVolume_smul
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P) :
    L.fullAdelicDifferentialCentralFiberBoundMeasure P =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
        L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure := by
  unfold fullAdelicDifferentialCentralFiberBoundMeasure
    fullAdelicInvariantDifferentialCentralFiberBoundMeasure
  rw [
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_eq_stabilizerVolume_smul_general
      hP,
    Measure.bind_smul]

/-! ## Invariance at the normalized scale -/

/-- Binding the central fibers against the carrier-independent differential
`SO` Haar is left invariant on ambient adelic `GSpin`. -/
theorem map_mul_left_fullAdelicInvariantDifferentialCentralFiberBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (g :
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map
        (fun x :
          L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup =>
          g * x)
        L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure =
      L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let R := fun x : V.FullAdelicCliffordGeneralSpinGroup => g * x
  let B := fun h : V.FullAdelicSpecialOrthogonalGroup =>
    V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom g * h
  have hR : Measurable R :=
    (continuous_const.mul continuous_id : Continuous R).measurable
  have hB : Measurable B :=
    (continuous_const.mul continuous_id : Continuous B).measurable
  apply Measure.ext
  intro s hs
  change (Measure.map R
      L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure) s =
    L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure s
  rw [Measure.map_apply hR hs]
  unfold fullAdelicInvariantDifferentialCentralFiberBoundMeasure
  rw [
    Measure.bind_apply (hR hs)
      L.fullAdelicDifferentialCentralFiberKernelAtSO.aemeasurable,
    Measure.bind_apply hs
      L.fullAdelicDifferentialCentralFiberKernelAtSO.aemeasurable]
  have hfiber (h : V.FullAdelicSpecialOrthogonalGroup) :
      L.fullAdelicDifferentialCentralFiberKernelAtSO h (R ⁻¹' s) =
        L.fullAdelicDifferentialCentralFiberKernelAtSO (B h) s := by
    have heq :=
      L.map_mul_left_fullAdelicDifferentialCentralFiberKernelAtSO g h
    have happ := congrArg
      (fun mu : Measure V.FullAdelicCliffordGeneralSpinGroup => mu s) heq
    change (Measure.map R
        (L.fullAdelicDifferentialCentralFiberKernelAtSO h)) s =
      L.fullAdelicDifferentialCentralFiberKernelAtSO (B h) s at happ
    rw [Measure.map_apply hR hs] at happ
    exact happ
  change
    (∫⁻ h, L.fullAdelicDifferentialCentralFiberKernelAtSO h (R ⁻¹' s)
      ∂V.fullAdelicInvariantDifferentialGroupMeasure) =
    ∫⁻ h, L.fullAdelicDifferentialCentralFiberKernelAtSO h s
      ∂V.fullAdelicInvariantDifferentialGroupMeasure
  simp_rw [hfiber]
  have hmeas : Measurable
      (fun h : V.FullAdelicSpecialOrthogonalGroup =>
        L.fullAdelicDifferentialCentralFiberKernelAtSO h s) :=
    L.fullAdelicDifferentialCentralFiberKernelAtSO.measurable_coe hs
  rw [← lintegral_map' hmeas.aemeasurable hB.aemeasurable]
  letI : Measure.IsMulLeftInvariant
      V.fullAdelicInvariantDifferentialGroupMeasure :=
    V.fullAdelicInvariantDifferentialGroupMeasure_isMulLeftInvariant
  rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self]

/-- The normalized ambient bind carries the exact left-invariance interface
needed for the remaining cylinder calibration and Haar regularity proof. -/
theorem
    fullAdelicInvariantDifferentialCentralFiberBoundMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    Measure.IsMulLeftInvariant
      L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure where
  map_mul_left_eq_self g :=
    L.map_mul_left_fullAdelicInvariantDifferentialCentralFiberBoundMeasure g

/-! ## The scalar survives cylinder restriction -/

/-- Restricting the ambient bind to any measurable carrier retains the same
finite stabilizer scalar.  The intended calibration carrier is the canonical
full-adelic identity-chart carrier, but the measure-theoretic statement is
useful without specializing the set. -/
theorem fullAdelicDifferentialCentralFiberBoundMeasure_restrict_eq_stabilizerVolume_smul
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P)
    (s : Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    (L.fullAdelicDifferentialCentralFiberBoundMeasure P).restrict s =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
        (L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure.restrict s) := by
  rw [L.fullAdelicDifferentialCentralFiberBoundMeasure_eq_stabilizerVolume_smul hP,
    Measure.restrict_smul]

/-- On the exact calibrated identity-chart carrier, the only scale between
the lattice bind and the normalized ambient bind is the literal finite
stabilizer volume. -/
theorem
    fullAdelicDifferentialCentralFiberBoundMeasure_restrict_identityChart_eq_stabilizerVolume_smul
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (L.fullAdelicDifferentialCentralFiberBoundMeasure P).restrict
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
          S) =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
        (L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure.restrict
          (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
            S)) :=
  L.fullAdelicDifferentialCentralFiberBoundMeasure_restrict_eq_stabilizerVolume_smul
    hP _

/-- Once the normalized ambient bind is calibrated on the identity chart,
the corresponding lattice bind restricts to the finite stabilizer volume
times the coherent horizontal cylinder.  This is the corrected downstream
target: the lattice volume is not absorbed by the real/dyadic square-modulus
cancellation. -/
theorem
    fullAdelicDifferentialCentralFiberBoundMeasure_restrict_identityChart_eq_stabilizerVolume_smul_coherent
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hcalibrate :
      L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure.restrict
          (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
            S) =
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure
          S) :
    (L.fullAdelicDifferentialCentralFiberBoundMeasure P).restrict
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
          S) =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure
          S := by
  rw [
    L.fullAdelicDifferentialCentralFiberBoundMeasure_restrict_identityChart_eq_stabilizerVolume_smul
      hP S,
    hcalibrate]

end PositiveDefiniteIntegralLattice
