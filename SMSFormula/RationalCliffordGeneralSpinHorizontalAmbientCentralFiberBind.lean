import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiber
import SMSFormula.SpecialOrthogonalRationalAdelicDifferentialHaar

/-!
# Binding the ambient differential central fiber over adelic SO

The descended ambient central-fiber family need not inherit Mathlib's stronger
`IsSFiniteKernel` certificate merely from its pullback along the surjective
`GSpin -> SO` map.  This module uses the direct `Measure.bind` interface
instead.  Every individual fiber is s-finite, the bound measure has the exact
set and nonnegative-integral formulas, and centrality makes the kernel
equivariant for simultaneous left translation.  Binding against the fixed
differential `SO` Haar measure is consequently left invariant.

No measurable section, finite-kernel descent, product decomposition, Haar
scale identification, quotient measure, or idele-class comparison is asserted.
-/

noncomputable section

open MeasureTheory
open MeasurableSpace
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalAmbientCentralFiberBindFullGSpinMeasurableSpace :
    MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalAmbientCentralFiberBindFullGSpinBorelSpace :
    BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalAmbientCentralFiberBindFullSOMeasurableSpace :
    MeasurableSpace V.FullAdelicSpecialOrthogonalGroup :=
  borel _

local instance horizontalAmbientCentralFiberBindFullSOBorelSpace :
    BorelSpace V.FullAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1800000

/-! ## Equivariance of the source-indexed fiber -/

/-- Left translation of an ambient differential central orbit is the central
orbit through the translated origin. -/
theorem map_mul_left_fullAdelicDifferentialCentralFiberKernel
    (g x : V.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map
        (fun y : V.FullAdelicCliffordGeneralSpinGroup => g * y)
        (V.fullAdelicDifferentialCentralFiberKernel x) =
      V.fullAdelicDifferentialCentralFiberKernel (g * x) := by
  rw [V.fullAdelicDifferentialCentralFiberKernel_apply,
    V.fullAdelicDifferentialCentralFiberKernel_apply]
  let orbit := fun a : RationalAdeleˣ =>
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
      V RationalAdele a * x
  let leftMul := fun y : V.FullAdelicCliffordGeneralSpinGroup => g * y
  have horbit : Measurable orbit :=
    (V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
      continuous_id).mul continuous_const |>.measurable
  have hleft : Measurable leftMul :=
    (continuous_const.mul continuous_id : Continuous leftMul).measurable
  rw [Measure.map_map hleft horbit]
  apply congrArg
    (fun f : RationalAdeleˣ → V.FullAdelicCliffordGeneralSpinGroup =>
      Measure.map f rationalIdeleDifferentialHaarMeasure)
  funext a
  let z := CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
    V RationalAdele a
  change g * (z * x) = z * (g * x)
  calc
    g * (z * x) = (g * z) * x := (mul_assoc _ _ _).symm
    _ = (z * g) * x := by
      rw [V.cliffordGeneralSpin_scalar_commutes RationalAdele a g]
    _ = z * (g * x) := mul_assoc _ _ _

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalAmbientCentralFiberBindLatticeFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalAmbientCentralFiberBindLatticeFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalAmbientCentralFiberBindLatticeFullSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  borel _

local instance horizontalAmbientCentralFiberBindLatticeFullSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1800000

/-! ## The direct bind interface -/

/-- Every descended ambient central fiber is s-finite as a measure.  This is
deliberately pointwise; it does not assert Mathlib's stronger uniform
`IsSFiniteKernel` decomposition on the descended kernel. -/
instance fullAdelicDifferentialCentralFiberKernelAtSO_apply_sFinite
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    SFinite (L.fullAdelicDifferentialCentralFiberKernelAtSO h) := by
  rw [L.fullAdelicDifferentialCentralFiberKernelAtSO_apply]
  unfold fullAdelicDifferentialCentralFiberMeasureAtSO
  infer_instance

/-- Bind fixed ambient differential `SO` Haar against the literal descended
differential central fibers. -/
noncomputable def fullAdelicDifferentialCentralFiberBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) (P : ℝ) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  Measure.bind
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P)
    L.fullAdelicDifferentialCentralFiberKernelAtSO

/-- The direct bound measure of a measurable set is the outer differential
`SO` integral of its literal central-fiber masses. -/
theorem fullAdelicDifferentialCentralFiberBoundMeasure_apply
    (L : PositiveDefiniteIntegralLattice (r + 2)) (P : ℝ)
    {s : Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup}
    (hs : MeasurableSet s) :
    L.fullAdelicDifferentialCentralFiberBoundMeasure P s =
      ∫⁻ h, L.fullAdelicDifferentialCentralFiberKernelAtSO h s
        ∂L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P := by
  rw [fullAdelicDifferentialCentralFiberBoundMeasure,
    Measure.bind_apply hs
      L.fullAdelicDifferentialCentralFiberKernelAtSO.aemeasurable]

/-- Full nonnegative measurable-integrand formula for the direct ambient
central-fiber bind. -/
theorem lintegral_fullAdelicDifferentialCentralFiberBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) (P : ℝ)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂L.fullAdelicDifferentialCentralFiberBoundMeasure P =
      ∫⁻ h, ∫⁻ x, f x
          ∂L.fullAdelicDifferentialCentralFiberKernelAtSO h
        ∂L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P := by
  rw [fullAdelicDifferentialCentralFiberBoundMeasure,
    Measure.lintegral_bind
      L.fullAdelicDifferentialCentralFiberKernelAtSO.aemeasurable
      hf.aemeasurable]

/-! ## Simultaneous left-translation covariance -/

/-- The descended ambient central-fiber kernel is equivariant for left
translation on both `GSpin` and its `SO` base. -/
theorem map_mul_left_fullAdelicDifferentialCentralFiberKernelAtSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    Measure.map
        (fun x :
          L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup =>
          g * x)
        (L.fullAdelicDifferentialCentralFiberKernelAtSO h) =
      L.fullAdelicDifferentialCentralFiberKernelAtSO
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
            g * h) := by
  let V := L.rationalQuadraticSpaceMatrix
  let x := L.fullAdelicDifferentialCentralFiberLift h
  have hx :
      V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom g * h =
        V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom (g * x) := by
    rw [map_mul, L.fullAdelicDifferentialCentralFiberLift_spec]
  have hh : h =
      V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x :=
    (L.fullAdelicDifferentialCentralFiberLift_spec h).symm
  rw [hx,
    L.fullAdelicDifferentialCentralFiberKernelAtSO_comp_projection,
    hh,
    L.fullAdelicDifferentialCentralFiberKernelAtSO_comp_projection]
  exact V.map_mul_left_fullAdelicDifferentialCentralFiberKernel g x

/-- Binding the equivariant central fibers against fixed differential `SO`
Haar produces a left-invariant measure on ambient adelic `GSpin`.
Its scale is fixed by the identity-chart cylinders. -/
theorem map_mul_left_fullAdelicDifferentialCentralFiberBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map
        (fun x :
          L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup =>
          g * x)
        (L.fullAdelicDifferentialCentralFiberBoundMeasure P) =
      L.fullAdelicDifferentialCentralFiberBoundMeasure P := by
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
      (L.fullAdelicDifferentialCentralFiberBoundMeasure P)) s =
    L.fullAdelicDifferentialCentralFiberBoundMeasure P s
  rw [Measure.map_apply hR hs]
  rw [L.fullAdelicDifferentialCentralFiberBoundMeasure_apply P
      (hR hs),
    L.fullAdelicDifferentialCentralFiberBoundMeasure_apply P hs]
  have hfiber (h : V.FullAdelicSpecialOrthogonalGroup) :
      L.fullAdelicDifferentialCentralFiberKernelAtSO h (R ⁻¹' s) =
        L.fullAdelicDifferentialCentralFiberKernelAtSO (B h) s := by
    have heq :=
      L.map_mul_left_fullAdelicDifferentialCentralFiberKernelAtSO g h
    have happ := congrArg
      (fun μ : Measure V.FullAdelicCliffordGeneralSpinGroup => μ s) heq
    change (Measure.map R
        (L.fullAdelicDifferentialCentralFiberKernelAtSO h)) s =
      L.fullAdelicDifferentialCentralFiberKernelAtSO (B h) s at happ
    rw [Measure.map_apply hR hs] at happ
    exact happ
  change
    (∫⁻ h, L.fullAdelicDifferentialCentralFiberKernelAtSO h (R ⁻¹' s)
      ∂L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P) =
    ∫⁻ h, L.fullAdelicDifferentialCentralFiberKernelAtSO h s
      ∂L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P
  simp_rw [hfiber]
  have hmeas : Measurable
      (fun h : V.FullAdelicSpecialOrthogonalGroup =>
        L.fullAdelicDifferentialCentralFiberKernelAtSO h s) :=
    L.fullAdelicDifferentialCentralFiberKernelAtSO.measurable_coe hs
  rw [← lintegral_map' hmeas.aemeasurable
    hB.aemeasurable]
  letI : Measure.IsMulLeftInvariant
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P) :=
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_isMulLeftInvariant
      hP
  rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self]

/-- The direct ambient central-fiber bind carries the exact left-invariance
instance needed for Haar-scale comparison. -/
theorem fullAdelicDifferentialCentralFiberBoundMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P) :
    Measure.IsMulLeftInvariant
      (L.fullAdelicDifferentialCentralFiberBoundMeasure P) where
  map_mul_left_eq_self g :=
    L.map_mul_left_fullAdelicDifferentialCentralFiberBoundMeasure hP g

end PositiveDefiniteIntegralLattice
