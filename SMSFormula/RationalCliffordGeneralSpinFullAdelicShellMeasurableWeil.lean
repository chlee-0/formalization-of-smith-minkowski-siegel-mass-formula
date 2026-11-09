import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellKernelBind
import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellBorel
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Measurable Weil identity on the native full-adelic GSpin shell

The coefficient-one quotient-kernel bind identity is exposed as a Weil
formula for arbitrary measurable nonnegative functions and transported
through the certified native quotient-to-shell measurable equivalence.  The
shell fiber kernel remains the literal translated complement-stabilizer Haar.
No section or quotient representative is selected.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open ProbabilityTheory
open Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance fullAdelicShellMeasurableWeilInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellMeasurableWeilFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellMeasurableWeilT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellMeasurableWeilSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellMeasurableWeilSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance fullAdelicShellMeasurableWeilSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellMeasurableWeilSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellMeasurableWeilStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellMeasurableWeilQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance fullAdelicShellMeasurableWeilQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellMeasurableWeilQuotientLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instLocallyCompactSpace
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellMeasurableWeilQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance fullAdelicShellMeasurableWeilQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellMeasurableWeilTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance fullAdelicShellMeasurableWeilTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- The measurable nonnegative Weil identity on the native standard quotient. -/
theorem lintegral_fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel_measurable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, ∫⁻ g, f g
          ∂W.fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel a ha x
        ∂W.fullAdelicNonisotropicLastShellQuotientMeasure a ha =
      ∫⁻ g, f g
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
  rw [← Measure.lintegral_bind
    (W.fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel a ha).aemeasurable
    hf.aemeasurable]
  exact congrArg (fun μ ↦ ∫⁻ g, f g ∂μ)
    (W.fullAdelicNonisotropicLastShellOrbitFiberBindMeasure_eq_horizontal a ha)

/-- The inverse of the existing quotient-to-shell carrier equivalence is
measurable for the same native Borel structures used by the Riesz measure and
orbit-fiber kernel. -/
theorem measurable_fullAdelicNonisotropicLastShellQuotientEquiv_symm
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    Measurable (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm := by
  rw [measurable_iff_le_map]
  change borel (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) ≤
    MeasurableSpace.map
      (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm
      (borel (W.nonisotropicLastQuadraticShell a ha RationalAdele))
  rw [← W.map_borel_fullAdelicNonisotropicLastShellQuotientMap_eq a ha]
  rw [MeasurableSpace.map_comp]
  have hcomp :
      (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm ∘
          W.fullAdelicNonisotropicLastShellQuotientMap a ha = id := by
    funext x
    exact (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm_apply_apply x
  rw [hcomp]
  rfl

/-- The invariant measure on the existing nonisotropic shell is the native
Riesz quotient measure pushed through the certified measurable equivalence. -/
noncomputable def fullAdelicNonisotropicLastShellMeasure
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    Measure (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  Measure.map
    (W.fullAdelicNonisotropicLastShellQuotientMap a ha)
    (W.fullAdelicNonisotropicLastShellQuotientMeasure a ha)

/-- The native shell orbit-fiber kernel, obtained by evaluating the already
descended quotient kernel at the inverse native measurable equivalence. -/
noncomputable def fullAdelicNonisotropicLastShellOrbitFiberKernel
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    Kernel (W.nonisotropicLastQuadraticShell a ha RationalAdele)
      ((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup) :=
  Kernel.comap
    (W.fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel a ha)
    (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm
    (W.measurable_fullAdelicNonisotropicLastShellQuotientEquiv_symm a ha)

/-- At an actual orbit point, the shell kernel is literally translated
complement-stabilizer Haar. -/
theorem fullAdelicNonisotropicLastShellOrbitFiberKernel_orbit
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha RationalAdele g) =
      Measure.map
        (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer
          a ha ↦ g * h.1)
        (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
          a ha) := by
  rw [fullAdelicNonisotropicLastShellOrbitFiberKernel, Kernel.comap_apply]
  have hclass :
      (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm
          (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele g) = QuotientGroup.mk g := by
    apply (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).injective
    simp
  rw [hclass]
  exact W.fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel_mk a ha g

/-- Integration against the shell fiber at an actual orbit point is literal
integration over the complement stabilizer. -/
theorem lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_orbit
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (f : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    ∫⁻ z, f z
        ∂W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha
          (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele g) =
      ∫⁻ h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha,
        f (g * h.1)
        ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
          a ha := by
  rw [W.fullAdelicNonisotropicLastShellOrbitFiberKernel_orbit a ha g]
  rw [MeasureTheory.lintegral_map hf (by fun_prop)]

/-- The measurable nonnegative Weil identity transported to the actual native
nonisotropic shell. -/
theorem lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_measurable
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (f : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y, ∫⁻ g, f g
          ∂W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha y
        ∂W.fullAdelicNonisotropicLastShellMeasure a ha =
      ∫⁻ g, f g
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
  have houter : Measurable fun y ↦
      ∫⁻ g, f g ∂W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha y :=
    hf.lintegral_kernel
  have hmap : Measurable
      (W.fullAdelicNonisotropicLastShellQuotientMap a ha) :=
    (W.continuous_fullAdelicNonisotropicLastShellQuotientMap a ha).measurable
  rw [fullAdelicNonisotropicLastShellMeasure]
  rw [MeasureTheory.lintegral_map houter hmap]
  have hkernel (x : W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :
      W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha
          (W.fullAdelicNonisotropicLastShellQuotientMap a ha x) =
        W.fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel a ha x := by
    rw [fullAdelicNonisotropicLastShellOrbitFiberKernel, Kernel.comap_apply]
    congr 1
    exact (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm_apply_apply x
  simp_rw [hkernel]
  exact
    W.lintegral_fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel_measurable
      a ha f hf

/-- The actual shell measure bound against its literal orbit-fiber kernel is
the established horizontal full-adelic GSpin Haar. -/
theorem fullAdelicNonisotropicLastShellMeasure_bind_orbitFiberKernel_eq_horizontal
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    (W.fullAdelicNonisotropicLastShellMeasure a ha).bind
        (W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha) =
      (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind
    (W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha).aemeasurable
    hf.aemeasurable]
  exact W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_measurable
    a ha f hf

end RationalQuadraticSpaceMatrix
