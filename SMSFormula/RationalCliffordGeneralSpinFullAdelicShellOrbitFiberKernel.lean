import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellQuotientInvariant
import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Native orbit-fiber kernel for the full-adelic GSpin shell quotient

The fixed complement-stabilizer Haar measure is translated into every ambient
right-coset fiber.  The resulting ambient kernel is constant on right cosets,
so it descends through the standard quotient with its native Borel structure.
No quotient representative or measurable section is selected.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance fullAdelicShellFiberKernelInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellFiberKernelFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellFiberKernelT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellFiberKernelSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellFiberKernelSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellFiberKernelSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellFiberKernelSourcePolishSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    PolishSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupPolishSpaceForMeasurableDescent

noncomputable local instance fullAdelicShellFiberKernelStabilizerSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

noncomputable local instance fullAdelicShellFiberKernelStabilizerSFinite
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SFinite
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) := by
  infer_instance

noncomputable local instance fullAdelicShellFiberKernelStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellFiberKernelQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance fullAdelicShellFiberKernelQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellFiberKernelQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance fullAdelicShellFiberKernelQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

/-- The measurable ambient family of right-coset fiber measures. -/
noncomputable def fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Kernel
      ((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup)
      ((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup) := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let H := W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha
  let μH :=
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha
  exact Kernel.map
    (Kernel.compProd (Kernel.id : Kernel G G)
      (Kernel.const (G × G) μH))
    (fun p : G × H ↦ p.1 * p.2.1)

/-- At an ambient point, the orbit-fiber kernel is literally the pushforward
of the fixed stabilizer Haar under right multiplication from that point. -/
theorem fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_apply
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha g =
      Measure.map
        (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha ↦
          g * h.1)
        (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
          a ha) := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let H := W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha
  let μH :=
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha
  ext s hs
  rw [fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel]
  rw [Kernel.map_apply' _ (by fun_prop) g hs]
  rw [Kernel.compProd_apply (hs.preimage (by fun_prop))]
  simp only [Kernel.const_apply, Kernel.id_apply]
  rw [lintegral_dirac]
  rw [Measure.map_apply (by fun_prop) hs]
  rfl

/-- Changing the ambient representative by a right stabilizer factor does not
change its orbit-fiber measure. -/
theorem fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_mul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (k : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
    W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha (g * k.1) =
      W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha g := by
  let μH :=
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha
  letI : Measure.IsMulLeftInvariant μH :=
    (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isHaarMeasure
      a ha).toIsMulLeftInvariant
  rw [W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_apply a ha,
    W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_apply a ha]
  calc
    Measure.map
        (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha ↦
          (g * k.1) * h.1) μH =
      Measure.map
        (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha ↦
          g * h.1)
        (Measure.map (fun h ↦ k * h) μH) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          congr 1
          funext h
          simp only [Function.comp_apply, Subgroup.coe_mul, mul_assoc]
    _ = Measure.map
        (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha ↦
          g * h.1) μH := by
      rw [map_mul_left_eq_self μH k]

/-- The section-free orbit-fiber measure on the standard right-coset quotient. -/
noncomputable def fullAdelicNonisotropicLastShellQuotientOrbitFiberMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha →
      Measure ((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup) :=
  Quotient.lift
    (W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha)
    (fun g h hrel ↦ by
      change QuotientGroup.leftRel
        (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
          a ha RationalAdele) g h at hrel
      rw [QuotientGroup.leftRel_apply] at hrel
      let k : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha :=
        ⟨g⁻¹ * h, hrel⟩
      have hh : h = g * k.1 := by
        change h = g * (g⁻¹ * h)
        symm
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [hh, W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_mul a ha g k])

@[simp]
theorem fullAdelicNonisotropicLastShellQuotientOrbitFiberMeasure_mk
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    W.fullAdelicNonisotropicLastShellQuotientOrbitFiberMeasure a ha
        (QuotientGroup.mk g) =
      W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha g :=
  rfl

/-- The descended orbit-fiber measure varies measurably in the native quotient
Borel structure. -/
theorem measurable_fullAdelicNonisotropicLastShellQuotientOrbitFiberMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measurable
      (W.fullAdelicNonisotropicLastShellQuotientOrbitFiberMeasure a ha) := by
  letI : T2Space
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    W.fullAdelicShellFiberKernelQuotientT2Space a ha
  letI : SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    W.fullAdelicShellFiberKernelQuotientSecondCountable a ha
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let q : G → X := QuotientGroup.mk
  rw [measurable_iff_le_map]
  change Measure.instMeasurableSpace ≤
    MeasurableSpace.map
      (W.fullAdelicNonisotropicLastShellQuotientOrbitFiberMeasure a ha)
      (borel X)
  have hq : MeasurableSpace.map q (borel G) = borel X :=
    continuous_quotient_mk'.map_borel_eq QuotientGroup.mk_surjective
  rw [← hq, MeasurableSpace.map_comp]
  exact
    (W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha
      |>.measurable).le_map

/-- The native-Borel orbit-fiber kernel on the standard right-coset quotient.
It is defined by quotient descent from the measurable ambient kernel. -/
noncomputable def fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Kernel
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha)
      ((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup) where
  toFun := W.fullAdelicNonisotropicLastShellQuotientOrbitFiberMeasure a ha
  measurable' :=
    W.measurable_fullAdelicNonisotropicLastShellQuotientOrbitFiberMeasure a ha

@[simp]
theorem fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel_mk
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    W.fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel a ha
        (QuotientGroup.mk g) =
      Measure.map
        (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha ↦
          g * h.1)
        (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
          a ha) := by
  exact W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_apply a ha g

end RationalQuadraticSpaceMatrix
