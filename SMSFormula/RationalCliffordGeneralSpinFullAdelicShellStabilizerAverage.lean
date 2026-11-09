import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellModularCompatibility
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Stabilizer averaging on the full-adelic block shell

Compactly supported continuous functions on the ambient block `GSpin` group
can be averaged along the literal complement stabilizer.  The average is
continuous, right-stabilizer invariant, and descends with compact support to
the native homogeneous-space quotient.

This is the section-free analytic input for the eventual Bruhat--Riesz
construction of the shell measure.  No quotient measure or disintegration is
asserted here.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped CompactlySupported Topology

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000

variable {n : ℕ}

local instance fullAdelicShellAverageInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellAverageFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellAverageT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellAverageSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellAverageSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance fullAdelicShellAverageSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellAverageSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellAverageStabilizerSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

noncomputable local instance fullAdelicShellAverageStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellAverageQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

/-- Average a compactly supported continuous ambient function along the
literal complement stabilizer, using its already normalized Haar measure. -/
noncomputable def fullAdelicNonisotropicLastShellStabilizerAverage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ))
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) : ℝ :=
  ∫ h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha,
    f (g * h.1)
      ∂(W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha)

/-- Stabilizer averaging preserves continuity.  Compact support in the
stabilizer variable is obtained locally by pulling back a compact product set
through the closed subtype embedding. -/
theorem continuous_fullAdelicNonisotropicLastShellStabilizerAverage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    Continuous (W.fullAdelicNonisotropicLastShellStabilizerAverage a ha f) := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let H := W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha
  let μH := W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    a ha
  apply continuous_iff_continuousAt.2
  intro g₀
  obtain ⟨t, ht_compact, ht_nhds⟩ : ∃ t : Set G, IsCompact t ∧ t ∈ 𝓝 g₀ :=
    exists_compact_mem_nhds g₀
  let ambientBound : Set G :=
    (fun p : G × G ↦ p.1⁻¹ * p.2) '' (t ×ˢ tsupport f)
  have hambientBound_compact : IsCompact ambientBound := by
    exact (ht_compact.prod f.hasCompactSupport).image
      ((continuous_fst.inv.mul continuous_snd))
  let stabilizerBound : Set H :=
    (Subtype.val : H → G) ⁻¹' ambientBound
  have hstabilizerBound_compact : IsCompact stabilizerBound := by
    exact
      (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
          a ha RationalAdele).isClosedEmbedding_subtypeVal.isCompact_preimage
        hambientBound_compact
  have hcontinuousOn : ContinuousOn
      (W.fullAdelicNonisotropicLastShellStabilizerAverage a ha f) t := by
    apply continuousOn_integral_of_compact_support hstabilizerBound_compact
    · exact (f.continuous.comp
        (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))).continuousOn
    · intro g h hg hh
      by_contra hzero
      have hmem : g * h.1 ∈ tsupport f := by
        by_contra hnot
        exact hzero (image_eq_zero_of_notMem_tsupport hnot)
      apply hh
      change h.1 ∈ ambientBound
      refine ⟨(g, g * h.1), ⟨hg, hmem⟩, ?_⟩
      change g⁻¹ * (g * h.1) = h.1
      rw [← mul_assoc, inv_mul_cancel, one_mul]
  exact hcontinuousOn.continuousAt ht_nhds

/-- Right multiplication by a literal complement-stabilizer point does not
change the stabilizer average.  This is a change of variable using the fixed
left-Haar normalization on the stabilizer itself. -/
theorem fullAdelicNonisotropicLastShellStabilizerAverage_mul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ))
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (k : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
    W.fullAdelicNonisotropicLastShellStabilizerAverage a ha f (g * k.1) =
      W.fullAdelicNonisotropicLastShellStabilizerAverage a ha f g := by
  letI : Measure.IsMulLeftInvariant
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) :=
    (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isHaarMeasure
      a ha).toIsMulLeftInvariant
  simpa only [fullAdelicNonisotropicLastShellStabilizerAverage, mul_assoc,
    Subgroup.coe_mul] using
    (integral_mul_left_eq_self
      (μ := W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha)
      (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha ↦
        f (g * h.1)) k)

/-- The section-free stabilizer average on the standard homogeneous-space
quotient. -/
noncomputable def fullAdelicNonisotropicLastShellQuotientAverage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha → ℝ :=
  Quotient.lift
    (W.fullAdelicNonisotropicLastShellStabilizerAverage a ha f)
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
      rw [hh, W.fullAdelicNonisotropicLastShellStabilizerAverage_mul a ha f g k])

@[simp]
theorem fullAdelicNonisotropicLastShellQuotientAverage_mk
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ))
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    W.fullAdelicNonisotropicLastShellQuotientAverage a ha f
        (QuotientGroup.mk g) =
      W.fullAdelicNonisotropicLastShellStabilizerAverage a ha f g :=
  rfl

/-- The descended stabilizer average is continuous for the standard quotient
topology. -/
theorem continuous_fullAdelicNonisotropicLastShellQuotientAverage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    Continuous (W.fullAdelicNonisotropicLastShellQuotientAverage a ha f) := by
  exact
    (W.continuous_fullAdelicNonisotropicLastShellStabilizerAverage a ha f)
      |>.quotient_lift _

/-- The quotient average is supported in the compact image of the original
ambient support. -/
theorem hasCompactSupport_fullAdelicNonisotropicLastShellQuotientAverage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    HasCompactSupport
      (W.fullAdelicNonisotropicLastShellQuotientAverage a ha f) := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let H := W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let q : G → X := QuotientGroup.mk
  let K : Set G := tsupport f
  have hqK_compact : IsCompact (q '' K) :=
    f.hasCompactSupport.image continuous_quotient_mk'
  have hsupport : Function.support
      (W.fullAdelicNonisotropicLastShellQuotientAverage a ha f) ⊆ q '' K := by
    intro x hx
    induction x using Quotient.inductionOn' with
    | _ g =>
        by_contra hnot
        apply hx
        rw [W.fullAdelicNonisotropicLastShellQuotientAverage_mk a ha f g]
        have hzero :
            (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer
                a ha ↦ f (g * h.1)) = 0 := by
          funext h
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          apply hnot
          refine ⟨g * h.1, hmem, ?_⟩
          change QuotientGroup.mk (g * h.1) = QuotientGroup.mk g
          symm
          apply Quotient.sound'
          rw [QuotientGroup.leftRel_apply]
          change g⁻¹ * (g * h.1) ∈ H
          rw [← mul_assoc, inv_mul_cancel, one_mul]
          exact h.2
        unfold fullAdelicNonisotropicLastShellStabilizerAverage
        rw [hzero]
        exact integral_zero H ℝ
  exact hqK_compact.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hsupport hqK_compact.isClosed)

/-- Stabilizer averaging as an actual compactly supported continuous function
on the native homogeneous-space quotient. -/
noncomputable def fullAdelicNonisotropicLastShellStabilizerAverageMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ) →
      C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ) :=
  fun f ↦
    { toFun := W.fullAdelicNonisotropicLastShellQuotientAverage a ha f
      continuous_toFun :=
        W.continuous_fullAdelicNonisotropicLastShellQuotientAverage a ha f
      hasCompactSupport' :=
        W.hasCompactSupport_fullAdelicNonisotropicLastShellQuotientAverage
          a ha f }

@[simp]
theorem fullAdelicNonisotropicLastShellStabilizerAverageMap_mk
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ))
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f
        (QuotientGroup.mk g) =
      W.fullAdelicNonisotropicLastShellStabilizerAverage a ha f g :=
  rfl

end RationalQuadraticSpaceMatrix
