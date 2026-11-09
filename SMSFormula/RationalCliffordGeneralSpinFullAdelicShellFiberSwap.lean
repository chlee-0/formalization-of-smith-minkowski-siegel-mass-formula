import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellBruhatPositiveLift
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fiber swap for the full-adelic block shell

This file proves the symmetric compactly supported fiber-integral identity
required to make ambient Haar integration independent of a stabilizer-average
lift.  The proof uses the already established bi-invariance and inversion
invariance of the fixed ambient and stabilizer Haar measures.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open Set
open scoped CompactlySupported Topology

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000

variable {n : ℕ}

local instance fullAdelicShellFiberSwapInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellFiberSwapFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellFiberSwapT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellFiberSwapSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellFiberSwapSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance fullAdelicShellFiberSwapSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellFiberSwapSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellFiberSwapStabilizerSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

noncomputable local instance fullAdelicShellFiberSwapStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellFiberSwapQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

/-- The joint ambient/stabilizer integrand used in the fiber-swap identity
has compact support. -/
private theorem hasCompactSupport_fullAdelicNonisotropicLastShell_fiberSwapJoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f g : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    HasCompactSupport
      (Function.uncurry fun x
        (h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) ↦
          f x * g (x * h.1)) := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let H := W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha
  let K : Set G := tsupport f
  let L : Set G := tsupport g
  let ambientBound : Set G :=
    (fun p : G × G ↦ p.1⁻¹ * p.2) '' (K ×ˢ L)
  have hambientBound : IsCompact ambientBound :=
    (f.hasCompactSupport.prod g.hasCompactSupport).image
      (continuous_fst.inv.mul continuous_snd)
  let stabilizerBound : Set H :=
    (Subtype.val : H → G) ⁻¹' ambientBound
  have hstabilizerBound : IsCompact stabilizerBound :=
    (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele).isClosedEmbedding_subtypeVal.isCompact_preimage
      hambientBound
  apply HasCompactSupport.of_support_subset_isCompact
    (f.hasCompactSupport.prod hstabilizerBound)
  rintro ⟨x, h⟩ hxh
  have hfx : f x ≠ 0 := (mul_ne_zero_iff.mp hxh).1
  have hgxh : g (x * h.1) ≠ 0 := (mul_ne_zero_iff.mp hxh).2
  refine ⟨subset_tsupport f hfx, ?_⟩
  change h.1 ∈ ambientBound
  refine ⟨(x, x * h.1), ⟨subset_tsupport f hfx, subset_tsupport g hgxh⟩, ?_⟩
  change x⁻¹ * (x * h.1) = h.1
  rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- Every compact quotient set admits a nonnegative ambient cutoff whose
stabilizer average is exactly one on that set. -/
theorem exists_fullAdelicNonisotropicLastShell_nonnegative_average_one_on_compact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (K : Set (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha))
    (hK : IsCompact K) :
    ∃ β : C_c((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup, ℝ),
      (∀ g, 0 ≤ β g) ∧
      ∀ x ∈ K,
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha β x = 1 := by
  obtain ⟨c, hcK, -, hccompact, hcmem⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty
      (disjoint_empty K)
  let φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ) :=
    ⟨c, hccompact⟩
  obtain ⟨β, hβ, haverage⟩ :=
    W.exists_fullAdelicNonisotropicLastShell_nonnegative_stabilizerAverage_lift
      a ha φ (fun x ↦ (hcmem x).1)
  refine ⟨β, hβ, ?_⟩
  intro x hx
  rw [haverage]
  exact hcK hx

/-- The fixed ambient Haar integral is symmetric after inserting the
stabilizer average.  This is the bi-invariant specialization of the modular
fiber-swap identity. -/
theorem integral_mul_fullAdelicNonisotropicLastShellStabilizerAverageMap_comm
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f g : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    ∫ x, f x *
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha g
          (QuotientGroup.mk x)
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      ∫ x, g x *
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f
          (QuotientGroup.mk x)
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let H := W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha
  let μG := (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let μH := W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    a ha
  letI : Measure.IsMulRightInvariant μG :=
    (W.nonisotropicLastExtension a ha)
      |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isMulRightInvariant
  calc
    ∫ x, f x *
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha g
          (QuotientGroup.mk x) ∂μG =
        ∫ x, ∫ h : H, f x * g (x * h.1) ∂μH ∂μG := by
          congr 1 with x
          rw [W.fullAdelicNonisotropicLastShellStabilizerAverageMap_mk a ha g x]
          unfold fullAdelicNonisotropicLastShellStabilizerAverage
          rw [integral_const_mul]
    _ = ∫ h : H, ∫ x, f x * g (x * h.1) ∂μG ∂μH := by
      apply integral_integral_swap_of_hasCompactSupport
      · exact f.continuous.comp continuous_fst |>.mul
          (g.continuous.comp (continuous_fst.mul continuous_snd.subtype_val))
      · exact W.hasCompactSupport_fullAdelicNonisotropicLastShell_fiberSwapJoint
          a ha f g
    _ = ∫ h : H, ∫ x, f (x * h.1⁻¹) * g x ∂μG ∂μH := by
      congr 1 with h
      rw [← integral_mul_right_eq_self
        (fun x ↦ f (x * h.1⁻¹) * g x) h.1]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    _ = ∫ h : H, ∫ x, f (x * h.1) * g x ∂μG ∂μH := by
      simpa only [Subgroup.coe_inv] using
        (integral_inv_eq_self
          (fun h : H ↦ ∫ x, f (x * h.1) * g x ∂μG) μH)
    _ = ∫ x, ∫ h : H, f (x * h.1) * g x ∂μH ∂μG := by
      apply integral_integral_swap_of_hasCompactSupport
      · exact (f.continuous.comp
          (continuous_snd.mul continuous_fst.subtype_val)).mul
            (g.continuous.comp continuous_snd)
      · have hsupport :=
          W.hasCompactSupport_fullAdelicNonisotropicLastShell_fiberSwapJoint
            a ha g f
        simpa only [Function.comp_apply, Homeomorph.coe_prodComm,
          mul_comm] using
          hsupport.comp_homeomorph (Homeomorph.prodComm H G)
    _ = ∫ x, g x *
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f
          (QuotientGroup.mk x) ∂μG := by
      congr 1 with x
      rw [W.fullAdelicNonisotropicLastShellStabilizerAverageMap_mk a ha f x]
      unfold fullAdelicNonisotropicLastShellStabilizerAverage
      rw [integral_mul_const]
      exact mul_comm _ _

/-- The fixed ambient Haar integral annihilates the kernel of the stabilizer
average. -/
theorem integral_fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_eq_zero_of_average_eq_zero
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ))
    (haverage :
      W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f = 0) :
    ∫ x, f x
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) = 0 := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let q : G → X := QuotientGroup.mk
  let μG := (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let K : Set X := q '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_quotient_mk'
  obtain ⟨β, -, hβaverage⟩ :=
    W.exists_fullAdelicNonisotropicLastShell_nonnegative_average_one_on_compact
      a ha K hK
  have hfcutoff : ∀ x : G,
      f x * W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha β (q x) =
        f x := by
    intro x
    by_cases hfx : f x = 0
    · simp [hfx]
    · rw [hβaverage (q x) ⟨x, subset_tsupport f hfx, rfl⟩, mul_one]
  calc
    ∫ x, f x ∂μG =
        ∫ x, f x *
          W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha β (q x)
          ∂μG := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (hfcutoff x).symm)
    _ = ∫ x, β x *
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f (q x)
        ∂μG :=
      W.integral_mul_fullAdelicNonisotropicLastShellStabilizerAverageMap_comm
        a ha f β
    _ = 0 := by rw [haverage]; simp

/-- Ambient Haar integration is independent of the selected compactly
supported continuous lift through the stabilizer-average operator. -/
theorem integral_fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_eq_of_average_eq
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f g : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ))
    (haverage :
      W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f =
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha g) :
    ∫ x, f x
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      ∫ x, g x
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let q : G → X := QuotientGroup.mk
  let μG := (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let K : Set X := q '' (tsupport f ∪ tsupport g)
  have hK : IsCompact K :=
    (f.hasCompactSupport.union g.hasCompactSupport).image continuous_quotient_mk'
  obtain ⟨β, -, hβaverage⟩ :=
    W.exists_fullAdelicNonisotropicLastShell_nonnegative_average_one_on_compact
      a ha K hK
  have hfcutoff : ∀ x : G,
      f x * W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha β (q x) =
        f x := by
    intro x
    by_cases hfx : f x = 0
    · simp [hfx]
    · rw [hβaverage (q x)
        ⟨x, Or.inl (subset_tsupport f hfx), rfl⟩, mul_one]
  have hgcutoff : ∀ x : G,
      g x * W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha β (q x) =
        g x := by
    intro x
    by_cases hgx : g x = 0
    · simp [hgx]
    · rw [hβaverage (q x)
        ⟨x, Or.inr (subset_tsupport g hgx), rfl⟩, mul_one]
  calc
    ∫ x, f x ∂μG =
        ∫ x, f x *
          W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha β (q x)
          ∂μG := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (hfcutoff x).symm)
    _ = ∫ x, β x *
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f (q x)
        ∂μG :=
      W.integral_mul_fullAdelicNonisotropicLastShellStabilizerAverageMap_comm
        a ha f β
    _ = ∫ x, β x *
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha g (q x)
        ∂μG := by rw [haverage]
    _ = ∫ x, g x *
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha β (q x)
        ∂μG :=
      (W.integral_mul_fullAdelicNonisotropicLastShellStabilizerAverageMap_comm
        a ha g β).symm
    _ = ∫ x, g x ∂μG := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hgcutoff

end RationalQuadraticSpaceMatrix
