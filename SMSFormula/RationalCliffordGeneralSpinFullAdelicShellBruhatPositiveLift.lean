import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellStabilizerAverage
import Mathlib.Topology.UrysohnsLemma

/-!
# Positive Bruhat lifting on the full-adelic block shell

This file constructs the positive compactly supported lift required by the
section-free Riesz construction on the block-shell homogeneous space.  The
construction uses only compact quotient covers and ambient Urysohn functions;
it does not choose a global quotient section.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open Set
open scoped CompactlySupported Topology

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000

variable {n : ℕ}

local instance fullAdelicShellBruhatInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellBruhatFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellBruhatT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellBruhatSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellBruhatSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance fullAdelicShellBruhatSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellBruhatSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellBruhatStabilizerSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

noncomputable local instance fullAdelicShellBruhatStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellBruhatQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

/-- Every compact subset of the native homogeneous-space quotient is covered
by the quotient image of one compact ambient set.  The proof uses finitely
many local compact neighborhoods, not a global section. -/
theorem exists_compact_fullAdelicNonisotropicLastShell_quotient_preimage_cover
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (K : Set (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha))
    (hK : IsCompact K) :
    ∃ C : Set ((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup),
      IsCompact C ∧ K ⊆ QuotientGroup.mk '' C := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let q : G → X := QuotientGroup.mk
  have hlocal : ∀ x : X, ∃ C : Set G, IsCompact C ∧
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ q '' C := by
    intro x
    induction x using Quotient.inductionOn' with
    | _ g =>
        obtain ⟨C, hCcompact, hCnhds⟩ :
            ∃ C : Set G, IsCompact C ∧ C ∈ 𝓝 g :=
          exists_compact_mem_nhds g
        refine ⟨C, hCcompact, q '' interior C, ?_, ?_, Set.image_mono interior_subset⟩
        · exact QuotientGroup.isOpenMap_coe (interior C) isOpen_interior
        · exact ⟨g, mem_interior_iff_mem_nhds.2 hCnhds, rfl⟩
  choose C hCcompact U hUopen hxU hUC using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hUopen
    (fun x _ ↦ mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨⋃ x ∈ s, C x, s.isCompact_biUnion (fun x _ ↦ hCcompact x), ?_⟩
  intro x hx
  have hxcover := hs hx
  rw [Set.mem_iUnion] at hxcover
  obtain ⟨i, hi⟩ := hxcover
  rw [Set.mem_iUnion] at hi
  obtain ⟨hiS, hxiU⟩ := hi
  obtain ⟨g, hgC, hqg⟩ := hUC i hxiU
  refine ⟨g, ?_, hqg⟩
  rw [Set.mem_iUnion]
  refine ⟨i, ?_⟩
  rw [Set.mem_iUnion]
  exact ⟨hiS, hgC⟩

/-- A stabilizer translate of an ambient compactly supported continuous
function still has compact support on the literal stabilizer. -/
theorem hasCompactSupport_fullAdelicNonisotropicLastShell_stabilizer_translate
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ))
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    HasCompactSupport
      (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer
          a ha ↦ f (g * h.1)) := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let H := W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha
  let ambientBound : Set G :=
    (fun x : G ↦ g⁻¹ * x) '' tsupport f
  have hambientBound : IsCompact ambientBound :=
    f.hasCompactSupport.image (continuous_const.mul continuous_id)
  let stabilizerBound : Set H :=
    (Subtype.val : H → G) ⁻¹' ambientBound
  have hstabilizerBound : IsCompact stabilizerBound :=
    (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele).isClosedEmbedding_subtypeVal.isCompact_preimage
      hambientBound
  apply HasCompactSupport.of_support_subset_isCompact hstabilizerBound
  intro h hh
  change h.1 ∈ ambientBound
  have hmem : g * h.1 ∈ tsupport f := by
    have hne : f (g * h.1) ≠ 0 := hh
    by_contra hnot
    exact hne (image_eq_zero_of_notMem_tsupport hnot)
  refine ⟨g * h.1, hmem, ?_⟩
  change g⁻¹ * (g * h.1) = h.1
  rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- A stabilizer translate of an ambient compactly supported continuous
function is integrable against the fixed stabilizer Haar. -/
theorem integrable_fullAdelicNonisotropicLastShell_stabilizer_translate
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ))
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    Integrable
      (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer
          a ha ↦ f (g * h.1))
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) := by
  exact
    (f.continuous.comp (continuous_const.mul continuous_subtype_val))
      |>.integrable_of_hasCompactSupport
        (W.hasCompactSupport_fullAdelicNonisotropicLastShell_stabilizer_translate
          a ha f g)

/-- On every compact quotient set there is one nonnegative ambient Bruhat
bump whose stabilizer average is strictly positive throughout that set. -/
theorem exists_fullAdelicNonisotropicLastShell_nonnegative_average_pos_on_compact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (K : Set (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha))
    (hK : IsCompact K) :
    ∃ β : C_c((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup, ℝ),
      (∀ g, 0 ≤ β g) ∧
      ∀ x ∈ K,
        0 < W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha β x := by
  obtain ⟨C, hCcompact, hKC⟩ :=
    W.exists_compact_fullAdelicNonisotropicLastShell_quotient_preimage_cover
      a ha K hK
  obtain ⟨b, hbC, -, hbcompact, hbmem⟩ :=
    exists_continuous_one_zero_of_isCompact hCcompact isClosed_empty
      (disjoint_empty C)
  let β : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ) := ⟨b, hbcompact⟩
  refine ⟨β, fun g ↦ (hbmem g).1, ?_⟩
  intro x hx
  obtain ⟨g, hgC, hqg⟩ := hKC hx
  rw [← hqg]
  change 0 < W.fullAdelicNonisotropicLastShellStabilizerAverage a ha β g
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
      a ha)
    (x := (1 : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer
      a ha))
  · exact β.continuous.comp (continuous_const.mul continuous_subtype_val)
  · exact
      W.hasCompactSupport_fullAdelicNonisotropicLastShell_stabilizer_translate
        a ha β g
  · intro h
    exact (hbmem (g * h.1)).1
  · simpa [β, hbC hgC] using (one_ne_zero : (1 : ℝ) ≠ 0)

/-- Every nonnegative compactly supported continuous function on the native
homogeneous-space quotient is the stabilizer average of a nonnegative ambient
compactly supported continuous function.  The lift is assembled from one
ambient Bruhat bump and the quotient function itself; no quotient section is
chosen. -/
theorem exists_fullAdelicNonisotropicLastShell_nonnegative_stabilizerAverage_lift
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ))
    (hφ : ∀ x, 0 ≤ φ x) :
    ∃ F : C_c((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup, ℝ),
      (∀ g, 0 ≤ F g) ∧
      W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha F = φ := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let H := W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let q : G → X := QuotientGroup.mk
  obtain ⟨β, hβ, hBpos⟩ :=
    W.exists_fullAdelicNonisotropicLastShell_nonnegative_average_pos_on_compact
      a ha (tsupport φ) φ.hasCompactSupport
  let B : C_c(X, ℝ) :=
    W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha β
  obtain ⟨δ, hδpos, hδle⟩ :=
    φ.hasCompactSupport.exists_forall_le' B.continuous.continuousOn hBpos
  let ψ : X → ℝ := fun x ↦ φ x / max (B x) δ
  have hdenom_pos : ∀ x : X, 0 < max (B x) δ := fun x ↦
    lt_of_lt_of_le hδpos (le_max_right _ _)
  have hψcontinuous : Continuous ψ :=
    φ.continuous.div (B.continuous.max continuous_const)
      (fun x ↦ (hdenom_pos x).ne')
  let F : C_c(G, ℝ) :=
    { toFun := fun g ↦ β g * ψ (q g)
      continuous_toFun :=
        β.continuous.mul (hψcontinuous.comp continuous_quotient_mk')
      hasCompactSupport' :=
        β.hasCompactSupport.mul_right }
  refine ⟨F, ?_, ?_⟩
  · intro g
    exact mul_nonneg (hβ g) (div_nonneg (hφ (q g)) (le_of_lt (hdenom_pos (q g))))
  · apply CompactlySupportedContinuousMap.ext
    intro x
    induction x using Quotient.inductionOn' with
    | _ g =>
        have hqmul : ∀ h : H, q (g * h.1) = q g := by
          intro h
          apply Quotient.sound'
          rw [QuotientGroup.leftRel_apply]
          simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using
            (Subgroup.inv_mem
              (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
                a ha RationalAdele) h.2)
        rw [W.fullAdelicNonisotropicLastShellStabilizerAverageMap_mk a ha F g]
        change (∫ h : H, β (g * h.1) * ψ (q (g * h.1))
            ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
              a ha) = φ (q g)
        simp_rw [hqmul]
        rw [integral_mul_const]
        change B (q g) * ψ (q g) = φ (q g)
        by_cases hzero : φ (q g) = 0
        · simp [ψ, hzero]
        · have hmem : q g ∈ tsupport φ := by
            by_contra hnot
            exact hzero (image_eq_zero_of_notMem_tsupport hnot)
          change B (q g) * (φ (q g) / max (B (q g)) δ) = φ (q g)
          rw [show max (B (q g)) δ = B (q g) from max_eq_left (hδle _ hmem)]
          exact mul_div_cancel₀ _ (hBpos _ hmem).ne'

end RationalQuadraticSpaceMatrix
