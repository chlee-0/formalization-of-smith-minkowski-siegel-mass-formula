import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellFiberSwap
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Riesz measure on the full-adelic block-shell quotient

Ambient horizontal Haar integration factors through the section-free
stabilizer-average operator.  The resulting positive functional on the native
homogeneous-space quotient defines its normalized Riesz measure.  The public
endpoint is the coefficient-one Weil identity for compactly supported
continuous functions.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open Set
open scoped CompactlySupported Topology

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000

variable {n : ℕ}

local instance fullAdelicShellRieszInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellRieszFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellRieszT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellRieszSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellRieszSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance fullAdelicShellRieszSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellRieszSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellRieszStabilizerSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

noncomputable local instance fullAdelicShellRieszStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellRieszQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance fullAdelicShellRieszQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance fullAdelicShellRieszQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

/-- Stabilizer averaging is additive. -/
theorem fullAdelicNonisotropicLastShellStabilizerAverageMap_add
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f g : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha (f + g) =
      W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f +
        W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha g := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  induction x using Quotient.inductionOn' with
  | _ y =>
      simp only [fullAdelicNonisotropicLastShellStabilizerAverageMap_mk,
        fullAdelicNonisotropicLastShellStabilizerAverage]
      change (∫ h, f (y * h.1) + g (y * h.1)
          ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
            a ha) =
        (∫ h, f (y * h.1)
          ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
            a ha) +
        ∫ h, g (y * h.1)
          ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
            a ha
      rw [integral_add
        (W.integrable_fullAdelicNonisotropicLastShell_stabilizer_translate
          a ha f y)
        (W.integrable_fullAdelicNonisotropicLastShell_stabilizer_translate
          a ha g y)]

/-- Stabilizer averaging commutes with real scalar multiplication. -/
theorem fullAdelicNonisotropicLastShellStabilizerAverageMap_smul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (c : ℝ)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha (c • f) =
      c • W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  induction x using Quotient.inductionOn' with
  | _ y =>
      simp only [fullAdelicNonisotropicLastShellStabilizerAverageMap_mk,
        fullAdelicNonisotropicLastShellStabilizerAverage]
      change (∫ h, c • f (y * h.1)
          ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
            a ha) =
        c • ∫ h, f (y * h.1)
          ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
            a ha
      rw [integral_smul]

/-- Every signed compactly supported continuous quotient function has an
ambient compactly supported continuous stabilizer-average lift.  The
construction multiplies by one compact-local average-one cutoff and chooses no
quotient representative. -/
theorem exists_fullAdelicNonisotropicLastShell_stabilizerAverage_lift
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ)) :
    ∃ F : C_c((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup, ℝ),
      W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha F = φ := by
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let H := W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let q : G → X := QuotientGroup.mk
  obtain ⟨β, -, hβaverage⟩ :=
    W.exists_fullAdelicNonisotropicLastShell_nonnegative_average_one_on_compact
      a ha (tsupport φ) φ.hasCompactSupport
  let F : C_c(G, ℝ) :=
    { toFun := fun g ↦ β g * φ (q g)
      continuous_toFun :=
        β.continuous.mul (φ.continuous.comp continuous_quotient_mk')
      hasCompactSupport' := β.hasCompactSupport.mul_right }
  refine ⟨F, ?_⟩
  apply CompactlySupportedContinuousMap.ext
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
      change (∫ h : H, β (g * h.1) * φ (q (g * h.1))
          ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
            a ha) = φ (q g)
      simp_rw [hqmul]
      rw [integral_mul_const]
      by_cases hzero : φ (q g) = 0
      · simp [hzero]
      · have havg :
            (∫ h : H, β (g * h.1)
              ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
                a ha) = 1 := by
          simpa only [q,
            W.fullAdelicNonisotropicLastShellStabilizerAverageMap_mk,
            fullAdelicNonisotropicLastShellStabilizerAverage] using
            hβaverage (q g) (subset_tsupport φ hzero)
        rw [havg, one_mul]

/-- One arbitrary function lift used only to define the quotient functional.
Lift independence below removes the choice from every public value theorem. -/
noncomputable def fullAdelicNonisotropicLastShellChosenAverageLift
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ)) :
    C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ) :=
  Classical.choose
    (W.exists_fullAdelicNonisotropicLastShell_stabilizerAverage_lift a ha φ)

@[simp]
theorem fullAdelicNonisotropicLastShellChosenAverageLift_average
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ)) :
    W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha
        (W.fullAdelicNonisotropicLastShellChosenAverageLift a ha φ) = φ :=
  Classical.choose_spec
    (W.exists_fullAdelicNonisotropicLastShell_stabilizerAverage_lift a ha φ)

/-- The canonical quotient functional obtained by factoring ambient horizontal
Haar integration through stabilizer averaging. -/
noncomputable def fullAdelicNonisotropicLastShellQuotientIntegral
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ)) : ℝ :=
  ∫ g, W.fullAdelicNonisotropicLastShellChosenAverageLift a ha φ g
    ∂((W.nonisotropicLastExtension a ha)
      |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)

/-- Any ambient lift computes the canonical quotient functional. -/
theorem fullAdelicNonisotropicLastShellQuotientIntegral_eq_integral_of_average_eq
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ))
    (F : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ))
    (hF : W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha F = φ) :
    W.fullAdelicNonisotropicLastShellQuotientIntegral a ha φ =
      ∫ g, F g
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
  unfold fullAdelicNonisotropicLastShellQuotientIntegral
  apply
    W.integral_fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_eq_of_average_eq
      a ha
  rw [W.fullAdelicNonisotropicLastShellChosenAverageLift_average a ha φ, hF]

/-- The quotient integral is additive. -/
theorem fullAdelicNonisotropicLastShellQuotientIntegral_add
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (φ ψ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ)) :
    W.fullAdelicNonisotropicLastShellQuotientIntegral a ha (φ + ψ) =
      W.fullAdelicNonisotropicLastShellQuotientIntegral a ha φ +
        W.fullAdelicNonisotropicLastShellQuotientIntegral a ha ψ := by
  let μ := (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let F := W.fullAdelicNonisotropicLastShellChosenAverageLift a ha φ
  let G := W.fullAdelicNonisotropicLastShellChosenAverageLift a ha ψ
  have hFint : Integrable (fun g ↦ F g) μ :=
    F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport
  have hGint : Integrable (fun g ↦ G g) μ :=
    G.continuous.integrable_of_hasCompactSupport G.hasCompactSupport
  rw [W.fullAdelicNonisotropicLastShellQuotientIntegral_eq_integral_of_average_eq
    a ha (φ + ψ) (F + G)]
  · change (∫ g, F g + G g ∂μ) =
      (∫ g, F g ∂μ) + ∫ g, G g ∂μ
    rw [integral_add hFint hGint]
  · rw [W.fullAdelicNonisotropicLastShellStabilizerAverageMap_add,
      W.fullAdelicNonisotropicLastShellChosenAverageLift_average,
      W.fullAdelicNonisotropicLastShellChosenAverageLift_average]

/-- The quotient integral commutes with real scalar multiplication. -/
theorem fullAdelicNonisotropicLastShellQuotientIntegral_smul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (c : ℝ)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ)) :
    W.fullAdelicNonisotropicLastShellQuotientIntegral a ha (c • φ) =
      c • W.fullAdelicNonisotropicLastShellQuotientIntegral a ha φ := by
  let F := W.fullAdelicNonisotropicLastShellChosenAverageLift a ha φ
  rw [W.fullAdelicNonisotropicLastShellQuotientIntegral_eq_integral_of_average_eq
    a ha (c • φ) (c • F)]
  · change (∫ g, c • F g
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)) =
      c • ∫ g, F g
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)
    rw [integral_smul]
  · rw [W.fullAdelicNonisotropicLastShellStabilizerAverageMap_smul,
      W.fullAdelicNonisotropicLastShellChosenAverageLift_average]

/-- The canonical quotient integral as a positive real-linear functional. -/
noncomputable def fullAdelicNonisotropicLastShellPositiveLinearMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ) →ₚ[ℝ] ℝ :=
  { toLinearMap :=
      { toFun := W.fullAdelicNonisotropicLastShellQuotientIntegral a ha
        map_add' := W.fullAdelicNonisotropicLastShellQuotientIntegral_add a ha
        map_smul' := W.fullAdelicNonisotropicLastShellQuotientIntegral_smul a ha }
    monotone' := by
      intro φ ψ hφψ
      have hnonneg : ∀ x, 0 ≤ (ψ - φ) x := fun x ↦ sub_nonneg.mpr (hφψ x)
      obtain ⟨F, hFnonneg, hFaverage⟩ :=
        W.exists_fullAdelicNonisotropicLastShell_nonnegative_stabilizerAverage_lift
          a ha (ψ - φ) hnonneg
      have hΛdiff :=
        W.fullAdelicNonisotropicLastShellQuotientIntegral_eq_integral_of_average_eq
          a ha (ψ - φ) F hFaverage
      have hintegral_nonneg : 0 ≤ ∫ g, F g
          ∂((W.nonisotropicLastExtension a ha)
            |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) :=
        integral_nonneg hFnonneg
      have hΛsub :
          W.fullAdelicNonisotropicLastShellQuotientIntegral a ha (ψ - φ) =
            W.fullAdelicNonisotropicLastShellQuotientIntegral a ha ψ -
              W.fullAdelicNonisotropicLastShellQuotientIntegral a ha φ := by
        rw [sub_eq_add_neg,
          W.fullAdelicNonisotropicLastShellQuotientIntegral_add]
        rw [show -φ = (-1 : ℝ) • φ from (neg_one_smul ℝ φ).symm,
          W.fullAdelicNonisotropicLastShellQuotientIntegral_smul]
        rw [neg_one_smul, sub_eq_add_neg]
      rw [hΛsub] at hΛdiff
      linarith }

/-- The native homogeneous-space quotient measure supplied by the real
Riesz--Markov--Kakutani theorem at the fixed Haar normalization. -/
noncomputable def fullAdelicNonisotropicLastShellQuotientMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  RealRMK.rieszMeasure
    (W.fullAdelicNonisotropicLastShellPositiveLinearMap a ha)

/-- The Riesz measure integrates every quotient `C_c` function to the
canonical quotient functional. -/
@[simp]
theorem integral_fullAdelicNonisotropicLastShellQuotientMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ)) :
    ∫ x, φ x ∂W.fullAdelicNonisotropicLastShellQuotientMeasure a ha =
      W.fullAdelicNonisotropicLastShellQuotientIntegral a ha φ := by
  exact RealRMK.integral_rieszMeasure
    (W.fullAdelicNonisotropicLastShellPositiveLinearMap a ha) φ

/-- The coefficient-one compactly supported continuous Weil identity. -/
theorem integral_fullAdelicNonisotropicLastShellStabilizerAverageMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (F : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    ∫ x, W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha F x
        ∂W.fullAdelicNonisotropicLastShellQuotientMeasure a ha =
      ∫ g, F g
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
  rw [W.integral_fullAdelicNonisotropicLastShellQuotientMeasure]
  exact W.fullAdelicNonisotropicLastShellQuotientIntegral_eq_integral_of_average_eq
    a ha _ F rfl

end RationalQuadraticSpaceMatrix
