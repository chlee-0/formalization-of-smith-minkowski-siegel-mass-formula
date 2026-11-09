import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellOrbitFiberKernel
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal

/-!
# Binding the native GSpin shell orbit-fiber kernel

The canonical Riesz measure on the native shell quotient, bound against the
literal translated-stabilizer-Haar kernel, is exactly the established ambient
horizontal GSpin Haar measure.  The proof first compares nonnegative compactly
supported continuous functions, proves the bound measure finite on compact
sets, and then applies regular-measure uniqueness.  No section is used.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open ProbabilityTheory
open Set
open scoped CompactlySupported Topology ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000

variable {n : ℕ}

local instance fullAdelicShellKernelBindInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellKernelBindFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellKernelBindT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellKernelBindSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellKernelBindSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance fullAdelicShellKernelBindSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellKernelBindSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellKernelBindStabilizerSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

noncomputable local instance fullAdelicShellKernelBindStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellKernelBindQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance fullAdelicShellKernelBindQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellKernelBindQuotientLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instLocallyCompactSpace
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellKernelBindQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance fullAdelicShellKernelBindQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

/-- Binding the canonical quotient Riesz measure against the native orbit
fiber kernel. -/
noncomputable def fullAdelicNonisotropicLastShellOrbitFiberBindMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure ((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :=
  (W.fullAdelicNonisotropicLastShellQuotientMeasure a ha).bind
    (W.fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel a ha)

/-- A nonnegative compactly supported continuous function integrates along one
orbit fiber to the nonnegative real stabilizer average. -/
theorem lintegral_fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, NNReal))
    (x : W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :
    ∫⁻ g, (f g : ℝ≥0∞)
        ∂W.fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel a ha x =
      ENNReal.ofReal
        (W.fullAdelicNonisotropicLastShellStabilizerAverageMap
          a ha f.toReal x) := by
  induction x using Quotient.inductionOn' with
  | _ g =>
      rw [W.fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel_mk a ha g]
      rw [MeasureTheory.lintegral_map]
      · rw [W.fullAdelicNonisotropicLastShellStabilizerAverageMap_mk]
        rw [fullAdelicNonisotropicLastShellStabilizerAverage]
        rw [ofReal_integral_eq_lintegral_ofReal]
        · congr 1
          funext h
          simp
        · exact
            W.integrable_fullAdelicNonisotropicLastShell_stabilizer_translate
              a ha f.toReal g
        · exact Filter.Eventually.of_forall fun h ↦ by simp
      · fun_prop
      · fun_prop

/-- Binding the native orbit-fiber kernel preserves every nonnegative compactly
supported continuous integral at coefficient one. -/
theorem lintegral_fullAdelicNonisotropicLastShellOrbitFiberBindMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, NNReal)) :
    ∫⁻ g, (f g : ℝ≥0∞)
        ∂W.fullAdelicNonisotropicLastShellOrbitFiberBindMeasure a ha =
      ∫⁻ g, (f g : ℝ≥0∞)
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
  let μX := W.fullAdelicNonisotropicLastShellQuotientMeasure a ha
  let κ := W.fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel a ha
  let μG := (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let A := W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f.toReal
  letI : μX.Regular := by
    dsimp [μX]
    change (RealRMK.rieszMeasure
      (W.fullAdelicNonisotropicLastShellPositiveLinearMap a ha)).Regular
    exact RealRMK.regular_rieszMeasure
      (Λ := W.fullAdelicNonisotropicLastShellPositiveLinearMap a ha)
  have hA_nonneg : ∀ x, 0 ≤ A x := by
    intro x
    induction x using Quotient.inductionOn' with
    | _ g =>
        rw [fullAdelicNonisotropicLastShellStabilizerAverageMap_mk]
        exact integral_nonneg fun h ↦ by simp
  have hA_integrable : Integrable A μX := by
    exact A.continuous.integrable_of_hasCompactSupport A.hasCompactSupport
  have hf_integrable : Integrable f.toReal μG :=
    f.toReal.continuous.integrable_of_hasCompactSupport f.toReal.hasCompactSupport
  rw [fullAdelicNonisotropicLastShellOrbitFiberBindMeasure]
  rw [Measure.lintegral_bind κ.aemeasurable (by fun_prop)]
  have hfiber :
      (fun x ↦ ∫⁻ g, (f g : ℝ≥0∞) ∂κ x) =
        (fun x ↦ ENNReal.ofReal (A x)) := by
    funext x
    exact W.lintegral_fullAdelicNonisotropicLastShellQuotientOrbitFiberKernel
      a ha f x
  rw [hfiber]
  rw [← ofReal_integral_eq_lintegral_ofReal hA_integrable
    (Filter.Eventually.of_forall hA_nonneg)]
  rw [W.integral_fullAdelicNonisotropicLastShellStabilizerAverageMap a ha f.toReal]
  rw [ofReal_integral_eq_lintegral_ofReal hf_integrable
    (Filter.Eventually.of_forall fun g ↦ by simp)]
  congr 1
  funext g
  simp

/-- The bound quotient/fiber measure is finite on compact ambient sets.  A
Urysohn bump equal to one on the compact set reduces the claim to the closed
coefficient-one compactly supported integral identity. -/
theorem fullAdelicNonisotropicLastShellOrbitFiberBindMeasure_isFiniteMeasureOnCompacts
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsFiniteMeasureOnCompacts
      (W.fullAdelicNonisotropicLastShellOrbitFiberBindMeasure a ha) := by
  constructor
  intro K hK
  obtain ⟨b, hbK, -, hbcompact, hbmem⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty
      (disjoint_empty K)
  let βR : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ) := ⟨b, hbcompact⟩
  let β : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, NNReal) := βR.nnrealPart
  let μB := W.fullAdelicNonisotropicLastShellOrbitFiberBindMeasure a ha
  let μG := (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hindicator :
      ∫⁻ x, K.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂μB = μB K :=
    lintegral_indicator_one hKmeas
  have hpoint : ∀ x,
      K.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ (β x : ℝ≥0∞) := by
    intro x
    by_cases hx : x ∈ K
    · have hb_one : βR x = 1 := hbK hx
      simp [hx, β, hb_one]
    · simp [hx]
  have hβ_integrable : Integrable β.toReal μG :=
    β.toReal.continuous.integrable_of_hasCompactSupport β.toReal.hasCompactSupport
  have hβ_finite : (∫⁻ x, (β x : ℝ≥0∞) ∂μG) < ∞ := by
    have hcoe : (fun x ↦ (β x : ℝ≥0∞)) =
        (fun x ↦ ENNReal.ofReal (β.toReal x)) := by
      funext x
      simp
    rw [hcoe, ← ofReal_integral_eq_lintegral_ofReal hβ_integrable
      (Filter.Eventually.of_forall fun x ↦ by simp)]
    exact ENNReal.ofReal_lt_top
  rw [← hindicator]
  exact (lintegral_mono hpoint).trans_lt <|
    (W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberBindMeasure
      a ha β).trans_lt hβ_finite

noncomputable instance
    fullAdelicNonisotropicLastShellOrbitFiberBindMeasureFiniteOnCompacts
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsFiniteMeasureOnCompacts
      (W.fullAdelicNonisotropicLastShellOrbitFiberBindMeasure a ha) :=
  W.fullAdelicNonisotropicLastShellOrbitFiberBindMeasure_isFiniteMeasureOnCompacts
    a ha

/-- The bound measure and ambient horizontal Haar give the same real integral
to every nonnegative compactly supported continuous test function. -/
theorem integral_fullAdelicNonisotropicLastShellOrbitFiberBindMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, NNReal)) :
    ∫ g, (f g : ℝ)
        ∂W.fullAdelicNonisotropicLastShellOrbitFiberBindMeasure a ha =
      ∫ g, (f g : ℝ)
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
  let μB := W.fullAdelicNonisotropicLastShellOrbitFiberBindMeasure a ha
  let μG := (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  have hB0 : Integrable f.toReal μB :=
    f.toReal.continuous.integrable_of_hasCompactSupport f.toReal.hasCompactSupport
  have hG0 : Integrable f.toReal μG :=
    f.toReal.continuous.integrable_of_hasCompactSupport f.toReal.hasCompactSupport
  have hB : Integrable (fun g ↦ (f g : ℝ)) μB := by
    apply hB0.congr
    filter_upwards with g
    simp
  have hG : Integrable (fun g ↦ (f g : ℝ)) μG := by
    apply hG0.congr
    filter_upwards with g
    simp
  have hlin :=
    W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberBindMeasure a ha f
  rw [lintegral_coe_eq_integral f hB, lintegral_coe_eq_integral f hG] at hlin
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg fun g ↦ by simp)
    (integral_nonneg fun g ↦ by simp)).mp hlin

/-- The canonical quotient Riesz measure bound against the literal translated
complement-stabilizer Haar kernel is exactly the established ambient
horizontal GSpin Haar. -/
theorem fullAdelicNonisotropicLastShellOrbitFiberBindMeasure_eq_horizontal
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.fullAdelicNonisotropicLastShellOrbitFiberBindMeasure a ha =
      (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  let μB := W.fullAdelicNonisotropicLastShellOrbitFiberBindMeasure a ha
  let μG := (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  letI : μB.Regular := by infer_instance
  letI : μG.Regular := by infer_instance
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  exact W.integral_fullAdelicNonisotropicLastShellOrbitFiberBindMeasure a ha

end RationalQuadraticSpaceMatrix
