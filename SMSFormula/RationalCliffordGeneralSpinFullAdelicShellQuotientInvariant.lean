import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellRieszMeasure

/-!
# Left invariance of the full-adelic block-shell quotient measure

The native right-coset quotient carries the canonical left action of ambient
full-adelic `GSpin`.  This file proves that the coefficient-one Riesz measure
is invariant under that action.  The proof translates an ambient `C_c` lift,
uses left invariance of the fixed horizontal Haar measure, and then invokes
regular-measure uniqueness.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open Set
open scoped CompactlySupported Topology

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000

variable {n : ℕ}

local instance fullAdelicShellInvariantInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellInvariantFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellInvariantT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellInvariantSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellInvariantSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance fullAdelicShellInvariantSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellInvariantSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellInvariantStabilizerSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

noncomputable local instance fullAdelicShellInvariantStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellInvariantQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance fullAdelicShellInvariantQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance fullAdelicShellInvariantQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

/-- Pull a quotient `C_c` function back along left multiplication by an
ambient full-adelic `GSpin` point. -/
noncomputable def fullAdelicNonisotropicLastShellQuotientLeftTranslate
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ)) :
    C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ) :=
  { toFun := fun x ↦ φ (g • x)
    continuous_toFun := φ.continuous.comp (continuous_const_smul g)
    hasCompactSupport' :=
      φ.hasCompactSupport.comp_homeomorph (Homeomorph.smul g) }

@[simp]
theorem fullAdelicNonisotropicLastShellQuotientLeftTranslate_apply
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ))
    (x : W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :
    W.fullAdelicNonisotropicLastShellQuotientLeftTranslate a ha g φ x =
      φ (g • x) :=
  rfl

/-- Pull an ambient `C_c` function back along left multiplication. -/
noncomputable def fullAdelicNonisotropicLastShellAmbientLeftTranslate
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (F : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ) :=
  { toFun := fun x ↦ F (g * x)
    continuous_toFun := F.continuous.comp (continuous_const.mul continuous_id)
    hasCompactSupport' :=
      F.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft g) }

@[simp]
theorem fullAdelicNonisotropicLastShellAmbientLeftTranslate_apply
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g x : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (F : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    W.fullAdelicNonisotropicLastShellAmbientLeftTranslate a ha g F x =
      F (g * x) :=
  rfl

/-- Stabilizer averaging intertwines ambient and quotient left translation. -/
theorem fullAdelicNonisotropicLastShellStabilizerAverageMap_leftTranslate
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (F : C_c((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup, ℝ)) :
    W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha
        (W.fullAdelicNonisotropicLastShellAmbientLeftTranslate a ha g F) =
      W.fullAdelicNonisotropicLastShellQuotientLeftTranslate a ha g
        (W.fullAdelicNonisotropicLastShellStabilizerAverageMap a ha F) := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  induction x using Quotient.inductionOn' with
  | _ y =>
      simp only [fullAdelicNonisotropicLastShellStabilizerAverageMap_mk,
        fullAdelicNonisotropicLastShellAmbientLeftTranslate_apply,
        fullAdelicNonisotropicLastShellQuotientLeftTranslate_apply,
        MulAction.Quotient.smul_mk, smul_eq_mul,
        fullAdelicNonisotropicLastShellStabilizerAverage]
      congr 1 with h
      rw [mul_assoc]

/-- The canonical quotient functional is invariant under the ambient left
action. -/
theorem fullAdelicNonisotropicLastShellQuotientIntegral_leftTranslate
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (φ : C_c(W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha, ℝ)) :
    W.fullAdelicNonisotropicLastShellQuotientIntegral a ha
        (W.fullAdelicNonisotropicLastShellQuotientLeftTranslate a ha g φ) =
      W.fullAdelicNonisotropicLastShellQuotientIntegral a ha φ := by
  let F := W.fullAdelicNonisotropicLastShellChosenAverageLift a ha φ
  letI : Measure.IsMulLeftInvariant
      ((W.nonisotropicLastExtension a ha)
        |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) :=
    (W.nonisotropicLastExtension a ha)
      |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
      |>.toIsMulLeftInvariant
  rw [W.fullAdelicNonisotropicLastShellQuotientIntegral_eq_integral_of_average_eq
    a ha _ (W.fullAdelicNonisotropicLastShellAmbientLeftTranslate a ha g F)]
  · change (∫ x, F (g * x)
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)) = _
    rw [integral_mul_left_eq_self]
    rfl
  · rw [W.fullAdelicNonisotropicLastShellStabilizerAverageMap_leftTranslate,
      W.fullAdelicNonisotropicLastShellChosenAverageLift_average]

/-- The native Riesz quotient measure is literally invariant under left
multiplication by every ambient full-adelic `GSpin` point. -/
theorem map_fullAdelicNonisotropicLastShellQuotientMeasure_smul
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map (fun x : W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha ↦
        g • x)
        (W.fullAdelicNonisotropicLastShellQuotientMeasure a ha) =
      W.fullAdelicNonisotropicLastShellQuotientMeasure a ha := by
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let μ := W.fullAdelicNonisotropicLastShellQuotientMeasure a ha
  let e : X ≃ₜ X := Homeomorph.smul g
  change Measure.map e μ = μ
  letI : μ.Regular := RealRMK.regular_rieszMeasure
    (W.fullAdelicNonisotropicLastShellPositiveLinearMap a ha)
  letI : (Measure.map e μ).Regular := Measure.Regular.map e
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  change (∫ x, φ x ∂Measure.map e.toMeasurableEquiv μ) = ∫ x, φ x ∂μ
  rw [integral_map_equiv e.toMeasurableEquiv]
  change (∫ x,
      W.fullAdelicNonisotropicLastShellQuotientLeftTranslate a ha g φ x ∂μ) =
    ∫ x, φ x ∂μ
  rw [W.integral_fullAdelicNonisotropicLastShellQuotientMeasure,
    W.integral_fullAdelicNonisotropicLastShellQuotientMeasure,
    W.fullAdelicNonisotropicLastShellQuotientIntegral_leftTranslate]

end RationalQuadraticSpaceMatrix
