import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellBorel
import SMSFormula.RationalCliffordGeneralSpinHorizontalAdelicUnimodular

/-!
# Modular compatibility for the full-adelic block shell

The existing horizontal full-adelic `GSpin` Haar on the block group and the
already normalized Haar on its literal complement stabilizer are both right
invariant.  Consequently both modular characters are trivial, so the standard
modular compatibility condition for an invariant measure on the non-normal
homogeneous space holds along the literal stabilizer inclusion.

No shell measure or quotient disintegration is constructed here.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance fullAdelicShellModularInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellModularFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellModularT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellModularSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellModularSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellModularSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellModularStabilizerSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

/-- The already normalized full-adelic complement-stabilizer Haar is invariant
under inversion. -/
noncomputable instance
    fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isInvInvariant
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure.IsInvInvariant
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) := by
  let E :=
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
      a ha
  rw [W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_eq_map_horizontal
    a ha]
  exact Measure.isInvInvariant_map_of_commutes
    W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure E
    E.continuous.measurable (fun x ↦ E.map_inv x)

/-- The already normalized full-adelic complement-stabilizer Haar is right
invariant at the same coefficient-one scale as its lower-rank source. -/
theorem
    fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isMulRightInvariant
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure.IsMulRightInvariant
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) := by
  letI : Measure.IsMulLeftInvariant
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) :=
    (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isHaarMeasure
      a ha).toIsMulLeftInvariant
  exact Measure.isMulRightInvariant_of_isInvInvariant
    (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
      a ha)

/-- The modular character of the literal complement stabilizer is trivial. -/
theorem fullAdelicNonisotropicLastComplementGeneralSpinStabilizer_modularCharacterFun_eq_one
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    ∀ h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha,
      Measure.modularCharacterFun h = 1 := by
  letI : Measure.IsHaarMeasure
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) :=
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isHaarMeasure
      a ha
  exact
    (Measure.modularCharacterFun_eq_one_iff_isMulRightInvariant
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha)).2
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isMulRightInvariant
        a ha)

/-- The modular character of the ambient full-adelic block `GSpin` group is
trivial. -/
theorem fullAdelicNonisotropicLastExtensionGeneralSpin_modularCharacterFun_eq_one
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    ∀ g : (W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup,
      Measure.modularCharacterFun g = 1 := by
  let V := W.nonisotropicLastExtension a ha
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  exact
    (Measure.modularCharacterFun_eq_one_iff_isMulRightInvariant
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure).2
      (V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isMulRightInvariant)

/-- The exact modular-character compatibility required for an invariant Weil
measure on the non-normal shell quotient. -/
theorem fullAdelicNonisotropicLastShell_modularCharacter_compatible
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
    Measure.modularCharacterFun
        (h.1 : (W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup) =
      Measure.modularCharacterFun h := by
  rw [W.fullAdelicNonisotropicLastExtensionGeneralSpin_modularCharacterFun_eq_one
      a ha h.1,
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizer_modularCharacterFun_eq_one
      a ha h]

end RationalQuadraticSpaceMatrix
