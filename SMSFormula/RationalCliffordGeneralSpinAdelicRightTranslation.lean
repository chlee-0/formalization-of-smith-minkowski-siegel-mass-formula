import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalBorel
import SMSFormula.RationalCliffordGeneralSpinQuotientLogCutoff

/-!
# Right translation on the rational adelic general-Spin quotient

Right multiplication by a full-adelic intrinsic general-Spin point descends
to the rational left quotient.  It is continuous for the genuine quotient
topology.  The descended idele class and logarithmic module transform by the
literal similitude of the translating point.

This is the carrier action used to translate the neutral Spin quotient fiber
over every rational idele class.  No measure is chosen here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Right multiplication by an adelic general-Spin point on the rational
general-Spin left quotient. -/
def fullAdelicCliffordGeneralSpinLeftQuotientRightMul
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient →
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Quot.lift
    (fun y => V.fullAdelicCliffordGeneralSpinLeftQuotientMap (y * x)) (by
      intro y z hyz
      rcases hyz with ⟨gamma, rfl⟩
      change V.fullAdelicCliffordGeneralSpinLeftQuotientMap (y * x) =
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap
          (((gamma : V.FullAdelicCliffordGeneralSpinGroup) * y) * x)
      rw [mul_assoc]
      exact (leftCosetMap_gamma_mul
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup gamma
        (y * x)).symm)

@[simp]
theorem fullAdelicCliffordGeneralSpinLeftQuotientRightMul_mk
    (x y : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap y) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap (y * x) :=
  rfl

/-- Quotient right multiplication is continuous for the existing quotient
topology. -/
theorem continuous_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    Continuous (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) := by
  apply Continuous.quotient_lift
  exact V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap.continuous.comp
    (continuous_id.mul continuous_const)

theorem measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    Measurable (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) :=
  (V.continuous_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x).measurable

/-- The descended idele class is multiplied by the translating similitude
class under quotient right multiplication. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_rightMul
    (x : V.FullAdelicCliffordGeneralSpinGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x z) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass z *
        QuotientGroup.mk' rationalIdeleDiagonalSubgroup
          (V.fullAdelicCliffordGeneralSpinSimilitudeHom x) := by
  induction z using Quot.inductionOn with
  | _ y =>
    change V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap (y * x)) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
          (V.fullAdelicCliffordGeneralSpinLeftQuotientMap y) * _
    rw [V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_mk,
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_mk,
      map_mul]
    exact map_mul (QuotientGroup.mk' rationalIdeleDiagonalSubgroup) _ _

/-- Quotient right multiplication adds the logarithm of the translating
similitude. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientLogModule_rightMul
    (x : V.FullAdelicCliffordGeneralSpinGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x z) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z +
        rationalIdeleLogModule
          (V.fullAdelicCliffordGeneralSpinSimilitudeHom x) := by
  rw [fullAdelicCliffordGeneralSpinLeftQuotientLogModule,
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_rightMul,
    rationalIdeleClassLogModule_mul]
  rfl

end RationalQuadraticSpaceMatrix
