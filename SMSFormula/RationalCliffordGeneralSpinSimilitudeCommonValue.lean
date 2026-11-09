import SMSFormula.RationalCliffordGeneralSpinSimilitudeImage
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRange

/-!
# Common quadratic values and intrinsic general-Spin similitudes

If two anisotropic vectors have quadratic values differing by a unit `a`,
their ordered reflection pair has spinor norm equal to the square class of
`a`.  The exact fieldwise similitude-image theorem then supplies an intrinsic
general-Spin point whose reverse-norm similitude is `a` itself.

This is the final algebraic step of the rational and p-adic
common-value arguments used by the crossed `GSpin` comparison.
-/

noncomputable section

open QuadraticMap.ReflectionWord

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (K : Type*) [Field K] [CharZero K]

namespace CliffordGeneralSpinIntrinsicPoint

/-- A reflection pair whose second quadratic value is `a` times its first
puts the square class of `a` in the special-orthogonal spinor-norm image. -/
theorem squareClass_mem_spinorNorm_range_of_reflectionPair_value_eq_mul
    (a : Kˣ)
    (v w : (V.commutativeScalarExtensionQuadraticForm K).AnisotropicVector)
    (hvalue : V.commutativeScalarExtensionQuadraticForm K w =
      (a : K) * V.commutativeScalarExtensionQuadraticForm K v) :
    (((a : Kˣ)) : Rat.SquareClass K) ∈
      (V.specialOrthogonalSpinorNormHom K).range := by
  let pair : V.ReflectionPair K := (v, w)
  refine ⟨V.reflectionPairMatrixGroup K pair, ?_⟩
  rw [V.specialOrthogonalSpinorNormHom_reflectionPairMatrixGroup K pair]
  apply QuotientGroup.eq_iff_div_mem.mpr
  rw [Subgroup.mem_square]
  let q : Kˣ := Units.mk0
    (V.commutativeScalarExtensionQuadraticForm K v) v.property
  refine ⟨q, ?_⟩
  apply Units.ext
  dsimp [pair, reflectionPairSquareClass, quadraticValueSquareClass, q]
  simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  change
    V.commutativeScalarExtensionQuadraticForm K v *
          V.commutativeScalarExtensionQuadraticForm K w * (a : K)⁻¹ =
      V.commutativeScalarExtensionQuadraticForm K v *
        V.commutativeScalarExtensionQuadraticForm K v
  rw [hvalue]
  field_simp [a.ne_zero]

/-- A common-value reflection pair realizes the prescribed literal
similitude in intrinsic general Spin. -/
theorem exists_similitude_eq_of_reflectionPair_value_eq_mul
    (a : Kˣ)
    (v w : (V.commutativeScalarExtensionQuadraticForm K).AnisotropicVector)
    (hvalue : V.commutativeScalarExtensionQuadraticForm K w =
      (a : K) * V.commutativeScalarExtensionQuadraticForm K v) :
    ∃ x : V.CliffordGeneralSpinIntrinsicPoint K,
      similitudeGroupHom V K x = a := by
  change a ∈ (similitudeGroupHom V K).range
  rw [range_similitudeGroupHom_eq_squareClass_comap_spinorNorm_range V K]
  exact squareClass_mem_spinorNorm_range_of_reflectionPair_value_eq_mul
    V K a v w hvalue

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
