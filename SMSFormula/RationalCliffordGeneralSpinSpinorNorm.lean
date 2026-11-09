import SMSFormula.RationalCliffordGeneralSpinFieldSurjectivity

/-!
# Similitude and spinor norm for intrinsic general Spin

For every field-valued intrinsic general-Spin point, the square class of its
literal reverse-norm similitude is the spinor norm of its represented
special-orthogonal action.  The proof compares the point with the canonical
unnormalized reflection-pair lift of the same action.  Their quotient lies in
the already identified scalar kernel, so their similitudes differ by a
square.
-/

noncomputable section

open QuadraticMap.ReflectionWord

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]

local notation "QK" => V.commutativeScalarExtensionQuadraticForm K

namespace CliffordGeneralSpinIntrinsicPoint

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- An intrinsic general-Spin point differs from the chosen unnormalized
reflection-pair lift of its orthogonal action by a central scalar. -/
theorem exists_scalar_mul_reflectionPairs_eq
    (x : V.CliffordGeneralSpinIntrinsicPoint K) :
    ∃ ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK),
      ∃ hps : eval QK (flattenPairs QK ps) =
          V.specialOrthogonalMatrixGroupIsometryEquiv K x.matrixGroup,
        ∃ z : Kˣ,
          x = ofScalar V K z *
            ofReflectionPairs V K x.matrixGroup ps hps := by
  let gd : DetOneIsometryGroup QK :=
    V.specialOrthogonalMatrixGroupDetOneIsometryHom K x.matrixGroup
  let ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK) :=
    chosenDetOneReflectionPairs QK
      (V.commutativeScalarExtensionQuadraticForm_associated_nondegenerate K)
      gd
  have hps : eval QK (flattenPairs QK ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv K x.matrixGroup := by
    exact eval_chosenDetOneReflectionPairs QK
      (V.commutativeScalarExtensionQuadraticForm_associated_nondegenerate K)
      gd
  let y := ofReflectionPairs V K x.matrixGroup ps hps
  have hy : y.matrixGroup = x.matrixGroup :=
    ofReflectionPairs_matrixGroup V K x.matrixGroup ps hps
  have hkernel : (x * y⁻¹).matrixGroup = 1 := by
    rw [mul_matrixGroup, inv_matrixGroup, hy, mul_inv_cancel]
  obtain ⟨z, hz⟩ :=
    exists_scalar_eq_of_matrixGroup_eq_one V K (x * y⁻¹) hkernel
  refine ⟨ps, hps, z, ?_⟩
  calc
    x = (x * y⁻¹) * y := by simp
    _ = ofScalar V K z * y := by rw [← hz]

/-- The general-Spin similitude and the special-orthogonal spinor norm agree
after passing to square classes. -/
theorem specialOrthogonalSpinorNorm_matrixGroup_eq_similitudeSquareClass
    (x : V.CliffordGeneralSpinIntrinsicPoint K) :
    V.specialOrthogonalSpinorNormHom K x.matrixGroup =
      ((x.similitude : Kˣ) : Rat.SquareClass K) := by
  obtain ⟨ps, hps, z, hx⟩ :=
    exists_scalar_mul_reflectionPairs_eq V K x
  have hnu : x.similitude = z ^ 2 *
      reflectionPairsQuadraticUnit QK ps := by
    have h := congrArg
      (fun y : V.CliffordGeneralSpinIntrinsicPoint K => y.similitude) hx
    simpa [mul_similitude] using h
  have hzsq : (((z ^ 2 : Kˣ)) : Rat.SquareClass K) = 1 := by
    apply (QuotientGroup.eq_one_iff (z ^ 2)).mpr
    exact ⟨z, pow_two z⟩
  rw [V.specialOrthogonalSpinorNormHom_eq_reflectionPairSquareClassProduct
    K x.matrixGroup ps hps]
  rw [← reflectionPairsQuadraticUnit_squareClass]
  rw [hnu]
  simp [hzsq]

/-- The square class of the intrinsic general-Spin similitude as a group
homomorphism. -/
def similitudeSquareClassGroupHom :
    V.CliffordGeneralSpinIntrinsicPoint K →* Rat.SquareClass K :=
  (QuotientGroup.mk' (Subgroup.square Kˣ)).comp
    (similitudeGroupHom V K)

omit [CharZero K] in
@[simp]
theorem similitudeSquareClassGroupHom_apply
    (x : V.CliffordGeneralSpinIntrinsicPoint K) :
    similitudeSquareClassGroupHom V K x =
      ((x.similitude : Kˣ) : Rat.SquareClass K) :=
  rfl

/-- The right-hand square of the carrier-specific crossed diagram commutes:
the similitude modulo squares is the spinor norm of the orthogonal action. -/
theorem similitudeSquareClassGroupHom_eq_spinorNorm_comp_toSO :
    similitudeSquareClassGroupHom V K =
      (V.specialOrthogonalSpinorNormHom K).comp
        (toSpecialOrthogonalGroupHom V K) := by
  ext x
  exact
    (specialOrthogonalSpinorNorm_matrixGroup_eq_similitudeSquareClass
      V K x).symm

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
