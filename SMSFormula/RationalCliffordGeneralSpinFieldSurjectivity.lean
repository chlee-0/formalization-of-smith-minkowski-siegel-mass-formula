import SMSFormula.RationalCliffordGeneralSpinHorizontalExactness
import SMSFormula.RationalCliffordSpinCandidateSpinorNormKernel

/-!
# Fieldwise surjectivity of intrinsic general Spin onto special orthogonal

For a characteristic-zero rational field, the completed determinant-one
Cartan--Dieudonne factorization supplies a list of reflection pairs for every
special-orthogonal point.  Its unnormalized Clifford product is already an
even unit; its reverse norm is the product of the represented quadratic
values.  Keeping that norm as the general-Spin similitude gives a literal
preimage without adjoining square roots.
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

/-- The unnormalized Clifford unit of a determinant-one reflection-pair word
as an intrinsic general-Spin point. -/
def ofReflectionPairs
    (g : V.specialOrthogonalMatrixGroup K)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK))
    (hps : eval QK (flattenPairs QK ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv K g) :
    V.CliffordGeneralSpinIntrinsicPoint K where
  cliffordUnit := V.reflectionPairsCoordinateCliffordUnit K ps
  similitude := reflectionPairsQuadraticUnit QK ps
  matrixPoint := V.specialOrthogonalMatrixPointOfGroup K g
  involute_eq :=
    V.reflectionPairsCoordinateCliffordUnit_involute K ps
  mul_reverse_eq :=
    V.reflectionPairsCoordinateCliffordUnit_mul_reverse K ps
  vectorGraph := by
    intro i
    exact V.reflectionPairsCoordinateCliffordUnit_vectorGraph K g ps hps i

omit [CharZero K] in
@[simp]
theorem ofReflectionPairs_matrixGroup
    (g : V.specialOrthogonalMatrixGroup K)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK))
    (hps : eval QK (flattenPairs QK ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv K g) :
    (ofReflectionPairs V K g ps hps).matrixGroup = g := by
  exact (V.specialOrthogonalMatrixPointEquivGroup K).apply_symm_apply g

omit [CharZero K] in
@[simp]
theorem ofReflectionPairs_similitude
    (g : V.specialOrthogonalMatrixGroup K)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK))
    (hps : eval QK (flattenPairs QK ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv K g) :
    (ofReflectionPairs V K g ps hps).similitude =
      reflectionPairsQuadraticUnit QK ps :=
  rfl

/-- Every field-valued special-orthogonal point has a literal intrinsic
general-Spin preimage. -/
theorem toSpecialOrthogonalGroupHom_surjective :
    Function.Surjective (toSpecialOrthogonalGroupHom V K) := by
  intro g
  let gd : DetOneIsometryGroup QK :=
    V.specialOrthogonalMatrixGroupDetOneIsometryHom K g
  let ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK) :=
    chosenDetOneReflectionPairs QK
      (V.commutativeScalarExtensionQuadraticForm_associated_nondegenerate K)
      gd
  have hps : eval QK (flattenPairs QK ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv K g := by
    exact eval_chosenDetOneReflectionPairs QK
      (V.commutativeScalarExtensionQuadraticForm_associated_nondegenerate K)
      gd
  refine ⟨ofReflectionPairs V K g ps hps, ?_⟩
  exact ofReflectionPairs_matrixGroup V K g ps hps

/-- The horizontal intrinsic sequence is short exact on every
characteristic-zero rational field: the scalar kernel theorem together with
literal reflection-pair surjectivity. -/
theorem horizontal_exact_and_surjective :
    (scalarGroupHom V K).range =
        (toSpecialOrthogonalGroupHom V K).ker ∧
      Function.Surjective (toSpecialOrthogonalGroupHom V K) :=
  ⟨range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom V K,
    toSpecialOrthogonalGroupHom_surjective V K⟩

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
