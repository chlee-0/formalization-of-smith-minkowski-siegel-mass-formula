import SMSFormula.SpecialOrthogonalRealIdentityElementaryBasis
import SMSFormula.StrictUpperPairProduct

/-!
# The identity tangent split on elementary bases

Strict upper pairs in rank `n + 1` split into pairs wholly below the final
index and pairs ending at the final index. Under the explicit identity tangent
decomposition, the corresponding elementary skew matrices become,
respectively, a lower-rank elementary tangent vector and a standard
last-column coordinate vector.

After reindexing by `Matrix.StrictUpperPair.succEquiv`, the transported
higher-rank elementary basis is exactly the product of the lower-rank
elementary basis and the standard coordinate basis. Its comparison determinant
is therefore one.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- The identity-form real skew-adjoint and skew-symmetric matrix spaces are
linearly equivalent by the identity on ambient matrices. -/
def identitySkewAdjointSkewSymmetricLinearEquivReal (n : ℕ) :
    identitySpecialOrthogonalTangent n ≃ₗ[ℝ]
      skewSymmetricMatricesSubmodule (R := ℝ) (ι := Fin n) where
  toFun X := ⟨X.1,
    (LieAlgebra.Orthogonal.mem_so (Fin n) ℝ X.1).mp X.2⟩
  invFun X := ⟨X.1,
    (LieAlgebra.Orthogonal.mem_so (Fin n) ℝ X.1).mpr X.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The elementary real identity tangent basis, with no finite reindexing. -/
def identitySpecialOrthogonalElementaryRealBasis (n : ℕ) :
    Module.Basis (Matrix.StrictUpperPair n) ℝ
      (identitySpecialOrthogonalTangent n) :=
  (Matrix.skewSymmetricBasis (K := ℝ) (by norm_num)).map
    (identitySkewAdjointSkewSymmetricLinearEquivReal n).symm

/-- Each real elementary tangent basis vector is `E i j - E j i`. -/
@[simp] theorem coe_identitySpecialOrthogonalElementaryRealBasis_apply
    (n : ℕ) (q : Matrix.StrictUpperPair n) :
    ((identitySpecialOrthogonalElementaryRealBasis n q :
        identitySpecialOrthogonalTangent n) :
      Matrix (Fin n) (Fin n) ℝ) =
      Matrix.single q.1.1 q.1.2 1 -
        Matrix.single q.1.2 q.1.1 1 := by
  simp [identitySpecialOrthogonalElementaryRealBasis,
    identitySkewAdjointSkewSymmetricLinearEquivReal]

/-- A pair below the final index becomes its lower-rank elementary tangent
vector and a zero last-column coordinate. -/
theorem identitySpecialOrthogonalTangentContinuousLinearEquiv_elementary_inl
    (n : ℕ) (q : Matrix.StrictUpperPair n) :
    identitySpecialOrthogonalTangentContinuousLinearEquiv n
        (identitySpecialOrthogonalElementaryRealBasis (n + 1)
          ((Matrix.StrictUpperPair.succEquiv n).symm (Sum.inl q))) =
      (identitySpecialOrthogonalElementaryRealBasis n q, 0) := by
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    change
      ((identitySpecialOrthogonalElementaryRealBasis (n + 1)
        ((Matrix.StrictUpperPair.succEquiv n).symm (Sum.inl q)) :
          identitySpecialOrthogonalTangent (n + 1)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          i.castSucc j.castSucc =
        ((identitySpecialOrthogonalElementaryRealBasis n q :
          identitySpecialOrthogonalTangent n) :
          Matrix (Fin n) (Fin n) ℝ) i j
    rw [coe_identitySpecialOrthogonalElementaryRealBasis_apply,
      coe_identitySpecialOrthogonalElementaryRealBasis_apply]
    simp [Matrix.StrictUpperPair.succEquiv, Matrix.single_apply]
  · funext i
    change
      ((identitySpecialOrthogonalElementaryRealBasis (n + 1)
        ((Matrix.StrictUpperPair.succEquiv n).symm (Sum.inl q)) :
          identitySpecialOrthogonalTangent (n + 1)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          i.castSucc (Fin.last n) = 0
    rw [coe_identitySpecialOrthogonalElementaryRealBasis_apply]
    simp [Matrix.StrictUpperPair.succEquiv]

/-- A pair ending at the final index becomes a zero lower-rank tangent and
the corresponding standard last-column coordinate vector. -/
theorem identitySpecialOrthogonalTangentContinuousLinearEquiv_elementary_inr
    (n : ℕ) (i : Fin n) :
    identitySpecialOrthogonalTangentContinuousLinearEquiv n
        (identitySpecialOrthogonalElementaryRealBasis (n + 1)
          ((Matrix.StrictUpperPair.succEquiv n).symm (Sum.inr i))) =
      (0, Pi.basisFun ℝ (Fin n) i) := by
  apply Prod.ext
  · apply Subtype.ext
    ext j k
    change
      ((identitySpecialOrthogonalElementaryRealBasis (n + 1)
        ((Matrix.StrictUpperPair.succEquiv n).symm (Sum.inr i)) :
          identitySpecialOrthogonalTangent (n + 1)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          j.castSucc k.castSucc = 0
    rw [coe_identitySpecialOrthogonalElementaryRealBasis_apply]
    have hlastJ : Fin.last n ≠ j.castSucc :=
      (Fin.castSucc_ne_last j).symm
    have hlastK : Fin.last n ≠ k.castSucc :=
      (Fin.castSucc_ne_last k).symm
    simp [Matrix.StrictUpperPair.succEquiv, hlastJ, hlastK]
  · funext j
    change
      ((identitySpecialOrthogonalElementaryRealBasis (n + 1)
        ((Matrix.StrictUpperPair.succEquiv n).symm (Sum.inr i)) :
          identitySpecialOrthogonalTangent (n + 1)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          j.castSucc (Fin.last n) =
        Pi.basisFun ℝ (Fin n) i j
    rw [coe_identitySpecialOrthogonalElementaryRealBasis_apply]
    simp [Matrix.StrictUpperPair.succEquiv, Matrix.single_apply,
      Pi.basisFun_apply, Pi.single_apply]
    by_cases h : i = j
    · subst j
      simp
    · have h' : j ≠ i := Ne.symm h
      simp [h, h']

/-- The product of the lower-rank elementary tangent basis and the standard
last-column coordinate basis. -/
def identitySpecialOrthogonalElementaryTangentProductBasis (n : ℕ) :
    Module.Basis (Matrix.StrictUpperPair n ⊕ Fin n) ℝ
      (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
  (identitySpecialOrthogonalElementaryRealBasis n).prod
    (Pi.basisFun ℝ (Fin n))

/-- The higher-rank elementary basis transported through the tangent split
and reindexed by the strict-pair decomposition. -/
def identitySpecialOrthogonalElementaryTangentSplitTransportedBasis (n : ℕ) :
    Module.Basis (Matrix.StrictUpperPair n ⊕ Fin n) ℝ
      (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
  ((identitySpecialOrthogonalElementaryRealBasis (n + 1)).map
      (identitySpecialOrthogonalTangentContinuousLinearEquiv n).toLinearEquiv).reindex
    (Matrix.StrictUpperPair.succEquiv n)

theorem
    identitySpecialOrthogonalElementaryTangentSplitTransportedBasis_eq_product
    (n : ℕ) :
    identitySpecialOrthogonalElementaryTangentSplitTransportedBasis n =
      identitySpecialOrthogonalElementaryTangentProductBasis n := by
  apply DFunLike.ext _ _
  intro q
  rcases q with q | i
  · simpa [identitySpecialOrthogonalElementaryTangentSplitTransportedBasis,
      identitySpecialOrthogonalElementaryTangentProductBasis] using
        identitySpecialOrthogonalTangentContinuousLinearEquiv_elementary_inl n q
  · simpa [identitySpecialOrthogonalElementaryTangentSplitTransportedBasis,
      identitySpecialOrthogonalElementaryTangentProductBasis] using
        identitySpecialOrthogonalTangentContinuousLinearEquiv_elementary_inr n i

/-- The elementary-basis comparison determinant for the tangent split. -/
def identitySpecialOrthogonalElementaryTangentSplitDetScalar (n : ℕ) : ℝ :=
  (identitySpecialOrthogonalElementaryTangentProductBasis n).det
    (identitySpecialOrthogonalElementaryTangentSplitTransportedBasis n)

/-- With the explicit strict-pair orientation, the elementary tangent split
has determinant exactly one. -/
theorem identitySpecialOrthogonalElementaryTangentSplitDetScalar_eq_one
    (n : ℕ) :
    identitySpecialOrthogonalElementaryTangentSplitDetScalar n = 1 := by
  rw [identitySpecialOrthogonalElementaryTangentSplitDetScalar,
    identitySpecialOrthogonalElementaryTangentSplitTransportedBasis_eq_product]
  exact
    (identitySpecialOrthogonalElementaryTangentProductBasis n).det_self

end PositiveDefiniteIntegralLattice
