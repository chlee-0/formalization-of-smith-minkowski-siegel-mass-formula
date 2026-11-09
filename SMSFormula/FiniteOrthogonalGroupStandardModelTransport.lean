import SMSFormula.FiniteOrthogonalGroupTailToHeadPermutation

/-!
# Transporting arbitrary finite-field forms to the weighted standard model

The arbitrary-rank tail-weighted classification is composed with the explicit
tail-to-head permutation.  The resulting literal congruence is then used to
transport finite orthogonal groups before taking any cardinality.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Every nonsingular symmetric positive-dimensional form over an odd finite
field is explicitly congruent to the existing head-weighted identity model,
with the determinant square class retained. -/
theorem exists_congr_finSuccIdentityGramMatrix_with_det_square
    {K : Type*} [Field K] [Fintype K]
    (n : ℕ) (hchar : ringChar K ≠ 2)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0) :
    ∃ (d s : K) (R : Matrix.GeneralLinearGroup (Fin (n + 1)) K),
      d ≠ 0 ∧ s ≠ 0 ∧
        Matrix.transpose
            (R : Matrix (Fin (n + 1)) (Fin (n + 1)) K) * A *
              (R : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
          finSuccIdentityGramMatrix (n := n) d ∧
        d = s ^ 2 * A.det := by
  obtain ⟨d, s, P, hd, hs, hP, hd_square⟩ :=
    exists_congr_tailWeightedIdentityGramMatrix_with_det_square
      n hchar A hA_symm hA_det
  let Q : Matrix.GeneralLinearGroup (Fin (n + 1)) K :=
    equivPermutationGeneralLinear (tailToHeadEquiv n)
  let X : Matrix (Fin (n + 1)) (Fin (n + 1)) K := P
  let Y : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Q
  have hR :
      Matrix.transpose (X * Y) * A * (X * Y) =
        finSuccIdentityGramMatrix (n := n) d := by
    rw [Matrix.transpose_mul]
    calc
      (Matrix.transpose Y * Matrix.transpose X) * A * (X * Y) =
          Matrix.transpose Y * (Matrix.transpose X * A * X) * Y := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.transpose Y * tailWeightedIdentityGramMatrix n d * Y := by
            rw [hP]
      _ = finSuccIdentityGramMatrix (n := n) d := by
            exact
              tailWeightedIdentityGramMatrix_congr_finSuccIdentityGramMatrix
                n d
  refine ⟨d, s, P * Q, hd, hs, ?_, hd_square⟩
  exact hR

/-- The explicit equivalence of finite orthogonal groups induced by a
congruence to the head-weighted standard model. -/
noncomputable def finiteGramOrthogonalGroupEquivFinSuccIdentityGramMatrix
    {K : Type*} [Field K]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (d : K)
    (R : Matrix.GeneralLinearGroup (Fin (n + 1)) K)
    (hR : Matrix.transpose
          (R : Matrix (Fin (n + 1)) (Fin (n + 1)) K) * A *
          (R : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        finSuccIdentityGramMatrix (n := n) d) :
    finiteGramOrthogonalGroup A ≃
      finiteGramOrthogonalGroup (finSuccIdentityGramMatrix (n := n) d) :=
  finiteGramOrthogonalGroupCongrEquiv
    A (finSuccIdentityGramMatrix (n := n) d) R hR

/-- Through the orthogonal-group equivalence, every
nonsingular symmetric form has the same cardinality as a weighted standard
model whose coefficient retains the determinant square class. -/
theorem exists_natCard_finiteGramOrthogonalGroup_eq_finSuccIdentity_with_det_square
    {K : Type*} [Field K] [Fintype K]
    (n : ℕ) (hchar : ringChar K ≠ 2)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0) :
    ∃ (d s : K) (R : Matrix.GeneralLinearGroup (Fin (n + 1)) K),
      d ≠ 0 ∧ s ≠ 0 ∧ d = s ^ 2 * A.det ∧
        Matrix.transpose
            (R : Matrix (Fin (n + 1)) (Fin (n + 1)) K) * A *
              (R : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
          finSuccIdentityGramMatrix (n := n) d ∧
        Nat.card (finiteGramOrthogonalGroup A) =
          Nat.card (finiteGramOrthogonalGroup
            (finSuccIdentityGramMatrix (n := n) d)) := by
  obtain ⟨d, s, R, hd, hs, hR, hd_square⟩ :=
    exists_congr_finSuccIdentityGramMatrix_with_det_square
      n hchar A hA_symm hA_det
  refine ⟨d, s, R, hd, hs, hd_square, hR, ?_⟩
  exact Nat.card_congr
    (finiteGramOrthogonalGroupEquivFinSuccIdentityGramMatrix A d R hR)

end PositiveDefiniteIntegralLattice
