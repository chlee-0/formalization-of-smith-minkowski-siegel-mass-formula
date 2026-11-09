import SMSFormula.PadicMatrixZeroFactorization

/-!
# Integral--diagonal--integral factorization over the p-adics

Every finite square matrix over `Q_p` that is a matrix unit admits an exact
factorization with integral general-linear outer factors and a signed
prime-power diagonal middle factor.

This is only the finite-dimensional linear decomposition. No coordinate
measure transport or orthogonal-group construction is performed.
-/

noncomputable section

open Matrix

namespace Matrix.PadicIntegralDiagonalIntegralFactorization

variable (p : ℕ) [Fact p.Prime]

/-- Every finite p-adic matrix unit admits integral--diagonal--integral
factorization data. -/
theorem nonempty_of_isUnit {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ_[p]) (hA : IsUnit A) :
    Nonempty (PadicIntegralDiagonalIntegralFactorization p A) := by
  induction d with
  | zero =>
      exact ⟨finZero p A⟩
  | succ d ih =>
      let P : PadicPivot p A :=
        Matrix.padicPivot p A (IsUnit.ne_zero hA)
      obtain ⟨F⟩ :=
        ih P.firstRowEliminatedLowerRightBlock
          (P.firstRowEliminatedLowerRightBlock_isUnit hA)
      exact ⟨P.conditionalSuccessorFactorization F⟩

end Matrix.PadicIntegralDiagonalIntegralFactorization
