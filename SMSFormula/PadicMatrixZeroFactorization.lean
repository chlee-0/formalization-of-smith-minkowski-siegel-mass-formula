import SMSFormula.PadicMatrixConditionalSuccessorFactor

/-!
# Zero-dimensional p-adic factorization

The unique matrix indexed by `Fin 0` has an
integral--signed-diagonal--integral factorization with identity outer factors
and the empty exponent vector.

No dimension induction or positive-dimensional factorization is constructed.
-/

noncomputable section

open Matrix

namespace Matrix.PadicIntegralDiagonalIntegralFactorization

variable (p : ℕ) [Fact p.Prime]

/-- The zero-dimensional integral--diagonal--integral factorization package. -/
def finZero (A : Matrix (Fin 0) (Fin 0) ℚ_[p]) :
    PadicIntegralDiagonalIntegralFactorization p A where
  left := 1
  exponents := fun i => Fin.elim0 i
  right := 1
  matrix_eq := Subsingleton.elim _ _

end Matrix.PadicIntegralDiagonalIntegralFactorization
