import SMSFormula.PadicMatrixSuccessorDiagonal

/-!
# Conditional successor p-adic factorization

Integral--diagonal--integral factorization data records the two integral
general-linear factors, the signed diagonal exponents, and their exact product.
A supplied package for the extracted lower block yields the corresponding
package for the original successor-dimensional matrix.

No lower-block factorization existence or dimension induction is constructed.
-/

noncomputable section

open Matrix

namespace Matrix

variable (p : ℕ) [Fact p.Prime]

/-- Data for an integral--signed-diagonal--integral factorization of a finite
matrix over `Q_p`. -/
structure PadicIntegralDiagonalIntegralFactorization
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ_[p]) where
  left : GL (Fin d) ℤ_[p]
  exponents : Fin d → ℤ
  right : GL (Fin d) ℤ_[p]
  matrix_eq :
    A =
      (GeneralLinearGroup.map PadicInt.Coe.ringHom left :
          Matrix (Fin d) (Fin d) ℚ_[p]) *
        padicSignedPrimePowerDiagonalMatrix p exponents *
      (GeneralLinearGroup.map PadicInt.Coe.ringHom right :
          Matrix (Fin d) (Fin d) ℚ_[p])

namespace PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- A supplied factorization package for the extracted lower block yields one
for the original successor-dimensional matrix. -/
def conditionalSuccessorFactorization
    (P : PadicPivot p A)
    (F : PadicIntegralDiagonalIntegralFactorization p
      P.firstRowEliminatedLowerRightBlock) :
    PadicIntegralDiagonalIntegralFactorization p A where
  left := P.conditionalOriginalLeftFactor F.left
  exponents := P.successorSignedDiagonalExponents F.exponents
  right := P.conditionalOriginalRightFactor F.right
  matrix_eq := by
    rw [← P.firstRowEliminatedOriginalIndexDiagonalBlock_eq F.exponents]
    exact
      P.matrix_eq_integralDiagonalIntegral_of_lower
        F.left F.right F.exponents F.matrix_eq

end PadicPivot

end Matrix
