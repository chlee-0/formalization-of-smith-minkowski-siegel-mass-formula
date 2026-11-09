import SMSFormula.RationalAdeleAdelicOrthogonalTransposeHaar

/-!
# The adelic transpose pairing identity

Adelic orthogonal Haar invariance is proved by a one-eigenfunction overlap argument.  Its
only algebraic input is that the standard coordinate pairing moves a matrix to its transpose:
`<N x, y> = <x, N^T y>`.  The repository had this only as a `private` special case inside the
rational-matrix Fourier covariance; this file records it publicly for an arbitrary full-adelic
matrix, which is the form the overlap computation needs.

Negative scope: an algebraic identity only.  No Fourier transform, no overlap integral, no Haar
scalar and no invariance statement is proved here.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The pairing identity: the standard coordinate pairing carries a full-adelic matrix to its
transpose. -/
theorem dotProduct_mulVec_transpose (N : Matrix (Fin n) (Fin n) RationalAdele)
    (x y : Fin n → RationalAdele) :
    dotProduct (N.mulVec x) y = dotProduct x (N.transpose.mulVec y) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- The same identity in the form used by the overlap argument: pairing against `N x` is pairing
against `x` after transposing. -/
theorem dotProduct_mulVec_transpose' (N : Matrix (Fin n) (Fin n) RationalAdele)
    (x y : Fin n → RationalAdele) :
    dotProduct (N.mulVec x) y = dotProduct (N.transpose.mulVec y) x := by
  rw [dotProduct_mulVec_transpose, dotProduct_comm]

end PositiveDefiniteIntegralLattice

end
