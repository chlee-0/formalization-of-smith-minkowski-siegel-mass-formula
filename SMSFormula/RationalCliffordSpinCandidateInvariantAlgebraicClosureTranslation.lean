import SMSFormula.RationalCliffordSpinCandidateInvariantAlgebraicClosurePatch
import SMSFormula.RationalCliffordSpinCandidateInvariantGroupScheme

/-!
# Algebraic-closure points and translations for the Spin invariant quotient

The completed principal-open patch supplies compatible algebra homomorphisms
from the right-tensor coordinate rings to `AlgebraicClosure ℚ`.  This file
turns them into the algebraic-closure-valued points of the already represented
`SO` and invariant-quotient group schemes.

It then packages left translation on both point groups and proves that the
invariant comparison intertwines translation by every compatible pair.  This
is point-level translation compatibility.  It does not translate the
ambient principal-open subschemes or prove that their translates cover.
-/

noncomputable section

open TensorProduct
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidalCategory

namespace RationalTamagawa

private abbrev Qbar := AlgebraicClosure ℚ

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Restrict a point of the right-tensor scalar extension to the original
rational coordinate algebra. -/
def algebraicClosureRightTensorPointCoordinateAlgHom
    {D : Type} [CommRing D] [Algebra ℚ D]
    (φ : D ⊗[ℚ] Qbar →ₐ[Qbar] Qbar) : D →ₐ[ℚ] Qbar :=
  (φ.restrictScalars ℚ).comp
    (Algebra.TensorProduct.includeLeft : D →ₐ[ℚ] D ⊗[ℚ] Qbar)

end RationalTamagawa

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev A := V.specialOrthogonalCoordinateRing
private abbrev C := V.negOneInvariantSubalgebra
private abbrev Qbar := AlgebraicClosure ℚ

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem algebraicClosureRightTensorPointCoordinateAlgHom_comp_invariantComparison
    (φA : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (φC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (hφ : φC.comp
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φA) :
    (algebraicClosureRightTensorPointCoordinateAlgHom φC).comp
        V.specialOrthogonalToNegOneInvariantRatAlgHom =
      algebraicClosureRightTensorPointCoordinateAlgHom φA := by
  ext a
  have h := DFunLike.congr_fun hφ
    (Algebra.TensorProduct.includeLeft
      (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) a)
  simpa [algebraicClosureRightTensorPointCoordinateAlgHom,
    V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom_tmul] using h

end RationalQuadraticSpaceMatrix
