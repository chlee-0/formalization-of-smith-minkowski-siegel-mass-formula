import SMSFormula.RationalCliffordSpinCandidatePointGroup

/-!
# The unit fiber of the affine Clifford--Spin candidate morphism

The categorical kernel is developed first as the ordinary pullback of the
underlying relative scheme morphism along the unit of `SO`.  This avoids
assuming a pullback instance for internal group objects.  Its arbitrary
relative points are identified with candidate points whose extracted
special-orthogonal matrix is the identity.
-/

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidalCategory Matrix

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Postcomposition of candidate coordinates commutes with extraction of the
special-orthogonal matrix. -/
theorem cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_map
    {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B)
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup B (f.comp F) =
      V.specialOrthogonalMatrixGroupMap f
        (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup A F) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix]
  rw [V.specialOrthogonalMatrixGroupMap_apply_matrix]
  rw [V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix]
  rfl

/-- Literal affine coordinate points whose extracted matrix is one. -/
abbrev CliffordSpinCandidateAffineCoordinateKernelPoint
    (A : Type) [CommRing A] [Algebra ℚ A] :=
  { F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A //
    V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup A F = 1 }

end RationalQuadraticSpaceMatrix
