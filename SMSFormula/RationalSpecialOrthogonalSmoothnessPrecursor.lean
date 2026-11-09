import SMSFormula.RationalSpecialOrthogonalAffineScheme
import SMSFormula.SpecialOrthogonalLinearization
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Matrix-linear precursor to smoothness of the rational special orthogonal scheme

For a symmetric matrix `F`, the differential at the identity of the
orthogonal relation `M ↦ Mᵀ F M` is

```text
X ↦ Xᵀ F + F X.
```

When `F` is nonsingular and two is invertible, this map is split-surjective
onto the symmetric matrices: a symmetric matrix `S` is hit by
`(1 / 2) F⁻¹ S`.  The result is proved over a commutative ring and then
specialized to the mapped rational form matrix over every commutative
rational algebra.

This is the matrix-linear core of the Jacobian smoothness argument.  It does
not assert that the quotient coordinate ring is smooth or reduced, and it does
not connect this split surjection to the redundant polynomial presentation.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The differential at the identity of `M ↦ Mᵀ F M`. -/
def orthogonalRelationDifferential (F : Matrix ι ι R) :
    Matrix ι ι R →ₗ[R] Matrix ι ι R where
  toFun X := Xᵀ * F + F * X
  map_add' X Y := by
    simp only [Matrix.transpose_add, add_mul, mul_add]
    abel
  map_smul' r X := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      RingHom.id_apply]

/-- The differential of the orthogonal relation, with its naturally symmetric
codomain made explicit. -/
def orthogonalRelationDifferentialToSymmetric
    (F : Matrix ι ι R) (hF : F.IsSymm) :
    Matrix ι ι R →ₗ[R] symmetricMatricesSubmodule (R := R) (ι := ι) :=
  (orthogonalRelationDifferential F).codRestrict
    (symmetricMatricesSubmodule (R := R) (ι := ι)) (by
      intro X
      change (Xᵀ * F + F * X).IsSymm
      exact skewAdjointOperator_isSymm F hF X)

/-- The explicit half-inverse candidate for the orthogonal differential. -/
def orthogonalRelationDifferentialRightInverse
    [Invertible (2 : R)] (F S : Matrix ι ι R) : Matrix ι ι R :=
  (⅟ (2 : R)) • (F⁻¹ * S)

/-- The half-inverse formula as a linear map on symmetric matrices. -/
def orthogonalRelationDifferentialRightInverseLinear
    [Invertible (2 : R)] (F : Matrix ι ι R) :
    symmetricMatricesSubmodule (R := R) (ι := ι) →ₗ[R] Matrix ι ι R where
  toFun S := orthogonalRelationDifferentialRightInverse F S.1
  map_add' S T := by
    simp [orthogonalRelationDifferentialRightInverse, mul_add]
  map_smul' r S := by
    simp [orthogonalRelationDifferentialRightInverse,
      RingHom.id_apply, smul_smul]
    rw [mul_comm]

/-- The orthogonal-relation differential sends the explicit half-inverse of
a symmetric matrix back to that matrix. -/
theorem orthogonalRelationDifferential_rightInverse
    [Invertible (2 : R)]
    (F S : Matrix ι ι R) (hF : F.IsSymm) (hFdet : IsUnit F.det)
    (hS : S.IsSymm) :
    orthogonalRelationDifferential F
        (orthogonalRelationDifferentialRightInverse F S) = S := by
  let c : R := ⅟ (2 : R)
  have hc : c + c = 1 := by
    calc
      c + c = (2 : R) * c := by ring
      _ = 1 := by simp [c]
  have hFinvSymm : (F⁻¹).IsSymm := by
    change F⁻¹ᵀ = F⁻¹
    rw [Matrix.transpose_nonsing_inv, hF.eq]
  change (c • (F⁻¹ * S))ᵀ * F + F * (c • (F⁻¹ * S)) = S
  rw [Matrix.transpose_smul, Matrix.transpose_mul, hS.eq, hFinvSymm.eq]
  calc
    (c • (S * F⁻¹)) * F + F * (c • (F⁻¹ * S)) =
        c • (S * (F⁻¹ * F)) + c • ((F * F⁻¹) * S) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    _ = c • S + c • S := by
      rw [Matrix.nonsing_inv_mul F hFdet,
        Matrix.mul_nonsing_inv F hFdet, Matrix.mul_one, Matrix.one_mul]
    _ = (c + c) • S := by rw [add_smul]
    _ = S := by rw [hc, one_smul]

/-- The orthogonal-relation differential is surjective onto symmetric
matrices. -/
theorem exists_orthogonalRelationDifferential_eq_of_isSymm
    [Invertible (2 : R)]
    (F : Matrix ι ι R) (hF : F.IsSymm) (hFdet : IsUnit F.det)
    (S : Matrix ι ι R) (hS : S.IsSymm) :
    ∃ X : Matrix ι ι R, orthogonalRelationDifferential F X = S :=
  ⟨orthogonalRelationDifferentialRightInverse F S,
    orthogonalRelationDifferential_rightInverse F S hF hFdet hS⟩

/-- The half-inverse is a literal linear right inverse after restricting the
codomain to symmetric matrices. -/
theorem orthogonalRelationDifferential_split_surjective
    [Invertible (2 : R)]
    (F : Matrix ι ι R) (hF : F.IsSymm) (hFdet : IsUnit F.det) :
    (orthogonalRelationDifferentialToSymmetric F hF).comp
        (orthogonalRelationDifferentialRightInverseLinear F) = LinearMap.id := by
  apply LinearMap.ext
  intro S
  apply Subtype.ext
  exact orthogonalRelationDifferential_rightInverse F S.1 hF hFdet S.2

end Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The mapped rational form matrix has unit determinant over every
commutative rational algebra. -/
theorem specialOrthogonalMappedFormMatrix_det_isUnit
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    IsUnit (V.specialOrthogonalMappedFormMatrix A).det := by
  have hdet : (V.specialOrthogonalMappedFormMatrix A).det =
      algebraMap ℚ A V.pairingMatrix.det := by
    simpa [specialOrthogonalMappedFormMatrix, RingHom.mapMatrix_apply] using
      (RingHom.map_det (algebraMap ℚ A) V.pairingMatrix).symm
  rw [hdet]
  exact (isUnit_iff_ne_zero.mpr V.form_det_ne_zero).map (algebraMap ℚ A)

/-- Over every commutative rational algebra, the linearized orthogonal
relation at the identity is split-surjective onto symmetric matrices. -/
theorem exists_specialOrthogonalRelationDifferential_eq_of_isSymm
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (S : Matrix (Fin n) (Fin n) A) (hS : S.IsSymm) :
    ∃ X : Matrix (Fin n) (Fin n) A,
      Matrix.orthogonalRelationDifferential
        (V.specialOrthogonalMappedFormMatrix A) X = S := by
  letI : Invertible (2 : A) :=
    Invertible.copy
      (Invertible.map (algebraMap ℚ A) (2 : ℚ)) (2 : A)
        (map_ofNat (algebraMap ℚ A) 2).symm
  exact Matrix.exists_orthogonalRelationDifferential_eq_of_isSymm
    (V.specialOrthogonalMappedFormMatrix A)
    (V.form_symm.map (algebraMap ℚ A))
    (V.specialOrthogonalMappedFormMatrix_det_isUnit A) S hS

end RationalQuadraticSpaceMatrix
