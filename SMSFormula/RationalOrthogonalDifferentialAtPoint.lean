import SMSFormula.RationalOrthogonalDeterminantComponent

/-!
# The independent orthogonal differential at an arbitrary point

The identity differential alone is not enough for a Jacobian smoothness
argument.  At a matrix `M`, the differential of `X ↦ Xᵀ F X` is

```text
H ↦ Hᵀ F M + Mᵀ F H.
```

If `Mᵀ F M = F`, multiplication by `M` transports the already constructed
right inverse at the identity to a right inverse at `M`.  This file proves
that statement over an arbitrary commutative ring with `2` invertible.

It also identifies symmetric matrices with functions on the independent
upper-triangular relation indices.  Consequently the rectangular
differential from all `n²` matrix coordinates to the `n(n+1)/2` independent
relations is split-surjective at every orthogonal point.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The differential of `X ↦ Xᵀ F X` at the matrix `M`. -/
def orthogonalRelationDifferentialAt (F M : Matrix ι ι R) :
    Matrix ι ι R →ₗ[R] Matrix ι ι R where
  toFun H := Hᵀ * F * M + Mᵀ * F * H
  map_add' H K := by
    simp only [Matrix.transpose_add, add_mul, mul_add]
    abel
  map_smul' r H := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      RingHom.id_apply]

/-- For symmetric `F`, the differential at every point has symmetric image. -/
def orthogonalRelationDifferentialAtToSymmetric
    (F M : Matrix ι ι R) (hF : F.IsSymm) :
    Matrix ι ι R →ₗ[R] symmetricMatricesSubmodule (R := R) (ι := ι) :=
  (orthogonalRelationDifferentialAt F M).codRestrict
    (symmetricMatricesSubmodule (R := R) (ι := ι)) (by
      intro H
      change (Hᵀ * F * M + Mᵀ * F * H)ᵀ =
        Hᵀ * F * M + Mᵀ * F * H
      simp only [Matrix.transpose_add, Matrix.transpose_mul,
        Matrix.transpose_transpose, hF.eq, Matrix.mul_assoc, add_comm])

/-- Multiplication by an orthogonal point transports the identity right
inverse to a right inverse at that point. -/
def orthogonalRelationDifferentialAtRightInverseLinear
    [Invertible (2 : R)] (F M : Matrix ι ι R) :
    symmetricMatricesSubmodule (R := R) (ι := ι) →ₗ[R] Matrix ι ι R where
  toFun S := M * orthogonalRelationDifferentialRightInverse F S.1
  map_add' S T := by
    simp [orthogonalRelationDifferentialRightInverse, mul_add]
  map_smul' r S := by
    simp [orthogonalRelationDifferentialRightInverse,
      RingHom.id_apply, smul_smul]
    rw [mul_comm]

/-- At an orthogonal point, the pointwise differential sends the transported
identity right inverse back to the original symmetric matrix. -/
theorem orthogonalRelationDifferentialAt_rightInverse
    [Invertible (2 : R)] (F M S : Matrix ι ι R)
    (hF : F.IsSymm) (hFdet : IsUnit F.det)
    (hM : Mᵀ * F * M = F) (hS : S.IsSymm) :
    orthogonalRelationDifferentialAt F M
        (M * orthogonalRelationDifferentialRightInverse F S) = S := by
  let Z := orthogonalRelationDifferentialRightInverse F S
  change (M * Z)ᵀ * F * M + Mᵀ * F * (M * Z) = S
  rw [Matrix.transpose_mul]
  calc
    Zᵀ * Mᵀ * F * M + Mᵀ * F * (M * Z) =
        Zᵀ * F + (Mᵀ * F * M) * Z := by
          rw [Matrix.mul_assoc Zᵀ Mᵀ F, Matrix.mul_assoc Zᵀ,
            hM, ← Matrix.mul_assoc (Mᵀ * F) M Z, hM]
    _ = Zᵀ * F + F * Z := by rw [hM]
    _ = orthogonalRelationDifferential F Z := by
      rfl
    _ = S := orthogonalRelationDifferential_rightInverse F S hF hFdet hS

/-- The differential at every orthogonal point is split-surjective onto the
symmetric matrices. -/
theorem orthogonalRelationDifferentialAt_split_surjective
    [Invertible (2 : R)] (F M : Matrix ι ι R)
    (hF : F.IsSymm) (hFdet : IsUnit F.det)
    (hM : Mᵀ * F * M = F) :
    (orthogonalRelationDifferentialAtToSymmetric F M hF).comp
        (orthogonalRelationDifferentialAtRightInverseLinear F M) =
      LinearMap.id := by
  apply LinearMap.ext
  intro S
  apply Subtype.ext
  exact orthogonalRelationDifferentialAt_rightInverse F M S.1 hF hFdet hM S.2

end Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The canonical upper-triangular index associated with an arbitrary pair. -/
def specialOrthogonalIndependentIndexOfPair (i j : Fin n) :
    SpecialOrthogonalIndependentRelationIndex (n := n) :=
  ⟨(min i j, max i j), min_le_max⟩

/-- Reconstruct a symmetric matrix from its independent upper-triangular
coordinates. -/
def symmetricMatrixOfIndependentCoordinates
    {A : Type*} [CommRing A]
    (c : SpecialOrthogonalIndependentRelationIndex (n := n) → A) :
    Matrix (Fin n) (Fin n) A :=
  fun i j => c (specialOrthogonalIndependentIndexOfPair i j)

/-- The reconstructed matrix is symmetric. -/
theorem symmetricMatrixOfIndependentCoordinates_isSymm
    {A : Type*} [CommRing A]
    (c : SpecialOrthogonalIndependentRelationIndex (n := n) → A) :
    (symmetricMatrixOfIndependentCoordinates c).IsSymm := by
  ext i j
  simp [symmetricMatrixOfIndependentCoordinates,
    specialOrthogonalIndependentIndexOfPair, min_comm, max_comm]

/-- Symmetric matrices are linearly equivalent to their independent
upper-triangular coordinates. -/
def symmetricMatricesIndependentCoordinatesLinearEquiv
    (A : Type*) [CommRing A] :
    Matrix.symmetricMatricesSubmodule (R := A) (ι := Fin n) ≃ₗ[A]
      (SpecialOrthogonalIndependentRelationIndex (n := n) → A) where
  toFun S ij := S.1 ij.1.1 ij.1.2
  invFun c :=
    ⟨symmetricMatrixOfIndependentCoordinates c,
      symmetricMatrixOfIndependentCoordinates_isSymm c⟩
  map_add' S T := rfl
  map_smul' r S := rfl
  left_inv S := by
    apply Subtype.ext
    ext i j
    by_cases hij : i ≤ j
    · simp [symmetricMatrixOfIndependentCoordinates,
        specialOrthogonalIndependentIndexOfPair, min_eq_left hij,
        max_eq_right hij]
    · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
      simp [symmetricMatrixOfIndependentCoordinates,
        specialOrthogonalIndependentIndexOfPair, min_eq_right hji,
        max_eq_left hji]
      exact congrFun (congrFun S.2.eq i) j
  right_inv c := by
    funext ij
    simp [symmetricMatrixOfIndependentCoordinates,
      specialOrthogonalIndependentIndexOfPair, min_eq_left ij.2,
      max_eq_right ij.2]

/-- The differential at `M`, expressed in the independent relation
coordinates. -/
def independentOrthogonalRelationDifferentialAt
    (A : Type*) [CommRing A]
    (F M : Matrix (Fin n) (Fin n) A) (hF : F.IsSymm) :
    Matrix (Fin n) (Fin n) A →ₗ[A]
      (SpecialOrthogonalIndependentRelationIndex (n := n) → A) :=
  (symmetricMatricesIndependentCoordinatesLinearEquiv A).toLinearMap.comp
    (Matrix.orthogonalRelationDifferentialAtToSymmetric F M hF)

/-- The transported pointwise right inverse, with independent relation
coordinates as its domain. -/
def independentOrthogonalRelationDifferentialAtRightInverse
    (A : Type*) [CommRing A] [Invertible (2 : A)]
    (F M : Matrix (Fin n) (Fin n) A) :
    (SpecialOrthogonalIndependentRelationIndex (n := n) → A) →ₗ[A]
      Matrix (Fin n) (Fin n) A :=
  (Matrix.orthogonalRelationDifferentialAtRightInverseLinear F M).comp
    (symmetricMatricesIndependentCoordinatesLinearEquiv A).symm.toLinearMap

/-- The rectangular independent differential is split-surjective at every
orthogonal point. -/
theorem independentOrthogonalRelationDifferentialAt_split_surjective
    (A : Type*) [CommRing A] [Invertible (2 : A)]
    (F M : Matrix (Fin n) (Fin n) A)
    (hF : F.IsSymm) (hFdet : IsUnit F.det)
    (hM : Mᵀ * F * M = F) :
    (independentOrthogonalRelationDifferentialAt A F M hF).comp
        (independentOrthogonalRelationDifferentialAtRightInverse A F M) =
      LinearMap.id := by
  apply LinearMap.ext
  intro c
  change symmetricMatricesIndependentCoordinatesLinearEquiv A
      (Matrix.orthogonalRelationDifferentialAtToSymmetric F M hF
        (Matrix.orthogonalRelationDifferentialAtRightInverseLinear F M
          ((symmetricMatricesIndependentCoordinatesLinearEquiv A).symm c))) = c
  have h := LinearMap.congr_fun
    (Matrix.orthogonalRelationDifferentialAt_split_surjective
      F M hF hFdet hM)
    ((symmetricMatricesIndependentCoordinatesLinearEquiv A).symm c)
  change Matrix.orthogonalRelationDifferentialAtToSymmetric F M hF
      (Matrix.orthogonalRelationDifferentialAtRightInverseLinear F M
        ((symmetricMatricesIndependentCoordinatesLinearEquiv A).symm c)) =
    (symmetricMatricesIndependentCoordinatesLinearEquiv A).symm c at h
  rw [h]
  exact (symmetricMatricesIndependentCoordinatesLinearEquiv A).apply_symm_apply c

variable (V : RationalQuadraticSpaceMatrix n)

/-- At the universal orthogonal matrix, the independent differential has an
explicit linear right inverse over the orthogonal coordinate ring. -/
theorem exists_orthogonalUniversalIndependentRelationDifferential_rightInverse :
    ∃ g :
        (SpecialOrthogonalIndependentRelationIndex (n := n) →
            V.orthogonalCoordinateRing) →ₗ[V.orthogonalCoordinateRing]
          Matrix (Fin n) (Fin n) V.orthogonalCoordinateRing,
      (independentOrthogonalRelationDifferentialAt
          V.orthogonalCoordinateRing V.orthogonalMappedFormMatrix
            V.orthogonalUniversalMatrix
              (V.form_symm.map
                (algebraMap ℚ V.orthogonalCoordinateRing))).comp g =
        LinearMap.id := by
  letI : Invertible (2 : V.orthogonalCoordinateRing) :=
    Invertible.copy
      (Invertible.map (algebraMap ℚ V.orthogonalCoordinateRing) (2 : ℚ))
      (2 : V.orthogonalCoordinateRing)
      (map_ofNat (algebraMap ℚ V.orthogonalCoordinateRing) 2).symm
  refine ⟨independentOrthogonalRelationDifferentialAtRightInverse
    V.orthogonalCoordinateRing V.orthogonalMappedFormMatrix
      V.orthogonalUniversalMatrix, ?_⟩
  exact independentOrthogonalRelationDifferentialAt_split_surjective
    V.orthogonalCoordinateRing V.orthogonalMappedFormMatrix
      V.orthogonalUniversalMatrix
        (V.form_symm.map (algebraMap ℚ V.orthogonalCoordinateRing))
          (V.specialOrthogonalMappedFormMatrix_det_isUnit
            V.orthogonalCoordinateRing)
              V.orthogonalUniversalMatrix_relation

end RationalQuadraticSpaceMatrix
