import SMSFormula.SpecialOrthogonalRealIdentityLastColumn

/-!
# Surjectivity of the identity-model last-column map

In rank at least two, every Euclidean unit vector occurs as the last column of
an identity-form real special orthogonal matrix. An orthonormal basis extending
the requested vector gives an orthogonal matrix. Multiplication by a diagonal
sign matrix in the first coordinate corrects its determinant without changing
the final column.

No stabilizer equivalence or measure disintegration is asserted.
-/

open scoped BigOperators

noncomputable section

open Matrix MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable (n : ℕ)

abbrev identitySpecialOrthogonalEuclideanSpace :=
  EuclideanSpace ℝ (Fin (n + 1))

def identitySpecialOrthogonalBasisMatrix
    (b : OrthonormalBasis (Fin (n + 1)) ℝ
      (identitySpecialOrthogonalEuclideanSpace n)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.toMatrix b

@[simp]
theorem identitySpecialOrthogonalBasisMatrix_apply
    (b : OrthonormalBasis (Fin (n + 1)) ℝ
      (identitySpecialOrthogonalEuclideanSpace n))
    (i j : Fin (n + 1)) :
    identitySpecialOrthogonalBasisMatrix n b i j = b j i := by
  simp [identitySpecialOrthogonalBasisMatrix, Module.Basis.toMatrix_apply]

theorem identitySpecialOrthogonalBasisMatrix_mem_orthogonal
    (b : OrthonormalBasis (Fin (n + 1)) ℝ
      (identitySpecialOrthogonalEuclideanSpace n)) :
    identitySpecialOrthogonalBasisMatrix n b ∈
      Matrix.orthogonalGroup (Fin (n + 1)) ℝ := by
  exact
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toMatrix_orthonormalBasis_mem_orthogonal b

theorem identitySpecialOrthogonalBasisMatrix_det_sq
    (b : OrthonormalBasis (Fin (n + 1)) ℝ
      (identitySpecialOrthogonalEuclideanSpace n)) :
    (identitySpecialOrthogonalBasisMatrix n b).det ^ 2 = 1 := by
  have h :=
    (EuclideanSpace.basisFun
      (Fin (n + 1)) ℝ).det_to_matrix_orthonormalBasis_real b
  rw [Module.Basis.det_apply] at h
  rcases h with h | h
  · simp [identitySpecialOrthogonalBasisMatrix, h]
  · simp [identitySpecialOrthogonalBasisMatrix, h]

def identitySpecialOrthogonalOrientationSign
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) : ℝ :=
  if i = 0 then A.det else 1

def identitySpecialOrthogonalOrientationCorrection
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (identitySpecialOrthogonalOrientationSign n A)

def identitySpecialOrthogonalOrientedBasisMatrix
    (b : OrthonormalBasis (Fin (n + 1)) ℝ
      (identitySpecialOrthogonalEuclideanSpace n)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  identitySpecialOrthogonalBasisMatrix n b *
    identitySpecialOrthogonalOrientationCorrection n
      (identitySpecialOrthogonalBasisMatrix n b)

theorem identitySpecialOrthogonalOrientationCorrection_det
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (identitySpecialOrthogonalOrientationCorrection n A).det = A.det := by
  classical
  simp [identitySpecialOrthogonalOrientationCorrection,
    identitySpecialOrthogonalOrientationSign, Matrix.det_diagonal]

theorem identitySpecialOrthogonalOrientedBasisMatrix_det
    (b : OrthonormalBasis (Fin (n + 1)) ℝ
      (identitySpecialOrthogonalEuclideanSpace n)) :
    (identitySpecialOrthogonalOrientedBasisMatrix n b).det = 1 := by
  rw [identitySpecialOrthogonalOrientedBasisMatrix, Matrix.det_mul,
    identitySpecialOrthogonalOrientationCorrection_det]
  simpa [pow_two] using identitySpecialOrthogonalBasisMatrix_det_sq n b

theorem identitySpecialOrthogonalOrientationCorrection_transpose_mul_self
    (b : OrthonormalBasis (Fin (n + 1)) ℝ
      (identitySpecialOrthogonalEuclideanSpace n)) :
    (identitySpecialOrthogonalOrientationCorrection n
      (identitySpecialOrthogonalBasisMatrix n b))ᵀ *
        identitySpecialOrthogonalOrientationCorrection n
          (identitySpecialOrthogonalBasisMatrix n b) = 1 := by
  classical
  have htranspose :
      (Matrix.diagonal
        (identitySpecialOrthogonalOrientationSign n
          (identitySpecialOrthogonalBasisMatrix n b)))ᵀ =
        Matrix.diagonal
          (identitySpecialOrthogonalOrientationSign n
            (identitySpecialOrthogonalBasisMatrix n b)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rfl
    · simp [Matrix.transpose_apply, hij, Ne.symm hij]
  rw [identitySpecialOrthogonalOrientationCorrection, htranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0
    · subst i
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      simpa [identitySpecialOrthogonalOrientationSign, pow_two] using
        identitySpecialOrthogonalBasisMatrix_det_sq n b
    · simp [identitySpecialOrthogonalOrientationSign, hi]
  · simp [hij]

theorem identitySpecialOrthogonalOrientedBasisMatrix_transpose_mul_self
    (b : OrthonormalBasis (Fin (n + 1)) ℝ
      (identitySpecialOrthogonalEuclideanSpace n)) :
    (identitySpecialOrthogonalOrientedBasisMatrix n b)ᵀ *
        identitySpecialOrthogonalOrientedBasisMatrix n b = 1 := by
  have hA :=
    identitySpecialOrthogonalBasisMatrix_mem_orthogonal n b
  have hA' :
      (identitySpecialOrthogonalBasisMatrix n b)ᵀ *
          identitySpecialOrthogonalBasisMatrix n b = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (R := ℝ) (Fin (n + 1))).mp hA
  simp only [identitySpecialOrthogonalOrientedBasisMatrix, Matrix.transpose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc
      (identitySpecialOrthogonalBasisMatrix n b)ᵀ
      (identitySpecialOrthogonalBasisMatrix n b),
    hA', one_mul,
    identitySpecialOrthogonalOrientationCorrection_transpose_mul_self]

theorem identitySpecialOrthogonalOrientedBasisMatrix_lastColumn
    (hn : 0 < n)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ
      (identitySpecialOrthogonalEuclideanSpace n))
    (i : Fin (n + 1)) :
    identitySpecialOrthogonalOrientedBasisMatrix n b i (Fin.last n) =
      b (Fin.last n) i := by
  classical
  have hlast : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro h
    have : n = 0 := by
      simpa [Fin.ext_iff] using congrArg Fin.val h
    omega
  simp [identitySpecialOrthogonalOrientedBasisMatrix,
    identitySpecialOrthogonalOrientationCorrection,
    identitySpecialOrthogonalOrientationSign, hlast]

theorem exists_identitySpecialOrthogonalOrthonormalBasis_last
    (y : identitySpecialOrthogonalLastColumnSphere n) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ
        (identitySpecialOrthogonalEuclideanSpace n),
      b (Fin.last n) = y.1 := by
  let v : Fin (n + 1) → identitySpecialOrthogonalEuclideanSpace n :=
    fun _ => y.1
  have hy_norm : ‖y.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.2
  have hv : Orthonormal ℝ (({Fin.last n} : Set (Fin (n + 1))).restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = Fin.last n := by simpa using hi
    have hj' : j = Fin.last n := by simpa using hj
    subst i
    subst j
    simp [v, hy_norm]
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq
      (by simp [identitySpecialOrthogonalEuclideanSpace])
  exact ⟨b, hb (Fin.last n) (by simp)⟩

theorem exists_identitySpecialOrthogonalLastColumn_eq
    (hn : 0 < n)
    (y : identitySpecialOrthogonalLastColumnSphere n) :
    ∃ g : identitySpecialOrthogonalGroup n,
      identitySpecialOrthogonalLastColumn n g = y := by
  obtain ⟨b, hb⟩ :=
    exists_identitySpecialOrthogonalOrthonormalBasis_last n y
  let A := identitySpecialOrthogonalOrientedBasisMatrix n b
  have hAform : Aᵀ * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) * A = 1 := by
    simpa [A] using
      identitySpecialOrthogonalOrientedBasisMatrix_transpose_mul_self n b
  let gset : Matrix.specialOrthogonalMatrixSet
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
    ⟨A, (Matrix.formPreservingConstraint_eq_zero_iff _ _).mpr hAform,
      identitySpecialOrthogonalOrientedBasisMatrix_det n b⟩
  let g : identitySpecialOrthogonalGroup n :=
    specialOrthogonalMatrixSetToSpecialSubgroup _ gset
  refine ⟨g, ?_⟩
  apply Subtype.ext
  ext i
  change A i (Fin.last n) = y.1 i
  dsimp [A]
  rw [identitySpecialOrthogonalOrientedBasisMatrix_lastColumn n hn b i, hb]

theorem surjective_identitySpecialOrthogonalLastColumn
    (hn : 0 < n) :
    Function.Surjective (identitySpecialOrthogonalLastColumn n) :=
  fun y => exists_identitySpecialOrthogonalLastColumn_eq n hn y

end PositiveDefiniteIntegralLattice
