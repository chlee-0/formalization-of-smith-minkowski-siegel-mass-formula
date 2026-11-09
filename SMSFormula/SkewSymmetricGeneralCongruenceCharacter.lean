import SMSFormula.SkewAdjointRealCongruenceElementaryResidual

/-!
# The skew-symmetric congruence determinant over a general field

Congruence by an invertible matrix on skew-symmetric matrices has determinant
equal to the `(n - 1)`st power of the ordinary matrix determinant.  The proof
uses diagonal--transvection induction and only assumes that two is nonzero.

This field-independent version is used for the real special-orthogonal
adjoint action.
-/

noncomputable section

set_option maxRecDepth 2000

open scoped Matrix BigOperators

namespace Matrix

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

private theorem ringChar_ne_two : ringChar K ≠ 2 := by
  rw [ringChar.eq_zero]
  norm_num

/-- Congruence `Y ↦ Cᵀ Y C` on skew-symmetric matrices over a field. -/
def skewSymmetricCongruenceEndomorphism
    (C : Matrix (Fin n) (Fin n) K) :
    skewSymmetricMatricesSubmodule (R := K) (ι := Fin n) →ₗ[K]
      skewSymmetricMatricesSubmodule (R := K) (ι := Fin n) where
  toFun Y := ⟨Cᵀ * (Y : Matrix (Fin n) (Fin n) K) * C, by
    change (Cᵀ * (Y : Matrix (Fin n) (Fin n) K) * C)ᵀ =
      -(Cᵀ * (Y : Matrix (Fin n) (Fin n) K) * C)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Y.property]
    noncomm_ring⟩
  map_add' Y Z := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a Y := by
    apply Subtype.ext
    simp

omit [CharZero K] in
@[simp]
theorem coe_skewSymmetricCongruenceEndomorphism_apply
    (C : Matrix (Fin n) (Fin n) K)
    (Y : skewSymmetricMatricesSubmodule (R := K) (ι := Fin n)) :
    (skewSymmetricCongruenceEndomorphism C Y :
        Matrix (Fin n) (Fin n) K) =
      Cᵀ * (Y : Matrix (Fin n) (Fin n) K) * C :=
  rfl

/-- Skew-symmetric congruence in strict-upper coordinates. -/
def skewSymmetricCongruenceCoordinateEndomorphism
    (C : Matrix (Fin n) (Fin n) K) :
    (StrictUpperPair n → K) →ₗ[K] (StrictUpperPair n → K) :=
  (skewSymmetricUpperCoordinateEquiv
      (K := K) (ringChar_ne_two (K := K))).toLinearMap.comp <|
    (skewSymmetricCongruenceEndomorphism C).comp
      (skewSymmetricUpperCoordinateEquiv
        (K := K) (ringChar_ne_two (K := K))).symm.toLinearMap

@[simp]
theorem skewSymmetricCongruenceCoordinateEndomorphism_apply_apply
    (C : Matrix (Fin n) (Fin n) K)
    (c : StrictUpperPair n → K) (q : StrictUpperPair n) :
    skewSymmetricCongruenceCoordinateEndomorphism C c q =
      (Cᵀ * skewSymmetricMatrixOfUpperCoordinates c * C) q.1.1 q.1.2 :=
  rfl

/-- Strict-upper coordinates do not alter the determinant. -/
theorem det_skewSymmetricCongruenceCoordinateEndomorphism
    (C : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (skewSymmetricCongruenceCoordinateEndomorphism C) =
      LinearMap.det (skewSymmetricCongruenceEndomorphism C) := by
  simpa only [skewSymmetricCongruenceCoordinateEndomorphism,
    LinearMap.comp_assoc] using
    LinearMap.det_conj
      (skewSymmetricCongruenceEndomorphism C)
      (skewSymmetricUpperCoordinateEquiv
        (K := K) (ringChar_ne_two (K := K)))

/-- In strict-upper coordinates, diagonal congruence is multiplication by
the pairwise products of the diagonal entries. -/
@[simp]
theorem skewSymmetricDiagonalCoordinateEndomorphism_apply_apply
    (d : Fin n → K) (c : StrictUpperPair n → K)
    (q : StrictUpperPair n) :
    skewSymmetricCongruenceCoordinateEndomorphism
        (Matrix.diagonal d) c q =
      d q.1.1 * d q.1.2 * c q := by
  change
    (((diagonal d)ᵀ * skewSymmetricMatrixOfUpperCoordinates c *
      diagonal d) q.1.1 q.1.2) = _
  simp [q.2, Matrix.diagonal_transpose,
    skewSymmetricMatrixOfUpperCoordinates]
  ring

/-- The determinant of diagonal congruence is the expected determinant
power. -/
theorem det_skewSymmetricCongruenceEndomorphism_diagonal
    (d : Fin n → K) :
    LinearMap.det
        (skewSymmetricCongruenceEndomorphism (Matrix.diagonal d)) =
      Matrix.det (Matrix.diagonal d) ^ (n - 1) := by
  rw [← det_skewSymmetricCongruenceCoordinateEndomorphism]
  rw [← LinearMap.det_toMatrix (Pi.basisFun K (StrictUpperPair n))]
  have hmatrix :
      LinearMap.toMatrix (Pi.basisFun K (StrictUpperPair n))
          (Pi.basisFun K (StrictUpperPair n))
          (skewSymmetricCongruenceCoordinateEndomorphism
            (Matrix.diagonal d)) =
        Matrix.diagonal (fun q : StrictUpperPair n ↦
          d q.1.1 * d q.1.2) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Pi.basisFun_repr,
      skewSymmetricDiagonalCoordinateEndomorphism_apply_apply]
    by_cases hij : i = j
    · subst i
      rw [Matrix.diagonal_apply_eq]
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp [hij]
  rw [hmatrix, Matrix.det_diagonal, StrictUpperPair.prod_endpoint_mul,
    Matrix.det_diagonal]

omit [CharZero K] in
/-- Congruence by a product is the corresponding composite. -/
theorem skewSymmetricCongruenceEndomorphism_mul
    (C D : Matrix (Fin n) (Fin n) K) :
    skewSymmetricCongruenceEndomorphism (C * D) =
      (skewSymmetricCongruenceEndomorphism D).comp
        (skewSymmetricCongruenceEndomorphism C) := by
  apply LinearMap.ext
  intro Y
  apply Subtype.ext
  simp only [LinearMap.comp_apply,
    coe_skewSymmetricCongruenceEndomorphism_apply,
    Matrix.transpose_mul]
  noncomm_ring

omit [CharZero K] in
/-- Congruence by the identity is the identity linear map. -/
theorem skewSymmetricCongruenceEndomorphism_one :
    skewSymmetricCongruenceEndomorphism
        (1 : Matrix (Fin n) (Fin n) K) = LinearMap.id := by
  apply LinearMap.ext
  intro Y
  apply Subtype.ext
  simp

omit [CharZero K] in
/-- The congruence determinant is multiplicative. -/
theorem det_skewSymmetricCongruenceEndomorphism_mul
    (C D : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (skewSymmetricCongruenceEndomorphism (C * D)) =
      LinearMap.det (skewSymmetricCongruenceEndomorphism C) *
        LinearMap.det (skewSymmetricCongruenceEndomorphism D) := by
  rw [skewSymmetricCongruenceEndomorphism_mul,
    LinearMap.det_comp, mul_comm]

/-- Congruence by a matrix unit is a linear equivalence. -/
def skewSymmetricCongruenceLinearEquiv
    (W : GL (Fin n) K) :
    skewSymmetricMatricesSubmodule (R := K) (ι := Fin n) ≃ₗ[K]
      skewSymmetricMatricesSubmodule (R := K) (ι := Fin n) :=
  LinearEquiv.mk
    (skewSymmetricCongruenceEndomorphism
      (W : Matrix (Fin n) (Fin n) K))
    (skewSymmetricCongruenceEndomorphism
      (W⁻¹ : Matrix (Fin n) (Fin n) K))
    (fun Y => by
      have hcomp :
          (skewSymmetricCongruenceEndomorphism
              (W⁻¹ : Matrix (Fin n) (Fin n) K)).comp
            (skewSymmetricCongruenceEndomorphism
              (W : Matrix (Fin n) (Fin n) K)) = LinearMap.id := by
        rw [← skewSymmetricCongruenceEndomorphism_mul]
        rw [← Matrix.GeneralLinearGroup.coe_inv,
          ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one,
          skewSymmetricCongruenceEndomorphism_one]
      exact LinearMap.congr_fun hcomp Y)
    (fun Y => by
      have hcomp :
          (skewSymmetricCongruenceEndomorphism
              (W : Matrix (Fin n) (Fin n) K)).comp
            (skewSymmetricCongruenceEndomorphism
              (W⁻¹ : Matrix (Fin n) (Fin n) K)) = LinearMap.id := by
        rw [← skewSymmetricCongruenceEndomorphism_mul]
        rw [← Matrix.GeneralLinearGroup.coe_inv,
          ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.GeneralLinearGroup.coe_one,
          skewSymmetricCongruenceEndomorphism_one]
      exact LinearMap.congr_fun hcomp Y)

/-- The determinant character of congruence on skew-symmetric matrices. -/
def skewSymmetricCongruenceDetCharacter : GL (Fin n) K →* Kˣ where
  toFun W := Units.mk0
    (LinearMap.det (skewSymmetricCongruenceEndomorphism
      (W : Matrix (Fin n) (Fin n) K)))
    (by
      change LinearMap.det
          (skewSymmetricCongruenceLinearEquiv W).toLinearMap ≠ 0
      rw [← LinearEquiv.coe_det]
      exact Units.ne_zero _)
  map_one' := by
    apply Units.ext
    change LinearMap.det
        (skewSymmetricCongruenceEndomorphism
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1
    rw [Matrix.GeneralLinearGroup.coe_one,
      skewSymmetricCongruenceEndomorphism_one, LinearMap.det_id]
  map_mul' W Z := by
    apply Units.ext
    change LinearMap.det
        (skewSymmetricCongruenceEndomorphism
          ((W * Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = _
    rw [Matrix.GeneralLinearGroup.coe_mul,
      det_skewSymmetricCongruenceEndomorphism_mul]
    rfl

private def twoUnit : Kˣ := Units.mk0 2 (by norm_num)

private theorem coordinateUnit_two_conj_transvection
    (t : TransvectionStruct (Fin n) K) :
    Matrix.GeneralLinearGroup.coordinateUnit t.i (twoUnit (K := K)) *
          t.toGeneralLinearGroup *
        (Matrix.GeneralLinearGroup.coordinateUnit
          t.i (twoUnit (K := K)))⁻¹ =
      t.toGeneralLinearGroup * t.toGeneralLinearGroup := by
  apply Units.ext
  ext a b
  simp only [Matrix.GeneralLinearGroup.coe_mul,
    Matrix.TransvectionStruct.coe_toGeneralLinearGroup]
  rw [show t.toMatrix = Matrix.transvection t.i t.j t.c by rfl]
  rw [show
    (Matrix.GeneralLinearGroup.coordinateUnit t.i (twoUnit (K := K)) :
        Matrix (Fin n) (Fin n) K) =
      diagonal (fun j ↦ if j = t.i then (twoUnit (K := K) : K) else 1) by
        rfl]
  rw [show
    (↑((Matrix.GeneralLinearGroup.coordinateUnit
      t.i (twoUnit (K := K)))⁻¹) : Matrix (Fin n) (Fin n) K) =
      diagonal (fun j ↦ if j = t.i then
        (((twoUnit (K := K))⁻¹ : Kˣ) : K) else 1) by rfl]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Matrix.transvection_mul_transvection_same
    t.i t.j t.hij t.c t.c]
  have hij : t.i ≠ t.j := t.hij
  by_cases hai : t.i = a <;>
    by_cases hbj : t.j = b <;>
    by_cases hab : b = a <;>
    by_cases hbi : t.i = b <;>
    simp_all [Matrix.transvection, Matrix.single, twoUnit, eq_comm]
  all_goals ring

private theorem skewSymmetricCongruenceDetCharacter_transvection
    (t : TransvectionStruct (Fin n) K) :
    skewSymmetricCongruenceDetCharacter
        t.toGeneralLinearGroup = 1 := by
  let χ := skewSymmetricCongruenceDetCharacter (K := K) (n := n)
  let D := Matrix.GeneralLinearGroup.coordinateUnit t.i (twoUnit (K := K))
  let T := t.toGeneralLinearGroup
  have hconj : D * T * D⁻¹ = T * T :=
    coordinateUnit_two_conj_transvection t
  have hclass : χ (D * T * D⁻¹) = χ T := by
    rw [map_mul, map_mul, map_inv]
    calc
      χ D * χ T * (χ D)⁻¹ = χ T * (χ D * (χ D)⁻¹) := by ac_rfl
      _ = χ T := by simp
  have hidem : χ T = χ T * χ T := by
    calc
      χ T = χ (D * T * D⁻¹) := hclass.symm
      _ = χ (T * T) := congrArg χ hconj
      _ = χ T * χ T := map_mul χ T T
  apply mul_left_cancel (a := χ T)
  simpa using hidem.symm

/-- Congruence on skew-symmetric matrices has determinant
`det(W)^(n-1)`. -/
theorem det_skewSymmetricCongruenceEndomorphism_eq_det_pow
    (W : GL (Fin n) K) :
    LinearMap.det (skewSymmetricCongruenceEndomorphism
        (W : Matrix (Fin n) (Fin n) K)) =
      Matrix.det (W : Matrix (Fin n) (Fin n) K) ^ (n - 1) := by
  let P : Matrix (Fin n) (Fin n) K → Prop := fun M ↦
    ∀ hM : Matrix.det M ≠ 0,
      LinearMap.det (skewSymmetricCongruenceEndomorphism M) =
        Matrix.det M ^ (n - 1)
  have hWdet : Matrix.det (W : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    change ((Matrix.GeneralLinearGroup.det W : Kˣ) : K) ≠ 0
    exact Units.ne_zero _
  have hP : P (W : Matrix (Fin n) (Fin n) K) := by
    apply Matrix.diagonal_transvection_induction_of_det_ne_zero
      P (W : Matrix (Fin n) (Fin n) K) hWdet
    · intro D hDdet
      dsimp only [P]
      intro hD
      exact det_skewSymmetricCongruenceEndomorphism_diagonal D
    · intro t
      dsimp only [P]
      intro ht
      have hmk : Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix ht =
          t.toGeneralLinearGroup := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
          Matrix.TransvectionStruct.coe_toGeneralLinearGroup]
      have hchar := skewSymmetricCongruenceDetCharacter_transvection t
      apply_fun ((↑) : Kˣ → K) at hchar
      rw [show t.toMatrix =
          (t.toGeneralLinearGroup : Matrix (Fin n) (Fin n) K) by rfl,
        ← hmk]
      simpa [skewSymmetricCongruenceDetCharacter] using hchar
    · intro A B hA hB hPA hPB
      dsimp only [P] at hPA hPB ⊢
      intro hAB
      rw [det_skewSymmetricCongruenceEndomorphism_mul,
        Matrix.det_mul, hPA hA, hPB hB, mul_pow]
  exact hP hWdet

end Matrix
