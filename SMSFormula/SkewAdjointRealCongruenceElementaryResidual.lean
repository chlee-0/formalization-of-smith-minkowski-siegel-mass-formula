import SMSFormula.SkewAdjointPositiveDiagonalElementaryResidual
import SMSFormula.SkewSymmetricPadicGeneralCongruenceCharacter

/-!
# The rational-congruence elementary tangent residual

Congruence by a rational matrix unit acts on the form-adapted elementary
skew-adjoint coordinates through the skew-symmetric congruence
`S ↦ Wᵀ S W`.  This file computes the determinant of that direct
`StrictUpperPair` action and then compares it with the independently reindexed
finite bases used by `skewAdjointRealCongruenceFormElementaryDetScalar`.

The signed comparison retains the determinant of the resulting finite
reindexing.  Only its absolute value is discarded.
-/

noncomputable section

set_option maxRecDepth 2000

open scoped Matrix BigOperators
open PositiveDefiniteIntegralLattice

namespace Matrix

variable {n : ℕ}

/-- Rational congruence `Y ↦ Cᵀ Y C` on skew-symmetric matrices. -/
def skewSymmetricRationalCongruenceEndomorphism
    (C : Matrix (Fin n) (Fin n) ℚ) :
    skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n) →ₗ[ℚ]
      skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n) where
  toFun Y := ⟨Cᵀ * (Y : Matrix (Fin n) (Fin n) ℚ) * C, by
    change (Cᵀ * (Y : Matrix (Fin n) (Fin n) ℚ) * C)ᵀ =
      -(Cᵀ * (Y : Matrix (Fin n) (Fin n) ℚ) * C)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Y.property]
    noncomm_ring⟩
  map_add' Y Z := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a Y := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_skewSymmetricRationalCongruenceEndomorphism_apply
    (C : Matrix (Fin n) (Fin n) ℚ)
    (Y : skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n)) :
    (skewSymmetricRationalCongruenceEndomorphism C Y :
        Matrix (Fin n) (Fin n) ℚ) =
      Cᵀ * (Y : Matrix (Fin n) (Fin n) ℚ) * C :=
  rfl

/-- Rational skew-symmetric congruence in strict-upper coordinates. -/
def skewSymmetricRationalCongruenceCoordinateEndomorphism
    (C : Matrix (Fin n) (Fin n) ℚ) :
    (StrictUpperPair n → ℚ) →ₗ[ℚ] (StrictUpperPair n → ℚ) :=
  (skewSymmetricUpperCoordinateEquiv (K := ℚ) (by norm_num)).toLinearMap.comp <|
    (skewSymmetricRationalCongruenceEndomorphism C).comp
      (skewSymmetricUpperCoordinateEquiv (K := ℚ) (by norm_num)).symm.toLinearMap

@[simp]
theorem skewSymmetricRationalCongruenceCoordinateEndomorphism_apply_apply
    (C : Matrix (Fin n) (Fin n) ℚ)
    (c : StrictUpperPair n → ℚ) (q : StrictUpperPair n) :
    skewSymmetricRationalCongruenceCoordinateEndomorphism C c q =
      (Cᵀ * skewSymmetricMatrixOfUpperCoordinates c * C) q.1.1 q.1.2 :=
  rfl

/-- Strict-upper coordinates do not alter the determinant of rational
skew-symmetric congruence. -/
theorem det_skewSymmetricRationalCongruenceCoordinateEndomorphism
    (C : Matrix (Fin n) (Fin n) ℚ) :
    LinearMap.det (skewSymmetricRationalCongruenceCoordinateEndomorphism C) =
      LinearMap.det (skewSymmetricRationalCongruenceEndomorphism C) := by
  simpa only [skewSymmetricRationalCongruenceCoordinateEndomorphism,
    LinearMap.comp_assoc] using
    LinearMap.det_conj
      (skewSymmetricRationalCongruenceEndomorphism C)
      (skewSymmetricUpperCoordinateEquiv (K := ℚ) (by norm_num))

/-- In strict-upper coordinates, rational diagonal congruence is pointwise
multiplication by the pairwise products of diagonal entries. -/
@[simp]
theorem skewSymmetricRationalDiagonalCoordinateEndomorphism_apply_apply
    (d : Fin n → ℚ) (c : StrictUpperPair n → ℚ)
    (q : StrictUpperPair n) :
    skewSymmetricRationalCongruenceCoordinateEndomorphism
        (Matrix.diagonal d) c q =
      d q.1.1 * d q.1.2 * c q := by
  change
    (((diagonal d)ᵀ * skewSymmetricMatrixOfUpperCoordinates c *
      diagonal d) q.1.1 q.1.2) = _
  simp [q.2, Matrix.diagonal_transpose,
    skewSymmetricMatrixOfUpperCoordinates]
  ring

/-- The determinant of rational diagonal congruence is the expected power of
the matrix determinant. -/
theorem det_skewSymmetricRationalCongruenceEndomorphism_diagonal
    (d : Fin n → ℚ) :
    LinearMap.det
        (skewSymmetricRationalCongruenceEndomorphism (Matrix.diagonal d)) =
      Matrix.det (Matrix.diagonal d) ^ (n - 1) := by
  rw [← det_skewSymmetricRationalCongruenceCoordinateEndomorphism]
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℚ (StrictUpperPair n))]
  have hmatrix :
      LinearMap.toMatrix (Pi.basisFun ℚ (StrictUpperPair n))
          (Pi.basisFun ℚ (StrictUpperPair n))
          (skewSymmetricRationalCongruenceCoordinateEndomorphism
            (Matrix.diagonal d)) =
        Matrix.diagonal (fun q : StrictUpperPair n =>
          d q.1.1 * d q.1.2) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Pi.basisFun_repr,
      skewSymmetricRationalDiagonalCoordinateEndomorphism_apply_apply]
    by_cases hij : i = j
    · subst i
      rw [Matrix.diagonal_apply_eq]
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp [hij]
  rw [hmatrix, Matrix.det_diagonal, StrictUpperPair.prod_endpoint_mul,
    Matrix.det_diagonal]

/-- Congruence by a product is the corresponding composite, in the order
forced by transposition. -/
theorem skewSymmetricRationalCongruenceEndomorphism_mul
    (C D : Matrix (Fin n) (Fin n) ℚ) :
    skewSymmetricRationalCongruenceEndomorphism (C * D) =
      (skewSymmetricRationalCongruenceEndomorphism D).comp
        (skewSymmetricRationalCongruenceEndomorphism C) := by
  apply LinearMap.ext
  intro Y
  apply Subtype.ext
  simp only [LinearMap.comp_apply,
    coe_skewSymmetricRationalCongruenceEndomorphism_apply,
    Matrix.transpose_mul]
  noncomm_ring

/-- Congruence by the identity matrix is the identity linear map. -/
theorem skewSymmetricRationalCongruenceEndomorphism_one :
    skewSymmetricRationalCongruenceEndomorphism
        (1 : Matrix (Fin n) (Fin n) ℚ) = LinearMap.id := by
  apply LinearMap.ext
  intro Y
  apply Subtype.ext
  simp

/-- The rational congruence determinant is multiplicative. -/
theorem det_skewSymmetricRationalCongruenceEndomorphism_mul
    (C D : Matrix (Fin n) (Fin n) ℚ) :
    LinearMap.det (skewSymmetricRationalCongruenceEndomorphism (C * D)) =
      LinearMap.det (skewSymmetricRationalCongruenceEndomorphism C) *
        LinearMap.det (skewSymmetricRationalCongruenceEndomorphism D) := by
  rw [skewSymmetricRationalCongruenceEndomorphism_mul,
    LinearMap.det_comp, mul_comm]

/-- Rational skew-symmetric congruence by a matrix unit is a linear
equivalence. -/
def skewSymmetricRationalCongruenceLinearEquiv
    (W : GL (Fin n) ℚ) :
    skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n) ≃ₗ[ℚ]
      skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n) :=
  LinearEquiv.mk
    (skewSymmetricRationalCongruenceEndomorphism
      (W : Matrix (Fin n) (Fin n) ℚ))
    (skewSymmetricRationalCongruenceEndomorphism
      (W⁻¹ : Matrix (Fin n) (Fin n) ℚ))
    (fun Y => by
      have hcomp :
          (skewSymmetricRationalCongruenceEndomorphism
              (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)).comp
            (skewSymmetricRationalCongruenceEndomorphism
              (W : Matrix (Fin n) (Fin n) ℚ)) = LinearMap.id := by
        rw [← skewSymmetricRationalCongruenceEndomorphism_mul]
        have hmat :
            (W : Matrix (Fin n) (Fin n) ℚ) *
                (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) = 1 := by
          exact Matrix.mul_nonsing_inv _
            ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit W))
        rw [hmat, skewSymmetricRationalCongruenceEndomorphism_one]
      exact LinearMap.congr_fun hcomp Y)
    (fun Y => by
      have hcomp :
          (skewSymmetricRationalCongruenceEndomorphism
              (W : Matrix (Fin n) (Fin n) ℚ)).comp
            (skewSymmetricRationalCongruenceEndomorphism
              (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)) = LinearMap.id := by
        rw [← skewSymmetricRationalCongruenceEndomorphism_mul]
        have hmat :
            (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) *
                (W : Matrix (Fin n) (Fin n) ℚ) = 1 := by
          exact Matrix.nonsing_inv_mul _
            ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit W))
        rw [hmat, skewSymmetricRationalCongruenceEndomorphism_one]
      exact LinearMap.congr_fun hcomp Y)

/-- The determinant character of rational congruence on skew-symmetric
matrices. -/
def skewSymmetricRationalCongruenceDetCharacter :
    GL (Fin n) ℚ →* ℚˣ where
  toFun W := Units.mk0
    (LinearMap.det (skewSymmetricRationalCongruenceEndomorphism
      (W : Matrix (Fin n) (Fin n) ℚ)))
    (by
      change LinearMap.det
          (skewSymmetricRationalCongruenceLinearEquiv W).toLinearMap ≠ 0
      rw [← LinearEquiv.coe_det]
      exact Units.ne_zero _)
  map_one' := by
    apply Units.ext
    change LinearMap.det
        (skewSymmetricRationalCongruenceEndomorphism
          ((1 : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)) = 1
    rw [Matrix.GeneralLinearGroup.coe_one,
      skewSymmetricRationalCongruenceEndomorphism_one, LinearMap.det_id]
  map_mul' W Z := by
    apply Units.ext
    change LinearMap.det
        (skewSymmetricRationalCongruenceEndomorphism
          ((W * Z : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)) = _
    rw [Matrix.GeneralLinearGroup.coe_mul,
      det_skewSymmetricRationalCongruenceEndomorphism_mul]
    rfl

private def rationalTwoUnit : ℚˣ := Units.mk0 2 (by norm_num)

private theorem rational_coordinateUnit_two_conj_transvection
    (t : TransvectionStruct (Fin n) ℚ) :
    Matrix.GeneralLinearGroup.coordinateUnit t.i rationalTwoUnit *
          t.toGeneralLinearGroup *
        (Matrix.GeneralLinearGroup.coordinateUnit
          t.i rationalTwoUnit)⁻¹ =
      t.toGeneralLinearGroup * t.toGeneralLinearGroup := by
  apply Units.ext
  ext a b
  simp only [Matrix.GeneralLinearGroup.coe_mul,
    Matrix.TransvectionStruct.coe_toGeneralLinearGroup]
  rw [show t.toMatrix = Matrix.transvection t.i t.j t.c by rfl]
  rw [show
    (Matrix.GeneralLinearGroup.coordinateUnit t.i rationalTwoUnit :
        Matrix (Fin n) (Fin n) ℚ) =
      diagonal (fun j => if j = t.i then (rationalTwoUnit : ℚ) else 1) by
        rfl]
  rw [show
    (↑((Matrix.GeneralLinearGroup.coordinateUnit
      t.i rationalTwoUnit)⁻¹) : Matrix (Fin n) (Fin n) ℚ) =
      diagonal (fun j => if j = t.i then
        (((rationalTwoUnit)⁻¹ : ℚˣ) : ℚ) else 1) by rfl]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Matrix.transvection_mul_transvection_same
    t.i t.j t.hij t.c t.c]
  have hij : t.i ≠ t.j := t.hij
  by_cases hai : t.i = a <;>
    by_cases hbj : t.j = b <;>
    by_cases hab : b = a <;>
    by_cases hbi : t.i = b <;>
    simp_all [Matrix.transvection, Matrix.single, rationalTwoUnit, eq_comm] ; ring

private theorem skewSymmetricRationalCongruenceDetCharacter_transvection
    (t : TransvectionStruct (Fin n) ℚ) :
    skewSymmetricRationalCongruenceDetCharacter
        t.toGeneralLinearGroup = 1 := by
  let χ := skewSymmetricRationalCongruenceDetCharacter (n := n)
  let D := Matrix.GeneralLinearGroup.coordinateUnit t.i rationalTwoUnit
  let T := t.toGeneralLinearGroup
  have hconj : D * T * D⁻¹ = T * T :=
    rational_coordinateUnit_two_conj_transvection t
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

/-- The determinant of rational congruence on skew-symmetric matrices is the
`(n - 1)`st power of the usual matrix determinant. -/
theorem det_skewSymmetricRationalCongruenceEndomorphism_eq_det_pow
    (W : GL (Fin n) ℚ) :
    LinearMap.det (skewSymmetricRationalCongruenceEndomorphism
        (W : Matrix (Fin n) (Fin n) ℚ)) =
      Matrix.det (W : Matrix (Fin n) (Fin n) ℚ) ^ (n - 1) := by
  let P : Matrix (Fin n) (Fin n) ℚ → Prop := fun M =>
    ∀ hM : Matrix.det M ≠ 0,
      LinearMap.det (skewSymmetricRationalCongruenceEndomorphism M) =
        Matrix.det M ^ (n - 1)
  have hWdet : Matrix.det (W : Matrix (Fin n) (Fin n) ℚ) ≠ 0 := by
    change ((Matrix.GeneralLinearGroup.det W : ℚˣ) : ℚ) ≠ 0
    exact Units.ne_zero _
  have hP : P (W : Matrix (Fin n) (Fin n) ℚ) := by
    apply Matrix.diagonal_transvection_induction_of_det_ne_zero
      P (W : Matrix (Fin n) (Fin n) ℚ) hWdet
    · intro D hDdet
      dsimp only [P]
      intro hD
      exact det_skewSymmetricRationalCongruenceEndomorphism_diagonal D
    · intro t
      dsimp only [P]
      intro ht
      have hmk : Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix ht =
          t.toGeneralLinearGroup := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
          Matrix.TransvectionStruct.coe_toGeneralLinearGroup]
      have hchar := skewSymmetricRationalCongruenceDetCharacter_transvection t
      apply_fun ((↑) : ℚˣ → ℚ) at hchar
      rw [show t.toMatrix =
          (t.toGeneralLinearGroup : Matrix (Fin n) (Fin n) ℚ) by rfl,
        ← hmk]
      simpa [skewSymmetricRationalCongruenceDetCharacter] using hchar
    · intro A B hA hB hPA hPB
      dsimp only [P] at hPA hPB ⊢
      intro hAB
      rw [det_skewSymmetricRationalCongruenceEndomorphism_mul,
        Matrix.det_mul, hPA hA, hPB hB, mul_pow]
  exact hP hWdet

/-- The directly indexed form-elementary rational basis transported by
rational skew-adjoint congruence. -/
def skewAdjointCongruenceTransportedFormElementaryRationalBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    Module.Basis (StrictUpperPair n) ℚ
      (skewAdjointMatricesLieSubalgebra
        (skewAdjointCongruenceForm F W)) :=
  (skewAdjointFormElementaryRationalBasis F hF hdet).map
    (skewAdjointCongruenceLinearEquiv F W)

/-- After congruence, multiplication by the target form recovers the literal
skew-symmetric coordinate `Wᵀ S W`. -/
theorem skewAdjointCongruenceTransportedFormElementaryRationalBasis_coordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ)
    (q : StrictUpperPair n) :
    skewAdjointCongruenceForm F W *
        (skewAdjointCongruenceTransportedFormElementaryRationalBasis
          F hF hdet W q : Matrix (Fin n) (Fin n) ℚ) =
      (W : Matrix (Fin n) (Fin n) ℚ)ᵀ *
        (Matrix.single q.1.1 q.1.2 1 -
          Matrix.single q.1.2 q.1.1 1) *
        (W : Matrix (Fin n) (Fin n) ℚ) := by
  let A : Matrix (Fin n) (Fin n) ℚ := W
  let B : Matrix (Fin n) (Fin n) ℚ := A⁻¹
  let S : Matrix (Fin n) (Fin n) ℚ :=
    Matrix.single q.1.1 q.1.2 1 - Matrix.single q.1.2 q.1.1 1
  have hAB : A * B = 1 := by
    exact Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit W))
  have hFF : F * F⁻¹ = 1 := by
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  rw [skewAdjointCongruenceTransportedFormElementaryRationalBasis,
    Module.Basis.map_apply,
    coe_skewAdjointCongruenceLinearEquiv_apply,
    coe_skewAdjointFormElementaryRationalBasis_apply]
  rw [skewAdjointCongruenceForm]
  change (Aᵀ * F * A) * (B * (F⁻¹ * S) * A) = Aᵀ * S * A
  calc
    (Aᵀ * F * A) * (B * (F⁻¹ * S) * A) =
        Aᵀ * F * (A * B) * F⁻¹ * S * A := by noncomm_ring
    _ = Aᵀ * (F * F⁻¹) * S * A := by rw [hAB]; noncomm_ring
    _ = Aᵀ * S * A := by rw [hFF]; simp

/-- The target form-coordinate equivalence sends the transported direct
elementary basis to the direct skew-symmetric basis acted on by rational
congruence. -/
theorem skewAdjointCongruenceTransportedFormElementaryRationalBasis_map_target
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    (skewAdjointCongruenceTransportedFormElementaryRationalBasis
        F hF hdet W).map
      (skewAdjointRationalSkewSymmetricLinearEquiv
        (skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)) =
      (skewSymmetricBasis (K := ℚ) (by norm_num)).map
        (skewSymmetricRationalCongruenceLinearEquiv W) := by
  apply DFunLike.ext _ _
  intro q
  simp only [Module.Basis.map_apply]
  apply Subtype.ext
  rw [coe_skewAdjointRationalSkewSymmetricLinearEquiv_apply]
  rw [skewAdjointCongruenceTransportedFormElementaryRationalBasis_coordinate]
  rw [show
      (skewSymmetricRationalCongruenceLinearEquiv W
          (skewSymmetricBasis (K := ℚ) (by norm_num) q) :
        Matrix (Fin n) (Fin n) ℚ) =
        (W : Matrix (Fin n) (Fin n) ℚ)ᵀ *
          (skewSymmetricBasis (K := ℚ) (by norm_num) q :
            Matrix (Fin n) (Fin n) ℚ) *
          (W : Matrix (Fin n) (Fin n) ℚ) by rfl]
  rw [skewSymmetricBasis_apply_coe]

/-- In direct strict-upper form-elementary bases, the rational skew-adjoint
congruence residual is exactly the determinant of skew-symmetric congruence. -/
theorem skewAdjointFormElementaryRationalBasis_det_congruenceTransported
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    (skewAdjointFormElementaryRationalBasis
        (skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).det
      (skewAdjointCongruenceTransportedFormElementaryRationalBasis
        F hF hdet W) =
      Matrix.det (W : Matrix (Fin n) (Fin n) ℚ) ^ (n - 1) := by
  let E := skewAdjointRationalSkewSymmetricLinearEquiv
    (skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let A := skewAdjointFormElementaryRationalBasis
    (skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let B := skewAdjointCongruenceTransportedFormElementaryRationalBasis
    F hF hdet W
  have hmapA : A.map E = skewSymmetricBasis (K := ℚ) (by norm_num) := by
    apply DFunLike.ext _ _
    intro q
    apply Subtype.ext
    simp [A, E, skewAdjointFormElementaryRationalBasis]
  have hmapB : B.map E =
      (skewSymmetricBasis (K := ℚ) (by norm_num)).map
        (skewSymmetricRationalCongruenceLinearEquiv W) := by
    exact
      skewAdjointCongruenceTransportedFormElementaryRationalBasis_map_target
        F hF hdet W
  have hdetMap : (A.map E).det (B.map E) = A.det B := by
    rw [Module.Basis.det_map]
    congr 1
    ext q
    simp
  rw [← hdetMap, hmapA, hmapB]
  rw [Module.Basis.det_apply]
  let b := skewSymmetricBasis (K := ℚ) (by norm_num) (n := n)
  let e := skewSymmetricRationalCongruenceLinearEquiv W
  have hmatrix : b.toMatrix (b.map e) =
      LinearMap.toMatrix b b e.toLinearMap := by
    ext i j
    simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
  change Matrix.det (b.toMatrix (b.map e)) = _
  rw [hmatrix, LinearMap.det_toMatrix]
  change LinearMap.det
      (skewSymmetricRationalCongruenceLinearEquiv W).toLinearMap = _
  exact det_skewSymmetricRationalCongruenceEndomorphism_eq_det_pow W

/-- The directly indexed real form-elementary basis transported by the
scalar-extended rational congruence. -/
def skewAdjointRealCongruenceTransportedFormElementaryRealBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    Module.Basis (StrictUpperPair n) ℝ
      (skewAdjointMatricesLieSubalgebra
        ((skewAdjointCongruenceForm F W).map (algebraMap ℚ ℝ))) :=
  (skewAdjointFormElementaryRealBasis F hF hdet).map
    (skewAdjointRealCongruenceContinuousLinearEquiv F W).toLinearEquiv

/-- Direct real congruence is exactly scalar extension of the directly
transported rational elementary basis. -/
theorem
    skewAdjointRealCongruenceTransportedFormElementaryRealBasis_eq_scalarExtension
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    skewAdjointRealCongruenceTransportedFormElementaryRealBasis F hF hdet W =
      skewAdjointScalarExtensionBasis (K := ℝ)
        (skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceTransportedFormElementaryRationalBasis
          F hF hdet W) := by
  apply DFunLike.ext _ _
  intro q
  apply Subtype.ext
  rw [skewAdjointRealCongruenceTransportedFormElementaryRealBasis,
    Module.Basis.map_apply]
  change
    ((skewAdjointRealCongruenceContinuousLinearEquiv F W
        (skewAdjointFormElementaryRealBasis F hF hdet q) :
      skewAdjointMatricesLieSubalgebra
        ((skewAdjointCongruenceForm F W).map (algebraMap ℚ ℝ))) :
      Matrix (Fin n) (Fin n) ℝ) = _
  rw [
    PositiveDefiniteIntegralLattice.coe_skewAdjointRealCongruenceContinuousLinearEquiv_apply,
    coe_skewAdjointFormElementaryRealBasis_apply,
    coe_skewAdjointScalarExtensionBasis_apply,
    skewAdjointCongruenceTransportedFormElementaryRationalBasis,
    Module.Basis.map_apply,
    coe_skewAdjointCongruenceLinearEquiv_apply,
    coe_skewAdjointFormElementaryRationalBasis_apply]
  simp only [PositiveDefiniteIntegralLattice.coe_rationalMatrixUnitReal]
  rw [Matrix.GeneralLinearGroup.coe_inv]
  simp only [Matrix.map_mul]

/-- The signed direct real elementary residual is the real cast of its
rational counterpart, hence the expected determinant power. -/
theorem skewAdjointFormElementaryRealBasis_det_congruenceTransported
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    (skewAdjointFormElementaryRealBasis
        (skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).det
      (skewAdjointRealCongruenceTransportedFormElementaryRealBasis
        F hF hdet W) =
      (((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ) ^ (n - 1) := by
  let F' := skewAdjointCongruenceForm F W
  let A := skewAdjointFormElementaryRationalBasis
    F' (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let B := skewAdjointCongruenceTransportedFormElementaryRationalBasis
    F hF hdet W
  have h := skewAdjointScalarExtensionBasis_det_apply
    (K := ℝ) F' A B
  have hA : skewAdjointScalarExtensionBasis (K := ℝ) F' A =
      skewAdjointFormElementaryRealBasis
        F' (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W) := rfl
  have hB : (fun q => skewAdjointScalarExtensionEquiv (K := ℝ) F'
        (1 ⊗ₜ[ℚ] B q)) =
      skewAdjointRealCongruenceTransportedFormElementaryRealBasis
        F hF hdet W := by
    funext q
    rw [skewAdjointRealCongruenceTransportedFormElementaryRealBasis_eq_scalarExtension]
    apply Subtype.ext
    rw [coe_skewAdjointScalarExtensionEquiv_tmul,
      coe_skewAdjointScalarExtensionBasis_apply]
    simp only [one_smul]
    rfl
  rw [hA, hB] at h
  rw [skewAdjointFormElementaryRationalBasis_det_congruenceTransported]
    at h
  simpa only [map_pow, Rat.cast_ofNat, Rat.cast_natCast] using h

/-- The source strict-pair reindexing followed by the literal target tangent
dimension cast used in the retained real congruence determinant. -/
def skewAdjointRealCongruenceSourceElementaryIndexEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    StrictUpperPair n ≃
      Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (skewAdjointCongruenceForm F W))) :=
  (skewAdjointFormElementaryIndexEquiv F hF hdet).trans
    (Fin.castOrderIso
      (finrank_skewAdjoint_eq_of_real_linearEquiv F
        (skewAdjointCongruenceForm F W)
        (skewAdjointRealCongruenceContinuousLinearEquiv F W)))

/-- The retained transported real `Fin` basis is the directly indexed
transported basis reindexed by the exact source equivalence and target
dimension cast. -/
theorem
    skewAdjointRealCongruenceTransportedFormElementaryFinBasis_eq_reindex
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    skewAdjointRealCongruenceTransportedFormElementaryFinBasis F hF hdet W =
      (skewAdjointRealCongruenceTransportedFormElementaryRealBasis
        F hF hdet W).reindex
          (skewAdjointRealCongruenceSourceElementaryIndexEquiv
            F hF hdet W) := by
  rw [skewAdjointRealCongruenceTransportedFormElementaryFinBasis,
    skewAdjointRealLinearEquivSourceFormElementaryBasis,
    skewAdjointFormElementaryRealFinBasis_eq_reindex]
  apply DFunLike.ext _ _
  intro j
  rw [Module.Basis.map_apply]
  let E := (skewAdjointRealCongruenceContinuousLinearEquiv F W).toLinearEquiv
  let b := skewAdjointFormElementaryRealBasis F hF hdet
  let e := skewAdjointFormElementaryIndexEquiv F hF hdet
  let c := Fin.castOrderIso
    (finrank_skewAdjoint_eq_of_real_linearEquiv F
      (skewAdjointCongruenceForm F W)
      (skewAdjointRealCongruenceContinuousLinearEquiv F W))
  let C := skewAdjointRealCongruenceTransportedFormElementaryRealBasis
    F hF hdet W
  change E (((b.reindex e).reindex c) j) =
    (C.reindex (e.trans c)) j
  rw [C.reindex_apply (e.trans c) j]
  change E (((b.reindex e).reindex c) j) = E (b ((e.trans c).symm j))
  congr 1
  calc
    ((b.reindex e).reindex c) j =
        (b.reindex e) (c.symm j) := Module.Basis.reindex_apply _ _ _
    _ = b (e.symm (c.symm j)) := Module.Basis.reindex_apply _ _ _
    _ = b ((e.trans c).symm j) := rfl

/-- The signed permutation determinant comparing the independently selected
target form-elementary reindexing with the source reindexing followed by the
literal target-dimension cast. -/
def skewAdjointRealCongruenceElementaryReindexDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) : ℝ :=
  ((skewAdjointFormElementaryRealBasis
      (skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).reindex
    (skewAdjointFormElementaryIndexEquiv
      (skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))).det
  ((skewAdjointFormElementaryRealBasis
      (skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).reindex
    (skewAdjointRealCongruenceSourceElementaryIndexEquiv F hF hdet W))

private theorem basis_det_reindex_both
    {K ι ι' M : Type*} [Field K]
    [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    [AddCommGroup M] [Module K M]
    (b b' : Module.Basis ι K M) (e : ι ≃ ι') :
    (b.reindex e).det (b'.reindex e) = b.det b' := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  have hmatrix :
      (b.reindex e).toMatrix (b'.reindex e) =
        Matrix.reindex e e (b.toMatrix b') := by
    ext i j
    simp [Module.Basis.toMatrix_apply, Matrix.reindex_apply]
  rw [hmatrix, Matrix.det_reindex_self]

private theorem basis_abs_det_reindex_reindex
    {ι ι' M : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    [AddCommGroup M] [Module ℝ M]
    (b : Module.Basis ι ℝ M) (e e' : ι ≃ ι') :
    |(b.reindex e).det (b.reindex e')| = 1 := by
  rw [Module.Basis.det_apply]
  have hmatrix :
      (b.reindex e).toMatrix (b.reindex e') =
        (b.toMatrix b).submatrix e.symm e'.symm := by
    ext i j
    simp [Module.Basis.toMatrix_apply]
    by_cases h : i = e (e'.symm j)
    · subst i
      simp [Matrix.one_apply]
    · have h' : e.symm i ≠ e'.symm j := by
        intro hij
        apply h
        rw [← hij, e.apply_symm_apply]
      simp [h, h']
  rw [hmatrix, Matrix.abs_det_submatrix_equiv_equiv,
    Module.Basis.toMatrix_self, Matrix.det_one, abs_one]

/-- The independent finite reindexings contribute only the retained signed
permutation determinant, whose absolute value is one. -/
theorem abs_skewAdjointRealCongruenceElementaryReindexDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    |skewAdjointRealCongruenceElementaryReindexDetScalar F hF hdet W| = 1 := by
  exact basis_abs_det_reindex_reindex
    (skewAdjointFormElementaryRealBasis
      (skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (skewAdjointFormElementaryIndexEquiv
      (skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (skewAdjointRealCongruenceSourceElementaryIndexEquiv F hF hdet W)

/-- The exact signed retained residual is the finite-reindexing sign times
the direct rational congruence determinant power. -/
theorem skewAdjointRealCongruenceFormElementaryDetScalar_eq_reindex_mul_det_pow
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W =
      skewAdjointRealCongruenceElementaryReindexDetScalar F hF hdet W *
        (((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ) ^ (n - 1) := by
  let D := skewAdjointFormElementaryRealBasis
    (skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let eT := skewAdjointFormElementaryIndexEquiv
    (skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let eS := skewAdjointRealCongruenceSourceElementaryIndexEquiv F hF hdet W
  let C := skewAdjointRealCongruenceTransportedFormElementaryRealBasis
    F hF hdet W
  let A := D.reindex eT
  let B := D.reindex eS
  let C' := C.reindex eS
  have hABC := Module.Basis.det_mul_det A B C'
  have hBC : B.det C' =
      (((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ) ^ (n - 1) := by
    rw [show B.det C' = D.det C by
      exact basis_det_reindex_both _ _ _]
    exact skewAdjointFormElementaryRealBasis_det_congruenceTransported
      F hF hdet W
  rw [skewAdjointRealCongruenceFormElementaryDetScalar,
    skewAdjointFormElementaryRealFinBasis_eq_reindex,
    skewAdjointRealCongruenceTransportedFormElementaryFinBasis_eq_reindex]
  change A.det C' = _
  calc
    A.det C' = A.det B * B.det C' := hABC.symm
    _ = skewAdjointRealCongruenceElementaryReindexDetScalar F hF hdet W *
        (((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ) ^
          (n - 1) := by rw [hBC]; rfl

/-- The real rational-congruence elementary residual has absolute value
`|det W|^(n-1)`; the independent finite reindexings remove only a sign. -/
theorem abs_skewAdjointRealCongruenceFormElementaryDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    |skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W| =
      |(((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ)| ^ (n - 1) := by
  rw [skewAdjointRealCongruenceFormElementaryDetScalar_eq_reindex_mul_det_pow,
    abs_mul, abs_skewAdjointRealCongruenceElementaryReindexDetScalar,
    one_mul, abs_pow]

end Matrix
