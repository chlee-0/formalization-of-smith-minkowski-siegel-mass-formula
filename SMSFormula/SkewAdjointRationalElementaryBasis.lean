import SMSFormula.SkewSymmetricMatrixBasis
import SMSFormula.SkewAdjointBaseChange

/-!
# A form-adapted rational basis for skew-adjoint matrices

For a symmetric nonsingular rational form `F`, left multiplication by `F`
identifies `F`-skew-adjoint matrices with skew-symmetric matrices.  Transporting
the elementary skew-symmetric basis through the inverse equivalence gives a
form-adapted rational basis of the `F`-skew-adjoint tangent space.

The determinant comparing this elementary basis with the fixed basis
`Matrix.skewAdjointFinBasis F` is kept as a symbolic nonzero rational scalar.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {n : ℕ}

/-- Left multiplication by a symmetric form sends its skew-adjoint matrices
to skew-symmetric matrices. -/
def skewAdjointRationalToSkewSymmetricLinearMap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) :
    skewAdjointMatricesLieSubalgebra F →ₗ[ℚ]
      skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n) where
  toFun X := ⟨F * (X : Matrix (Fin n) (Fin n) ℚ), by
    have hXker : skewAdjointOperator F
        (X : Matrix (Fin n) (Fin n) ℚ) = 0 := by
      exact LinearMap.mem_ker.mp
        ((mem_ker_skewAdjointOperator_iff F X).mpr X.property)
    have hXskew :
        (X : Matrix (Fin n) (Fin n) ℚ)ᵀ * F =
          -(F * (X : Matrix (Fin n) (Fin n) ℚ)) :=
      eq_neg_of_add_eq_zero_left hXker
    change (F * (X : Matrix (Fin n) (Fin n) ℚ))ᵀ =
      -(F * (X : Matrix (Fin n) (Fin n) ℚ))
    rw [Matrix.transpose_mul, hF.eq, hXskew]⟩
  map_add' X Y := by
    apply Subtype.ext
    simp [Matrix.mul_add]
  map_smul' a X := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_skewAdjointRationalToSkewSymmetricLinearMap_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (X : skewAdjointMatricesLieSubalgebra F) :
    (skewAdjointRationalToSkewSymmetricLinearMap F hF X :
        Matrix (Fin n) (Fin n) ℚ) =
      F * (X : Matrix (Fin n) (Fin n) ℚ) :=
  rfl

/-- Left multiplication by the inverse form sends skew-symmetric matrices
back to skew-adjoint matrices. -/
def skewSymmetricRationalToSkewAdjointLinearMap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n) →ₗ[ℚ]
      skewAdjointMatricesLieSubalgebra F where
  toFun Y := ⟨F⁻¹ * (Y : Matrix (Fin n) (Fin n) ℚ), by
    have hFdet : IsUnit F.det := isUnit_iff_ne_zero.mpr hdet
    apply (mem_ker_skewAdjointOperator_iff F
      (F⁻¹ * (Y : Matrix (Fin n) (Fin n) ℚ))).mp
    rw [LinearMap.mem_ker, skewAdjointOperator_apply, Matrix.transpose_mul,
      Matrix.transpose_nonsing_inv, hF.eq, Y.property]
    calc
      (-(Y : Matrix (Fin n) (Fin n) ℚ)) * F⁻¹ * F +
          F * (F⁻¹ * (Y : Matrix (Fin n) (Fin n) ℚ)) =
        -((Y : Matrix (Fin n) (Fin n) ℚ) * (F⁻¹ * F)) +
          (F * F⁻¹) * (Y : Matrix (Fin n) (Fin n) ℚ) := by
            noncomm_ring
      _ = 0 := by
        rw [Matrix.nonsing_inv_mul F hFdet,
          Matrix.mul_nonsing_inv F hFdet]
        simp⟩
  map_add' Y Z := by
    apply Subtype.ext
    simp [Matrix.mul_add]
  map_smul' a Y := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_skewSymmetricRationalToSkewAdjointLinearMap_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (Y : skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n)) :
    (skewSymmetricRationalToSkewAdjointLinearMap F hF hdet Y :
        Matrix (Fin n) (Fin n) ℚ) =
      F⁻¹ * (Y : Matrix (Fin n) (Fin n) ℚ) :=
  rfl

/-- For a symmetric nonsingular rational form, `X ↦ F X` identifies its
skew-adjoint tangent space with the skew-symmetric matrices. -/
def skewAdjointRationalSkewSymmetricLinearEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointMatricesLieSubalgebra F ≃ₗ[ℚ]
      skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n) := by
  let hFunit : IsUnit F.det := isUnit_iff_ne_zero.mpr hdet
  refine LinearEquiv.ofLinear
    (skewAdjointRationalToSkewSymmetricLinearMap F hF)
    (skewSymmetricRationalToSkewAdjointLinearMap F hF hdet) ?_ ?_
  · apply LinearMap.ext
    intro Y
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.id_apply,
      coe_skewAdjointRationalToSkewSymmetricLinearMap_apply,
      coe_skewSymmetricRationalToSkewAdjointLinearMap_apply]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv F hFunit,
      Matrix.one_mul]
  · apply LinearMap.ext
    intro X
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.id_apply,
      coe_skewAdjointRationalToSkewSymmetricLinearMap_apply,
      coe_skewSymmetricRationalToSkewAdjointLinearMap_apply]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul F hFunit,
      Matrix.one_mul]

@[simp]
theorem coe_skewAdjointRationalSkewSymmetricLinearEquiv_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (X : skewAdjointMatricesLieSubalgebra F) :
    (skewAdjointRationalSkewSymmetricLinearEquiv F hF hdet X :
        Matrix (Fin n) (Fin n) ℚ) =
      F * (X : Matrix (Fin n) (Fin n) ℚ) :=
  rfl

@[simp]
theorem coe_skewAdjointRationalSkewSymmetricLinearEquiv_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (Y : skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n)) :
    ((skewAdjointRationalSkewSymmetricLinearEquiv F hF hdet).symm Y :
        Matrix (Fin n) (Fin n) ℚ) =
      F⁻¹ * (Y : Matrix (Fin n) (Fin n) ℚ) :=
  rfl

/-- The form-adapted elementary rational skew-adjoint basis, indexed by
strict upper-triangular pairs. -/
def skewAdjointFormElementaryRationalBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Module.Basis (StrictUpperPair n) ℚ
      (skewAdjointMatricesLieSubalgebra F) :=
  (skewSymmetricBasis (K := ℚ) (by norm_num)).map
    (skewAdjointRationalSkewSymmetricLinearEquiv F hF hdet).symm

/-- Each form-adapted elementary vector is `F⁻¹ (E i j - E j i)`. -/
@[simp]
theorem coe_skewAdjointFormElementaryRationalBasis_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (q : StrictUpperPair n) :
    ((skewAdjointFormElementaryRationalBasis F hF hdet q :
        skewAdjointMatricesLieSubalgebra F) :
      Matrix (Fin n) (Fin n) ℚ) =
      F⁻¹ * (Matrix.single q.1.1 q.1.2 1 -
        Matrix.single q.1.2 q.1.1 1) := by
  simp [skewAdjointFormElementaryRationalBasis]

theorem card_strictUpperPair_eq_finrank_skewAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Fintype.card (StrictUpperPair n) =
      Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  rw [StrictUpperPair.card]
  calc
    n.choose 2 =
        Module.finrank ℚ
          (skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n)) := by
      symm
      exact finrank_skewSymmetricMatricesSubmodule (K := ℚ) (by norm_num)
    _ = Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) :=
      (skewAdjointRationalSkewSymmetricLinearEquiv F hF hdet).finrank_eq.symm

/-- A fixed reindexing of strict upper pairs by the index of
`skewAdjointFinBasis F`. -/
def skewAdjointFormElementaryIndexEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    StrictUpperPair n ≃
      Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) :=
  Fintype.equivOfCardEq
    (by simpa using
      card_strictUpperPair_eq_finrank_skewAdjoint F hF hdet)

/-- The form-adapted elementary rational basis reindexed to match
`skewAdjointFinBasis F`. -/
def skewAdjointFormElementaryRationalFinBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Module.Basis
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
      ℚ (skewAdjointMatricesLieSubalgebra F) :=
  (skewAdjointFormElementaryRationalBasis F hF hdet).reindex
    (skewAdjointFormElementaryIndexEquiv F hF hdet)

/-- The rational determinant of the form-adapted elementary basis in the
fixed rational skew-adjoint coordinates. -/
def skewAdjointFixedFormElementaryDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) : ℚ :=
  (skewAdjointFinBasis F).det
    (skewAdjointFormElementaryRationalFinBasis F hF hdet)

/-- The fixed/form-adapted rational basis comparison determinant is nonzero. -/
theorem skewAdjointFixedFormElementaryDetScalar_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFixedFormElementaryDetScalar F hF hdet ≠ 0 := by
  rw [skewAdjointFixedFormElementaryDetScalar,
    ← Module.Basis.det_basis
      (skewAdjointFormElementaryRationalFinBasis F hF hdet)
      (skewAdjointFinBasis F),
    ← LinearEquiv.coe_det]
  exact Units.ne_zero _

end Matrix
