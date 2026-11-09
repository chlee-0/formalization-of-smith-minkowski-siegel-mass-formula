import SMSFormula.SkewAdjointRealDeterminantComposition
import SMSFormula.StrictUpperPairProduct

/-!
# The positive-diagonal elementary tangent residual

Square-root scaling from a positive rational diagonal form to the identity
acts diagonally on the form-adapted elementary tangent basis indexed by
`Matrix.StrictUpperPair`.  This file computes that diagonal determinant and
then compares it with the independently reindexed finite bases used by
`positiveDiagonalSkewAdjointFormElementaryDetScalar`.

The signed comparison retains the determinant of the resulting permutation.
Only its absolute value is discarded.
-/

noncomputable section

set_option maxRecDepth 2000

open scoped Matrix BigOperators
open PositiveDefiniteIntegralLattice

namespace Matrix

variable {n : ℕ}

/-- The form-adapted elementary basis, indexed directly by strict upper
pairs, after scalar extension from the rationals to the reals. -/
def skewAdjointFormElementaryRealBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Module.Basis (StrictUpperPair n) ℝ
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))) :=
  skewAdjointScalarExtensionBasis (K := ℝ) F
    (skewAdjointFormElementaryRationalBasis F hF hdet)

/-- Ambient matrix formula for the directly indexed real form-elementary
basis. -/
@[simp]
theorem coe_skewAdjointFormElementaryRealBasis_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (q : StrictUpperPair n) :
    (skewAdjointFormElementaryRealBasis F hF hdet q :
        Matrix (Fin n) (Fin n) ℝ) =
      (F⁻¹ * (Matrix.single q.1.1 q.1.2 1 -
        Matrix.single q.1.2 q.1.1 1)).map (algebraMap ℚ ℝ) := by
  rw [skewAdjointFormElementaryRealBasis,
    coe_skewAdjointScalarExtensionBasis_apply,
    coe_skewAdjointFormElementaryRationalBasis_apply]

/-- The identity-form elementary basis, still directly indexed by strict
upper pairs, after scalar extension to the reals. -/
def identitySpecialOrthogonalElementaryRealBasis (n : ℕ) :
    Module.Basis (StrictUpperPair n) ℝ
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  skewAdjointScalarExtensionBasis (K := ℝ)
    (1 : Matrix (Fin n) (Fin n) ℚ)
    (PositiveDefiniteIntegralLattice.identitySpecialOrthogonalElementaryRationalBasis n)

/-- The directly indexed real identity basis consists literally of the
matrices `E i j - E j i`. -/
@[simp]
theorem coe_identitySpecialOrthogonalElementaryRealBasis_apply
    (n : ℕ) (q : StrictUpperPair n) :
    (identitySpecialOrthogonalElementaryRealBasis n q :
        Matrix (Fin n) (Fin n) ℝ) =
      Matrix.single q.1.1 q.1.2 1 -
        Matrix.single q.1.2 q.1.1 1 := by
  rw [identitySpecialOrthogonalElementaryRealBasis,
    coe_skewAdjointScalarExtensionBasis_apply,
    PositiveDefiniteIntegralLattice.coe_identitySpecialOrthogonalElementaryRationalBasis_apply]
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.single_apply]
  by_cases h₁ : q.1.1 = i ∧ q.1.2 = j <;>
    by_cases h₂ : q.1.2 = i ∧ q.1.1 = j <;>
      simp [h₁, h₂]
  all_goals norm_cast

/-- At the identity form, the general form-elementary basis agrees with the
direct identity elementary basis before either is finitely reindexed. -/
theorem skewAdjointFormElementaryRealBasis_one_eq_identity (n : ℕ) :
    skewAdjointFormElementaryRealBasis
        (1 : Matrix (Fin n) (Fin n) ℚ) (by simp) (by simp) =
      identitySpecialOrthogonalElementaryRealBasis n := by
  apply DFunLike.ext _ _
  intro q
  apply Subtype.ext
  rw [coe_skewAdjointFormElementaryRealBasis_apply,
    coe_identitySpecialOrthogonalElementaryRealBasis_apply]
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.single_apply]
  by_cases h₁ : q.1.1 = i ∧ q.1.2 = j <;>
    by_cases h₂ : q.1.2 = i ∧ q.1.1 = j <;>
      simp [h₁, h₂, Matrix.single_apply]
  all_goals norm_cast

/-- The positive pairwise multiplier occurring under inverse-square-root
diagonal scaling. -/
def positiveDiagonalSkewAdjointElementaryPairMultiplier
    (d : Fin n → ℚ) (q : StrictUpperPair n) : ℝ :=
  (Real.sqrt (d q.1.1 : ℝ) * Real.sqrt (d q.1.2 : ℝ))⁻¹

/-- Square-root scaling sends each diagonal-form elementary tangent vector
to the corresponding identity-form vector times the literal pairwise
inverse-square-root multiplier. -/
theorem positiveDiagonalSkewAdjointContinuousLinearEquiv_formElementary_apply
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) (q : StrictUpperPair n) :
    positiveDiagonalSkewAdjointContinuousLinearEquiv d hd
        (skewAdjointFormElementaryRealBasis
          (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
          (positiveDiagonalForm_det_ne_zero d hd) q) =
      positiveDiagonalSkewAdjointElementaryPairMultiplier d q •
        identitySpecialOrthogonalElementaryRealBasis n q := by
  have hinvScaling (k : Fin n) :
      Ring.inverse (positiveDiagonalRealScalingEntries d) k =
        (positiveDiagonalRealScalingEntries d k)⁻¹ := by
    have hu : IsUnit (positiveDiagonalRealScalingEntries d) :=
      Pi.isUnit_iff.mpr fun i =>
        isUnit_iff_ne_zero.mpr
          (positiveDiagonalRealScalingEntries_ne_zero d hd i)
    rw [Ring.inverse_of_isUnit hu, IsUnit.val_inv_apply]
    rw [Units.val_inv_eq_inv_val]
    rw [(hu.apply k).unit_spec]
  have hinvDiagonal (k : Fin n) :
      Ring.inverse d k = (d k)⁻¹ := by
    have hu : IsUnit d :=
      Pi.isUnit_iff.mpr fun i =>
        isUnit_iff_ne_zero.mpr (ne_of_gt (hd i))
    rw [Ring.inverse_of_isUnit hu, IsUnit.val_inv_apply]
    rw [Units.val_inv_eq_inv_val]
    rw [(hu.apply k).unit_spec]
  have hroot (k : Fin n) :
      Ring.inverse (positiveDiagonalRealScalingEntries d) k *
          (algebraMap ℚ ℝ) (Ring.inverse d k) =
        (Real.sqrt (d k : ℝ))⁻¹ := by
    have hk : 0 < (d k : ℝ) := by exact_mod_cast hd k
    have hsqrt : Real.sqrt (d k : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hk
    rw [hinvScaling, hinvDiagonal, map_inv₀]
    simp only [positiveDiagonalRealScalingEntries, inv_inv]
    change Real.sqrt (d k : ℝ) * ((d k : ℝ)⁻¹) = _
    have hsqrt_sq :
        Real.sqrt (d k : ℝ) * Real.sqrt (d k : ℝ) = (d k : ℝ) := by
      simpa [pow_two] using Real.sq_sqrt hk.le
    rw [show ((d k : ℝ))⁻¹ =
        (Real.sqrt (d k : ℝ) * Real.sqrt (d k : ℝ))⁻¹ by
          rw [hsqrt_sq]]
    field_simp
  apply Subtype.ext
  ext i j
  simp only [coe_positiveDiagonalSkewAdjointContinuousLinearEquiv_apply,
    coe_skewAdjointFormElementaryRealBasis_apply,
    coe_positiveDiagonalRealScalingUnit,
    positiveDiagonalRealScalingMatrix, Matrix.inv_diagonal,
    Matrix.map_mul]
  rw [Matrix.diagonal_map (map_zero (algebraMap ℚ ℝ))]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hfwd : q.1.1 = i ∧ q.1.2 = j
  · obtain ⟨rfl, rfl⟩ := hfwd
    rw [← mul_assoc, hroot]
    simp [positiveDiagonalSkewAdjointElementaryPairMultiplier,
      positiveDiagonalRealScalingEntries, ne_of_lt q.2]
    ring
  by_cases hrev : q.1.2 = i ∧ q.1.1 = j
  · obtain ⟨rfl, rfl⟩ := hrev
    rw [← mul_assoc, hroot]
    simp [positiveDiagonalSkewAdjointElementaryPairMultiplier,
      positiveDiagonalRealScalingEntries, ne_of_lt q.2]
  simp [hfwd, hrev,
    positiveDiagonalSkewAdjointElementaryPairMultiplier,
    positiveDiagonalRealScalingEntries]

/-- The directly indexed diagonal-form elementary basis transported by
positive square-root scaling to the identity tangent space. -/
def positiveDiagonalSkewAdjointTransportedFormElementaryRealBasis
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    Module.Basis (StrictUpperPair n) ℝ
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointFormElementaryRealBasis
      (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
      (positiveDiagonalForm_det_ne_zero d hd)).map
    (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd).toLinearEquiv

/-- The transported directly indexed basis vector is the matching identity
elementary vector multiplied by its pairwise inverse-square-root scale. -/
@[simp]
theorem positiveDiagonalSkewAdjointTransportedFormElementaryRealBasis_apply
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (q : StrictUpperPair n) :
    positiveDiagonalSkewAdjointTransportedFormElementaryRealBasis d hd q =
      positiveDiagonalSkewAdjointElementaryPairMultiplier d q •
        identitySpecialOrthogonalElementaryRealBasis n q := by
  exact
    positiveDiagonalSkewAdjointContinuousLinearEquiv_formElementary_apply
      d hd q

/-- The strict-upper coordinate endomorphism of the transported elementary
basis. -/
def positiveDiagonalSkewAdjointElementaryCoordinateEndomorphism
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    (StrictUpperPair n → ℝ) →ₗ[ℝ] (StrictUpperPair n → ℝ) :=
  (identitySpecialOrthogonalElementaryRealBasis n).equivFun.toLinearMap.comp <|
    (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd).toLinearMap.comp <|
      (skewAdjointFormElementaryRealBasis
        (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
        (positiveDiagonalForm_det_ne_zero d hd)).equivFun.symm.toLinearMap

/-- The coordinate endomorphism acts diagonally on the canonical function
basis. -/
@[simp]
theorem positiveDiagonalSkewAdjointElementaryCoordinateEndomorphism_basisFun
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (q : StrictUpperPair n) :
    positiveDiagonalSkewAdjointElementaryCoordinateEndomorphism d hd
        (Pi.basisFun ℝ (StrictUpperPair n) q) =
      positiveDiagonalSkewAdjointElementaryPairMultiplier d q •
        Pi.basisFun ℝ (StrictUpperPair n) q := by
  change
    (identitySpecialOrthogonalElementaryRealBasis n).equivFun
        (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd
          ((skewAdjointFormElementaryRealBasis
            (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
            (positiveDiagonalForm_det_ne_zero d hd)).equivFun.symm
              (Pi.basisFun ℝ (StrictUpperPair n) q))) = _
  rw [show
      (skewAdjointFormElementaryRealBasis
        (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
        (positiveDiagonalForm_det_ne_zero d hd)).equivFun.symm
          (Pi.basisFun ℝ (StrictUpperPair n) q) =
        skewAdjointFormElementaryRealBasis
          (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
          (positiveDiagonalForm_det_ne_zero d hd) q by simp]
  rw [positiveDiagonalSkewAdjointContinuousLinearEquiv_formElementary_apply]
  simp only [LinearEquiv.map_smul, Module.Basis.equivFun_apply,
    Module.Basis.repr_self]
  ext r
  by_cases h : r = q
  · subst r
    simp
  · simp [h]

/-- The coordinate matrix of positive diagonal elementary scaling is the
literal diagonal of pairwise inverse-square-root multipliers. -/
theorem toMatrix_positiveDiagonalSkewAdjointElementaryCoordinateEndomorphism
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    LinearMap.toMatrix (Pi.basisFun ℝ (StrictUpperPair n))
        (Pi.basisFun ℝ (StrictUpperPair n))
        (positiveDiagonalSkewAdjointElementaryCoordinateEndomorphism d hd) =
      Matrix.diagonal
        (positiveDiagonalSkewAdjointElementaryPairMultiplier d) := by
  ext i j
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr,
    positiveDiagonalSkewAdjointElementaryCoordinateEndomorphism_basisFun]
  by_cases hij : i = j
  · subst i
    rw [Matrix.diagonal_apply_eq]
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    simp [hij]

/-- The determinant of the strict-upper coordinate endomorphism is the
unsimplified product of its pairwise multipliers. -/
theorem positiveDiagonalSkewAdjointElementaryCoordinateEndomorphism_det
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    LinearMap.det
        (positiveDiagonalSkewAdjointElementaryCoordinateEndomorphism d hd) =
      ∏ q : StrictUpperPair n,
        positiveDiagonalSkewAdjointElementaryPairMultiplier d q := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (StrictUpperPair n)),
    toMatrix_positiveDiagonalSkewAdjointElementaryCoordinateEndomorphism,
    Matrix.det_diagonal]

/-- Before finite reindexing, the determinant of the transported basis in
identity elementary coordinates is the product of the literal pairwise
multipliers. -/
theorem identityElementaryRealBasis_det_positiveDiagonalTransported
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    (identitySpecialOrthogonalElementaryRealBasis n).det
        (positiveDiagonalSkewAdjointTransportedFormElementaryRealBasis d hd) =
      ∏ q : StrictUpperPair n,
        positiveDiagonalSkewAdjointElementaryPairMultiplier d q := by
  rw [Module.Basis.det_apply]
  have hmatrix :
      (identitySpecialOrthogonalElementaryRealBasis n).toMatrix
          (positiveDiagonalSkewAdjointTransportedFormElementaryRealBasis d hd) =
        Matrix.diagonal
          (positiveDiagonalSkewAdjointElementaryPairMultiplier d) := by
    ext i j
    rw [Module.Basis.toMatrix_apply,
      positiveDiagonalSkewAdjointTransportedFormElementaryRealBasis_apply]
    by_cases hij : i = j
    · subst i
      rw [Matrix.diagonal_apply_eq]
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp [hij]
  rw [hmatrix, Matrix.det_diagonal]

/-- The pairwise multiplier product has the closed endpoint-product form. -/
theorem prod_positiveDiagonalSkewAdjointElementaryPairMultiplier
    (d : Fin n → ℚ) :
    (∏ q : StrictUpperPair n,
        positiveDiagonalSkewAdjointElementaryPairMultiplier d q) =
      (∏ i : Fin n, (Real.sqrt (d i : ℝ))⁻¹) ^ (n - 1) := by
  rw [← StrictUpperPair.prod_endpoint_mul
    (fun i : Fin n => (Real.sqrt (d i : ℝ))⁻¹)]
  apply Fintype.prod_congr
  intro q
  rw [positiveDiagonalSkewAdjointElementaryPairMultiplier]
  rw [← Ring.inverse_eq_inv,
    Ring.mul_inverse_rev, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
  ring

/-- The strict-upper source index followed by the dimension cast used by the
positive-diagonal determinant. -/
def positiveDiagonalSkewAdjointSourceElementaryIndexEquiv
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    StrictUpperPair n ≃
      Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin n) (Fin n) ℚ))) :=
  (skewAdjointFormElementaryIndexEquiv
      (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
      (positiveDiagonalForm_det_ne_zero d hd)).trans
    (Fin.castOrderIso
      (finrank_skewAdjoint_eq_of_real_linearEquiv
        (Matrix.diagonal d) 1
        (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd)))

/-- Direct scalar extension commutes with the finite reindexing of the
form-elementary basis. -/
theorem skewAdjointFormElementaryRealFinBasis_eq_reindex
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryRealFinBasis F hF hdet =
      (skewAdjointFormElementaryRealBasis F hF hdet).reindex
        (skewAdjointFormElementaryIndexEquiv F hF hdet) := by
  apply DFunLike.ext _ _
  intro j
  apply Subtype.ext
  simp [skewAdjointFormElementaryRealFinBasis,
    skewAdjointFormElementaryRealBasis,
    skewAdjointFormElementaryRationalFinBasis]

/-- The identity elementary real Fin basis is exactly the directly indexed
identity elementary basis reindexed by its independently chosen equivalence. -/
theorem identitySpecialOrthogonalElementaryRealFinBasis_eq_reindex
    (n : ℕ) :
    PositiveDefiniteIntegralLattice.identitySpecialOrthogonalElementaryRealFinBasis n =
      (identitySpecialOrthogonalElementaryRealBasis n).reindex
        (PositiveDefiniteIntegralLattice.identitySpecialOrthogonalElementaryIndexEquiv n) := by
  apply DFunLike.ext _ _
  intro j
  apply Subtype.ext
  simp [PositiveDefiniteIntegralLattice.identitySpecialOrthogonalElementaryRealFinBasis,
    identitySpecialOrthogonalElementaryRealBasis,
    PositiveDefiniteIntegralLattice.identitySpecialOrthogonalElementaryRationalFinBasis]

/-- The transported elementary Fin basis is exactly the directly indexed
transported basis reindexed by the source equivalence followed by the
target-dimension cast. -/
theorem
    positiveDiagonalSkewAdjointTransportedFormElementaryRealFinBasis_eq_reindex
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    positiveDiagonalSkewAdjointTransportedFormElementaryRealFinBasis d hd =
      (positiveDiagonalSkewAdjointTransportedFormElementaryRealBasis d hd).reindex
        (positiveDiagonalSkewAdjointSourceElementaryIndexEquiv d hd) := by
  rw [positiveDiagonalSkewAdjointTransportedFormElementaryRealFinBasis,
    skewAdjointRealLinearEquivSourceFormElementaryBasis,
    skewAdjointFormElementaryRealFinBasis_eq_reindex]
  apply DFunLike.ext _ _
  intro j
  simp only [Module.Basis.map_apply, Module.Basis.reindex_apply]
  simp only [positiveDiagonalSkewAdjointTransportedFormElementaryRealBasis,
    Module.Basis.map_apply]
  congr 1

/-- The signed permutation determinant comparing the independently selected
identity and diagonal-form finite reindexings. -/
def positiveDiagonalSkewAdjointElementaryReindexDetScalar
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) : ℝ :=
  ((identitySpecialOrthogonalElementaryRealBasis n).reindex
      (PositiveDefiniteIntegralLattice.identitySpecialOrthogonalElementaryIndexEquiv n)).det
    ((identitySpecialOrthogonalElementaryRealBasis n).reindex
      (positiveDiagonalSkewAdjointSourceElementaryIndexEquiv d hd))

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

/-- The independently selected reindexings contribute only the signed
permutation determinant, whose absolute value is one. -/
theorem abs_positiveDiagonalSkewAdjointElementaryReindexDetScalar
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    |positiveDiagonalSkewAdjointElementaryReindexDetScalar d hd| = 1 := by
  exact basis_abs_det_reindex_reindex
    (identitySpecialOrthogonalElementaryRealBasis n)
    (PositiveDefiniteIntegralLattice.identitySpecialOrthogonalElementaryIndexEquiv n)
    (positiveDiagonalSkewAdjointSourceElementaryIndexEquiv d hd)

/-- The exact signed residual is the finite-reindexing sign times the
canonical strict-upper diagonal determinant. -/
theorem positiveDiagonalSkewAdjointFormElementaryDetScalar_eq_reindex_mul_prod
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    positiveDiagonalSkewAdjointFormElementaryDetScalar d hd =
      positiveDiagonalSkewAdjointElementaryReindexDetScalar d hd *
        ∏ q : StrictUpperPair n,
          positiveDiagonalSkewAdjointElementaryPairMultiplier d q := by
  let A := (identitySpecialOrthogonalElementaryRealBasis n).reindex
    (PositiveDefiniteIntegralLattice.identitySpecialOrthogonalElementaryIndexEquiv n)
  let B := (identitySpecialOrthogonalElementaryRealBasis n).reindex
    (positiveDiagonalSkewAdjointSourceElementaryIndexEquiv d hd)
  let C := (positiveDiagonalSkewAdjointTransportedFormElementaryRealBasis
    d hd).reindex
      (positiveDiagonalSkewAdjointSourceElementaryIndexEquiv d hd)
  have hABC := Module.Basis.det_mul_det A B C
  have hBC : B.det C =
      ∏ q : StrictUpperPair n,
        positiveDiagonalSkewAdjointElementaryPairMultiplier d q := by
    rw [show B.det C =
        (identitySpecialOrthogonalElementaryRealBasis n).det
          (positiveDiagonalSkewAdjointTransportedFormElementaryRealBasis
            d hd) by
      exact basis_det_reindex_both _ _ _]
    exact identityElementaryRealBasis_det_positiveDiagonalTransported d hd
  rw [positiveDiagonalSkewAdjointFormElementaryDetScalar,
    identitySpecialOrthogonalElementaryRealFinBasis_eq_reindex,
    positiveDiagonalSkewAdjointTransportedFormElementaryRealFinBasis_eq_reindex]
  change A.det C = _
  calc
    A.det C = A.det B * B.det C := hABC.symm
    _ = positiveDiagonalSkewAdjointElementaryReindexDetScalar d hd *
        ∏ q : StrictUpperPair n,
          positiveDiagonalSkewAdjointElementaryPairMultiplier d q := by
      rw [hBC]
      rfl

/-- The absolute residual is the positive product of pairwise
inverse-square-root multipliers; the independent finite reindexings have
removed only a sign. -/
theorem abs_positiveDiagonalSkewAdjointFormElementaryDetScalar
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    |positiveDiagonalSkewAdjointFormElementaryDetScalar d hd| =
      ∏ q : StrictUpperPair n,
        (Real.sqrt (d q.1.1 : ℝ) *
          Real.sqrt (d q.1.2 : ℝ))⁻¹ := by
  rw [positiveDiagonalSkewAdjointFormElementaryDetScalar_eq_reindex_mul_prod,
    abs_mul, abs_positiveDiagonalSkewAdjointElementaryReindexDetScalar,
    one_mul]
  rw [abs_of_nonneg]
  · rfl
  · apply Finset.prod_nonneg
    intro q hq
    exact inv_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Closed endpoint-product form of the absolute positive-diagonal
elementary residual. -/
theorem abs_positiveDiagonalSkewAdjointFormElementaryDetScalar_closed
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    |positiveDiagonalSkewAdjointFormElementaryDetScalar d hd| =
      (∏ i : Fin n, (Real.sqrt (d i : ℝ))⁻¹) ^ (n - 1) := by
  rw [abs_positiveDiagonalSkewAdjointFormElementaryDetScalar,
    ← prod_positiveDiagonalSkewAdjointElementaryPairMultiplier]
  rfl

end Matrix
