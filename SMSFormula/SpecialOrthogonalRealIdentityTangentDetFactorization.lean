import SMSFormula.SpecialOrthogonalRealIdentityElementaryTangentSplit

/-!
# Factorization of the identity tangent split determinant

This file compares the explicit elementary tangent split with the
fixed rational tangent bases. Scalar extension identifies the elementary
rational basis with the direct real matrix-unit basis. The elementary split
has determinant of absolute value one; the only possible sign comes from the
independently chosen finite reindexings.

Consequently, the absolute fixed-basis split determinant is the ratio of the
consecutive fixed-to-elementary rational comparison determinants.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

def identitySpecialOrthogonalElementaryLiteralRealFinBasis (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin n) (Fin n) ℚ))))
      ℝ
      (identitySpecialOrthogonalTangent n) :=
  (identitySpecialOrthogonalElementaryRealFinBasis n).map
    (identitySpecialOrthogonalMappedIdentityTangentEquiv n)

def identitySpecialOrthogonalElementaryDirectRealFinBasis (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin n) (Fin n) ℚ))))
      ℝ
      (identitySpecialOrthogonalTangent n) :=
  (identitySpecialOrthogonalElementaryRealBasis n).reindex
    (identitySpecialOrthogonalElementaryIndexEquiv n)

theorem identitySpecialOrthogonalElementaryLiteralRealFinBasis_eq_direct
    (n : ℕ) :
    identitySpecialOrthogonalElementaryLiteralRealFinBasis n =
      identitySpecialOrthogonalElementaryDirectRealFinBasis n := by
  apply DFunLike.ext _ _
  intro j
  apply Subtype.ext
  rw [show
      ((identitySpecialOrthogonalElementaryLiteralRealFinBasis n j :
          identitySpecialOrthogonalTangent n) :
        Matrix (Fin n) (Fin n) ℝ) =
        ((identitySpecialOrthogonalElementaryRealFinBasis n j :
          skewAdjointMatricesLieSubalgebra
            ((1 : Matrix (Fin n) (Fin n) ℚ).map
              (algebraMap ℚ ℝ))) :
          Matrix (Fin n) (Fin n) ℝ) by
        simp [identitySpecialOrthogonalElementaryLiteralRealFinBasis]]
  rw [show
      ((identitySpecialOrthogonalElementaryDirectRealFinBasis n j :
          identitySpecialOrthogonalTangent n) :
        Matrix (Fin n) (Fin n) ℝ) =
        ((identitySpecialOrthogonalElementaryRealBasis n
          ((identitySpecialOrthogonalElementaryIndexEquiv n).symm j) :
            identitySpecialOrthogonalTangent n) :
          Matrix (Fin n) (Fin n) ℝ) by
        simp [identitySpecialOrthogonalElementaryDirectRealFinBasis]]
  change
    ((skewAdjointScalarExtensionBasis (K := ℝ)
      (1 : Matrix (Fin n) (Fin n) ℚ)
      (identitySpecialOrthogonalElementaryRationalFinBasis n) j :
        skewAdjointMatricesLieSubalgebra
          ((1 : Matrix (Fin n) (Fin n) ℚ).map
            (algebraMap ℚ ℝ))) :
      Matrix (Fin n) (Fin n) ℝ) = _
  rw [Matrix.coe_skewAdjointScalarExtensionBasis_apply,
    coe_identitySpecialOrthogonalElementaryRealBasis_apply]
  rw [show
      identitySpecialOrthogonalElementaryRationalFinBasis n j =
        identitySpecialOrthogonalElementaryRationalBasis n
          ((identitySpecialOrthogonalElementaryIndexEquiv n).symm j) by
        simp [identitySpecialOrthogonalElementaryRationalFinBasis]]
  rw [coe_identitySpecialOrthogonalElementaryRationalBasis_apply]
  ext i k
  simp [Matrix.single_apply]
  exact_mod_cast rfl

theorem identitySpecialOrthogonalFixedTangentBasis_det_elementaryDirect
    (n : ℕ) :
    (identitySpecialOrthogonalFixedTangentBasis n).det
        (identitySpecialOrthogonalElementaryDirectRealFinBasis n) =
      (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) := by
  rw [← identitySpecialOrthogonalElementaryLiteralRealFinBasis_eq_direct]
  rw [identitySpecialOrthogonalElementaryLiteralRealFinBasis,
    identitySpecialOrthogonalFixedTangentBasis,
    Module.Basis.det_map]
  convert identitySpecialOrthogonalFixedRealBasis_det_elementary n using 1

private theorem basis_det_prod
    {ι κ M N : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (b b' : Module.Basis ι ℝ M) (c c' : Module.Basis κ ℝ N) :
    (b.prod c).det (b'.prod c') = b.det b' * c.det c' := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply,
    Module.Basis.det_apply]
  have hmatrix :
      (b.prod c).toMatrix (b'.prod c') =
        Matrix.fromBlocks (b.toMatrix b') 0 0 (c.toMatrix c') := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Module.Basis.toMatrix_apply]
  rw [hmatrix, Matrix.det_fromBlocks_zero₂₁]

private theorem basis_det_reindex_both
    {ι ι' M : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    [AddCommGroup M] [Module ℝ M]
    (b b' : Module.Basis ι ℝ M) (e : ι ≃ ι') :
    (b.reindex e).det (b'.reindex e) = b.det b' := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  have hmatrix :
      (b.reindex e).toMatrix (b'.reindex e) =
        Matrix.reindex e e (b.toMatrix b') := by
    ext i j
    simp [Module.Basis.toMatrix_apply, Matrix.reindex_apply]
  rw [hmatrix, Matrix.det_reindex_self]

private theorem basis_det_map_both
    {ι M M' : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module ℝ M]
    [AddCommGroup M'] [Module ℝ M']
    (b b' : Module.Basis ι ℝ M) (e : M ≃ₗ[ℝ] M') :
    (b.map e).det (b'.map e) = b.det b' := by
  rw [Module.Basis.det_map]
  congr 1
  ext i
  simp

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

/-- The elementary product basis, reindexed by the higher-rank fixed
tangent index. -/
def identitySpecialOrthogonalElementaryDirectTangentProductBasis (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))))
      ℝ
      (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
  ((identitySpecialOrthogonalElementaryDirectRealFinBasis n).prod
      (Pi.basisFun ℝ (Fin n))).reindex
    (identitySpecialOrthogonalTangentProductIndexEquiv n)

/-- The higher-rank elementary Fin basis transported through the tangent
split. -/
def identitySpecialOrthogonalElementaryDirectTangentSplitTransportedBasis
    (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))))
      ℝ
      (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
  (identitySpecialOrthogonalElementaryDirectRealFinBasis (n + 1)).map
    (identitySpecialOrthogonalTangentContinuousLinearEquiv n).toLinearEquiv

def identitySpecialOrthogonalElementaryProductFinIndexEquiv (n : ℕ) :
    (Matrix.StrictUpperPair n ⊕ Fin n) ≃
      Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))) :=
  (Equiv.sumCongr (identitySpecialOrthogonalElementaryIndexEquiv n)
    (Equiv.refl (Fin n))).trans
      (identitySpecialOrthogonalTangentProductIndexEquiv n)

def identitySpecialOrthogonalElementarySplitFinIndexEquiv (n : ℕ) :
    (Matrix.StrictUpperPair n ⊕ Fin n) ≃
      Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))) :=
  (Matrix.StrictUpperPair.succEquiv n).symm.trans
    (identitySpecialOrthogonalElementaryIndexEquiv (n + 1))

theorem
    identitySpecialOrthogonalElementaryDirectTangentProductBasis_eq_reindex
    (n : ℕ) :
    identitySpecialOrthogonalElementaryDirectTangentProductBasis n =
      (identitySpecialOrthogonalElementaryTangentProductBasis n).reindex
        (identitySpecialOrthogonalElementaryProductFinIndexEquiv n) := by
  apply DFunLike.ext _ _
  intro j
  cases h :
      (identitySpecialOrthogonalTangentProductIndexEquiv n).symm j with
  | inl k =>
    simp [identitySpecialOrthogonalElementaryDirectTangentProductBasis,
      identitySpecialOrthogonalElementaryDirectRealFinBasis,
      identitySpecialOrthogonalElementaryTangentProductBasis,
      identitySpecialOrthogonalElementaryProductFinIndexEquiv, h]
  | inr i =>
    simp [identitySpecialOrthogonalElementaryDirectTangentProductBasis,
      identitySpecialOrthogonalElementaryDirectRealFinBasis,
      identitySpecialOrthogonalElementaryTangentProductBasis,
      identitySpecialOrthogonalElementaryProductFinIndexEquiv, h]

theorem
    identitySpecialOrthogonalElementaryDirectTangentSplitTransportedBasis_eq_reindex
    (n : ℕ) :
    identitySpecialOrthogonalElementaryDirectTangentSplitTransportedBasis n =
      (identitySpecialOrthogonalElementaryTangentSplitTransportedBasis n).reindex
        (identitySpecialOrthogonalElementarySplitFinIndexEquiv n) := by
  apply DFunLike.ext _ _
  intro j
  simp [identitySpecialOrthogonalElementaryDirectTangentSplitTransportedBasis,
    identitySpecialOrthogonalElementaryDirectRealFinBasis,
    identitySpecialOrthogonalElementaryTangentSplitTransportedBasis,
    identitySpecialOrthogonalElementarySplitFinIndexEquiv]

theorem identitySpecialOrthogonalElementaryDirectSplit_abs_det_eq_one
    (n : ℕ) :
    |(identitySpecialOrthogonalElementaryDirectTangentProductBasis n).det
        (identitySpecialOrthogonalElementaryDirectTangentSplitTransportedBasis n)| =
      1 := by
  rw [
    identitySpecialOrthogonalElementaryDirectTangentProductBasis_eq_reindex,
    identitySpecialOrthogonalElementaryDirectTangentSplitTransportedBasis_eq_reindex,
    identitySpecialOrthogonalElementaryTangentSplitTransportedBasis_eq_product]
  exact basis_abs_det_reindex_reindex
    (identitySpecialOrthogonalElementaryTangentProductBasis n)
    (identitySpecialOrthogonalElementaryProductFinIndexEquiv n)
    (identitySpecialOrthogonalElementarySplitFinIndexEquiv n)

theorem identitySpecialOrthogonalTangentProductBasis_det_elementaryDirect
    (n : ℕ) :
    (identitySpecialOrthogonalTangentProductBasis n).det
        (identitySpecialOrthogonalElementaryDirectTangentProductBasis n) =
      (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) := by
  rw [identitySpecialOrthogonalTangentProductBasis,
    identitySpecialOrthogonalElementaryDirectTangentProductBasis,
    basis_det_reindex_both, basis_det_prod,
    identitySpecialOrthogonalFixedTangentBasis_det_elementaryDirect,
    Module.Basis.det_self, mul_one]

theorem
    identitySpecialOrthogonalTangentSplitTransportedBasis_det_elementaryDirect
    (n : ℕ) :
    (identitySpecialOrthogonalTangentSplitTransportedBasis n).det
        (identitySpecialOrthogonalElementaryDirectTangentSplitTransportedBasis n) =
      (identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ) := by
  rw [identitySpecialOrthogonalTangentSplitTransportedBasis,
    identitySpecialOrthogonalElementaryDirectTangentSplitTransportedBasis,
    basis_det_map_both,
    identitySpecialOrthogonalFixedTangentBasis_det_elementaryDirect]

/-- The absolute fixed-basis split determinant is the ratio of consecutive
rational fixed-to-elementary comparison determinants. -/
theorem abs_identitySpecialOrthogonalTangentSplitDetScalar
    (n : ℕ) :
    |identitySpecialOrthogonalTangentSplitDetScalar n| =
      |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| /
        |(identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ)| := by
  let A := identitySpecialOrthogonalTangentProductBasis n
  let B := identitySpecialOrthogonalElementaryDirectTangentProductBasis n
  let C :=
    identitySpecialOrthogonalElementaryDirectTangentSplitTransportedBasis n
  let D := identitySpecialOrthogonalTangentSplitTransportedBasis n
  have h₁ := Module.Basis.det_mul_det A D C
  have h₂ := Module.Basis.det_mul_det A B C
  have hdet :
      identitySpecialOrthogonalTangentSplitDetScalar n *
          (identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ) =
        (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) *
          B.det C := by
    simpa [A, B, C, D, identitySpecialOrthogonalTangentSplitDetScalar,
      identitySpecialOrthogonalTangentProductBasis_det_elementaryDirect,
      identitySpecialOrthogonalTangentSplitTransportedBasis_det_elementaryDirect]
      using h₁.trans h₂.symm
  have habs :
      |identitySpecialOrthogonalTangentSplitDetScalar n| *
          |(identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ)| =
        |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| := by
    calc
      _ = |identitySpecialOrthogonalTangentSplitDetScalar n *
          (identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ)| :=
        (abs_mul _ _).symm
      _ = |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) *
          B.det C| := congrArg abs hdet
      _ = |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
          |B.det C| := abs_mul _ _
      _ = |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| := by
        rw [show |B.det C| = 1 by
          simpa [B, C] using
            identitySpecialOrthogonalElementaryDirectSplit_abs_det_eq_one n,
          mul_one]
  have hne :
      |(identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ)| ≠
        0 := by
    rw [abs_ne_zero]
    exact_mod_cast
      identitySpecialOrthogonalFixedElementaryDetScalar_ne_zero (n + 1)
  exact (eq_div_iff hne).2 habs

end PositiveDefiniteIntegralLattice
