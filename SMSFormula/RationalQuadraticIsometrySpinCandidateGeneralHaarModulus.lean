import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralTopology
import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarModulus

/-!
# Tangent modulus under an arbitrary rational quadratic isometry

A supplied rational quadratic isometry conjugates the two native
skew-adjoint tangent spaces even when their coordinate index types are not
definitionally equal.  This file records that linear equivalence and its
determinant in the repository's independently fixed rational tangent bases.

The determinant is nonzero and satisfies the rational product formula.  No
rank identification, local chart, Haar measure, integral structure, raw
normalization certificate, quotient measure, or Tamagawa value is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped BigOperators Matrix ENNReal

namespace RationalQuadraticSpaceMatrix

variable {r s : ℕ}
variable (U : RationalQuadraticSpaceMatrix r)
variable (V : RationalQuadraticSpaceMatrix s)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

/-- A rational quadratic isometry forces equality of the two native
coordinate ranks.  The tangent modulus below does not use this equality to
identify its carriers; it is exposed only for same-rank local chart theorems. -/
theorem rationalIsometry_dimension_eq
    (e : U.quadraticForm.IsometryEquiv V.quadraticForm) : r = s := by
  simpa using LinearEquiv.finrank_eq
    (e : (Fin r → ℚ) ≃ₗ[ℚ] (Fin s → ℚ))

/-- Matrix of a supplied rational quadratic isometry in the native
coordinate bases. -/
abbrev rationalIsometryMatrix : Matrix (Fin s) (Fin r) ℚ :=
  LinearMap.toMatrix' e.toLinearEquiv.toLinearMap

/-- Matrix of the inverse supplied rational quadratic isometry. -/
abbrev rationalIsometryInverseMatrix : Matrix (Fin r) (Fin s) ℚ :=
  LinearMap.toMatrix' e.symm.toLinearEquiv.toLinearMap

theorem rationalIsometryMatrix_mul_inverseMatrix :
    rationalIsometryMatrix U V e * rationalIsometryInverseMatrix U V e = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have hcomp :
      e.toLinearEquiv.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap =
        LinearMap.id := by
    apply LinearMap.ext
    intro y
    exact e.apply_symm_apply y
  rw [hcomp, LinearMap.toMatrix'_id]

theorem rationalIsometryInverseMatrix_mul_matrix :
    rationalIsometryInverseMatrix U V e * rationalIsometryMatrix U V e = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have hcomp :
      e.symm.toLinearEquiv.toLinearMap.comp e.toLinearEquiv.toLinearMap =
        LinearMap.id := by
    apply LinearMap.ext
    intro y
    exact e.symm_apply_apply y
  rw [hcomp, LinearMap.toMatrix'_id]

/-- Exact rectangular form congruence attached to the supplied isometry. -/
theorem rationalIsometryMatrix_form_congruence :
    (rationalIsometryMatrix U V e)ᵀ * V.pairingMatrix *
        rationalIsometryMatrix U V e = U.pairingMatrix := by
  have hcomp :
      V.nativeRationalQuadraticForm.comp e.toLinearEquiv.toLinearMap =
        U.nativeRationalQuadraticForm := by
    apply QuadraticMap.ext
    intro y
    exact e.map_app y
  have hmatrix := congrArg QuadraticForm.toMatrix' hcomp
  rw [QuadraticForm.toMatrix'_comp, V.quadraticForm_toMatrix',
    U.quadraticForm_toMatrix'] at hmatrix
  exact hmatrix

/-- Conjugation through an arbitrary supplied rational quadratic isometry
transports the full skew-adjoint tangent space across the native coordinate
types. -/
def rationalIsometrySkewAdjointLinearEquiv :
    skewAdjointMatricesLieSubalgebra U.pairingMatrix ≃ₗ[ℚ]
      skewAdjointMatricesLieSubalgebra V.pairingMatrix where
  toFun X := by
    let M := rationalIsometryMatrix U V e
    let N := rationalIsometryInverseMatrix U V e
    refine ⟨M * X.1 * N, ?_⟩
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
    have hX := X.property
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule] at hX
    have hMN : M * N = 1 :=
      rationalIsometryMatrix_mul_inverseMatrix U V e
    have hform : Mᵀ * V.pairingMatrix * M = U.pairingMatrix :=
      rationalIsometryMatrix_form_congruence U V e
    have hleft : Mᵀ * V.pairingMatrix = U.pairingMatrix * N := by
      calc
        Mᵀ * V.pairingMatrix = (Mᵀ * V.pairingMatrix) *
            (1 : Matrix (Fin s) (Fin s) ℚ) := by rw [Matrix.mul_one]
        _ = (Mᵀ * V.pairingMatrix) * (M * N) := by rw [hMN]
        _ = (Mᵀ * V.pairingMatrix * M) * N := by
          simp only [Matrix.mul_assoc]
        _ = U.pairingMatrix * N := by rw [hform]
    have hright : Nᵀ * U.pairingMatrix = V.pairingMatrix * M := by
      calc
        Nᵀ * U.pairingMatrix = Nᵀ * (Mᵀ * V.pairingMatrix * M) := by rw [hform]
        _ = (Nᵀ * Mᵀ) * V.pairingMatrix * M := by
          simp only [Matrix.mul_assoc]
        _ = (M * N)ᵀ * V.pairingMatrix * M := by rw [Matrix.transpose_mul]
        _ = V.pairingMatrix * M := by rw [hMN, Matrix.transpose_one]; simp
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_neg] at hX ⊢
    calc
      (M * X.1 * N)ᵀ * V.pairingMatrix =
          (Nᵀ * (X.1ᵀ * Mᵀ)) * V.pairingMatrix := by
            rw [Matrix.transpose_mul, Matrix.transpose_mul]
      _ = Nᵀ * X.1ᵀ * (Mᵀ * V.pairingMatrix) := by
            simp only [Matrix.mul_assoc]
      _ = Nᵀ * X.1ᵀ * (U.pairingMatrix * N) := by rw [hleft]
      _ = Nᵀ * (X.1ᵀ * U.pairingMatrix) * N := by
            simp only [Matrix.mul_assoc]
      _ = Nᵀ * (-(U.pairingMatrix * X.1)) * N := by rw [hX]
      _ = -((Nᵀ * U.pairingMatrix) * X.1 * N) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -((V.pairingMatrix * M) * X.1 * N) := by rw [hright]
      _ = -(V.pairingMatrix * (M * X.1 * N)) := by
            simp only [Matrix.mul_assoc]
  invFun Y := by
    let M := rationalIsometryMatrix U V e
    let N := rationalIsometryInverseMatrix U V e
    refine ⟨N * Y.1 * M, ?_⟩
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
    have hY := Y.property
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule] at hY
    have hMN : M * N = 1 :=
      rationalIsometryMatrix_mul_inverseMatrix U V e
    have hform : Mᵀ * V.pairingMatrix * M = U.pairingMatrix :=
      rationalIsometryMatrix_form_congruence U V e
    have hleft : Mᵀ * V.pairingMatrix = U.pairingMatrix * N := by
      calc
        Mᵀ * V.pairingMatrix = (Mᵀ * V.pairingMatrix) *
            (1 : Matrix (Fin s) (Fin s) ℚ) := by rw [Matrix.mul_one]
        _ = (Mᵀ * V.pairingMatrix) * (M * N) := by rw [hMN]
        _ = (Mᵀ * V.pairingMatrix * M) * N := by
          simp only [Matrix.mul_assoc]
        _ = U.pairingMatrix * N := by rw [hform]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_neg] at hY ⊢
    calc
      (N * Y.1 * M)ᵀ * U.pairingMatrix =
          (Mᵀ * (Y.1ᵀ * Nᵀ)) * U.pairingMatrix := by
            rw [Matrix.transpose_mul, Matrix.transpose_mul]
      _ = Mᵀ * Y.1ᵀ * (Nᵀ * U.pairingMatrix) := by
            simp only [Matrix.mul_assoc]
      _ = Mᵀ * Y.1ᵀ * (V.pairingMatrix * M) := by
            have hright : Nᵀ * U.pairingMatrix = V.pairingMatrix * M := by
              calc
                Nᵀ * U.pairingMatrix =
                    Nᵀ * (Mᵀ * V.pairingMatrix * M) := by rw [hform]
                _ = (Nᵀ * Mᵀ) * V.pairingMatrix * M := by
                  simp only [Matrix.mul_assoc]
                _ = (M * N)ᵀ * V.pairingMatrix * M := by
                  rw [Matrix.transpose_mul]
                _ = V.pairingMatrix * M := by
                  rw [hMN, Matrix.transpose_one]
                  simp
            rw [hright]
      _ = Mᵀ * (Y.1ᵀ * V.pairingMatrix) * M := by
            simp only [Matrix.mul_assoc]
      _ = Mᵀ * (-(V.pairingMatrix * Y.1)) * M := by rw [hY]
      _ = -((Mᵀ * V.pairingMatrix) * Y.1 * M) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -((U.pairingMatrix * N) * Y.1 * M) := by rw [hleft]
      _ = -(U.pairingMatrix * (N * Y.1 * M)) := by
            simp only [Matrix.mul_assoc]
  left_inv X := by
    apply Subtype.ext
    change rationalIsometryInverseMatrix U V e *
          (rationalIsometryMatrix U V e * X.1 *
            rationalIsometryInverseMatrix U V e) *
          rationalIsometryMatrix U V e = X.1
    calc
      _ = (rationalIsometryInverseMatrix U V e *
            rationalIsometryMatrix U V e) * X.1 *
          (rationalIsometryInverseMatrix U V e *
            rationalIsometryMatrix U V e) := by
              simp only [Matrix.mul_assoc]
      _ = X.1 := by
        rw [rationalIsometryInverseMatrix_mul_matrix U V e]
        simp
  right_inv Y := by
    apply Subtype.ext
    change rationalIsometryMatrix U V e *
          (rationalIsometryInverseMatrix U V e * Y.1 *
            rationalIsometryMatrix U V e) *
          rationalIsometryInverseMatrix U V e = Y.1
    calc
      _ = (rationalIsometryMatrix U V e *
            rationalIsometryInverseMatrix U V e) * Y.1 *
          (rationalIsometryMatrix U V e *
            rationalIsometryInverseMatrix U V e) := by
              simp only [Matrix.mul_assoc]
      _ = Y.1 := by
        rw [rationalIsometryMatrix_mul_inverseMatrix U V e]
        simp
  map_add' X Y := by
    apply Subtype.ext
    change rationalIsometryMatrix U V e * (X.1 + Y.1) *
        rationalIsometryInverseMatrix U V e =
      rationalIsometryMatrix U V e * X.1 *
          rationalIsometryInverseMatrix U V e +
        rationalIsometryMatrix U V e * Y.1 *
          rationalIsometryInverseMatrix U V e
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by
    apply Subtype.ext
    change rationalIsometryMatrix U V e * (a • X.1) *
        rationalIsometryInverseMatrix U V e =
      a • (rationalIsometryMatrix U V e * X.1 *
        rationalIsometryInverseMatrix U V e)
    simp

@[simp]
theorem coe_rationalIsometrySkewAdjointLinearEquiv_apply
    (X : skewAdjointMatricesLieSubalgebra U.pairingMatrix) :
    (rationalIsometrySkewAdjointLinearEquiv U V e X :
        Matrix (Fin s) (Fin s) ℚ) =
      rationalIsometryMatrix U V e * X.1 *
        rationalIsometryInverseMatrix U V e := by
  simp [rationalIsometrySkewAdjointLinearEquiv]

/-- The source fixed tangent basis, transported through the isometry and
reindexed by the forced equality of tangent dimensions. -/
def rationalIsometrySkewAdjointTransportedFinBasis :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra V.pairingMatrix)))
      ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix) :=
  ((Matrix.skewAdjointFinBasis U.pairingMatrix).map
      (rationalIsometrySkewAdjointLinearEquiv U V e)).reindex
    (Fin.castOrderIso
      (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq)

/-- Rational differential modulus of an arbitrary supplied isometry in the
two independently fixed native tangent bases. -/
def rationalIsometrySkewAdjointDetScalar : ℚ :=
  (Matrix.skewAdjointFinBasis V.pairingMatrix).det
    (rationalIsometrySkewAdjointTransportedFinBasis U V e)

theorem rationalIsometrySkewAdjointDetScalar_ne_zero :
    rationalIsometrySkewAdjointDetScalar U V e ≠ 0 := by
  rw [rationalIsometrySkewAdjointDetScalar,
    ← Module.Basis.det_basis
      (rationalIsometrySkewAdjointTransportedFinBasis U V e)
      (Matrix.skewAdjointFinBasis V.pairingMatrix),
    ← LinearEquiv.coe_det]
  exact Units.ne_zero _

/-- Archimedean absolute value and all nontrivial p-adic norms of the
arbitrary-isometry tangent modulus multiply to one. -/
theorem rationalIsometrySkewAdjointDetScalar_product_formula :
    ENNReal.ofReal
          |((rationalIsometrySkewAdjointDetScalar U V e : ℚ) : ℝ)| *
        (∏ q ∈ Rat.padicNormPrimeSupport
            (rationalIsometrySkewAdjointDetScalar U V e),
          Rat.padicNormENNRealAtPrime
            (rationalIsometrySkewAdjointDetScalar U V e) q) = 1 := by
  exact Rat.ofReal_abs_mul_prod_padicNormENNRealAtPrime_eq_one
    (rationalIsometrySkewAdjointDetScalar U V e)
    (rationalIsometrySkewAdjointDetScalar_ne_zero U V e)

end RationalQuadraticSpaceMatrix

end
