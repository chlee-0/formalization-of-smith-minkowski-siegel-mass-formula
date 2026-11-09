import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarFactorization
import SMSFormula.RationalPadicNormProductFormula

/-!
# Rational differential modulus of an anisotropic presentation

A supplied anisotropic-complement presentation identifies two native quadratic
spaces whose coordinate index types need not be definitionally equal.  This
file constructs the resulting rational conjugation equivalence between their
skew-adjoint tangent spaces directly, without choosing a common chart.  Its
determinant in the two already fixed rational tangent bases is the single
rational modulus that must control both the real and finite presentation Haar
factors.

The rational product formula for that nonzero determinant is proved here.  No
local group measure is yet identified with the corresponding absolute-value
factor; that is the remaining differential/cylinder compatibility theorem.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped BigOperators Matrix ENNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Matrix of the rational block-to-ambient quadratic isometry. -/
abbrev blockToAmbientRationalMatrix
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Matrix (Fin n) (Fin (m + 1)) ℚ :=
  LinearMap.toMatrix' (P.blockToAmbientIsometryEquiv hx).toLinearEquiv.toLinearMap

/-- Matrix of the inverse rational block-to-ambient quadratic isometry. -/
abbrev ambientToBlockRationalMatrix
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Matrix (Fin (m + 1)) (Fin n) ℚ :=
  LinearMap.toMatrix'
    (P.blockToAmbientIsometryEquiv hx).symm.toLinearEquiv.toLinearMap

theorem blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.blockToAmbientRationalMatrix hx * P.ambientToBlockRationalMatrix hx = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have hcomp :
      (P.blockToAmbientIsometryEquiv hx).toLinearEquiv.toLinearMap.comp
          (P.blockToAmbientIsometryEquiv hx).symm.toLinearEquiv.toLinearMap =
        LinearMap.id := by
    apply LinearMap.ext
    intro y
    exact (P.blockToAmbientIsometryEquiv hx).apply_symm_apply y
  rw [hcomp, LinearMap.toMatrix'_id]

theorem ambientToBlockRationalMatrix_mul_blockToAmbientRationalMatrix
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.ambientToBlockRationalMatrix hx * P.blockToAmbientRationalMatrix hx = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have hcomp :
      (P.blockToAmbientIsometryEquiv hx).symm.toLinearEquiv.toLinearMap.comp
          (P.blockToAmbientIsometryEquiv hx).toLinearEquiv.toLinearMap =
        LinearMap.id := by
    apply LinearMap.ext
    intro y
    exact (P.blockToAmbientIsometryEquiv hx).symm_apply_apply y
  rw [hcomp, LinearMap.toMatrix'_id]

/-- The block and ambient form matrices satisfy the exact rectangular
congruence identity determined by the supplied rational isometry. -/
theorem blockToAmbientRationalMatrix_form_congruence
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockToAmbientRationalMatrix hx)ᵀ * V.pairingMatrix *
        P.blockToAmbientRationalMatrix hx =
      (P.blockSpace hx).pairingMatrix := by
  have hcomp :
      V.nativeRationalQuadraticForm.comp
          (P.blockToAmbientIsometryEquiv hx).toLinearEquiv.toLinearMap =
        (P.blockSpace hx).nativeRationalQuadraticForm := by
    apply QuadraticMap.ext
    intro y
    exact (P.blockToAmbientIsometryEquiv hx).map_app y
  have hmatrix := congrArg QuadraticForm.toMatrix' hcomp
  rw [QuadraticForm.toMatrix'_comp,
    V.quadraticForm_toMatrix',
    (P.blockSpace hx).quadraticForm_toMatrix'] at hmatrix
  exact hmatrix

/-- Conjugation through the supplied rational quadratic isometry transports
the block skew-adjoint tangent space to the ambient skew-adjoint tangent
space.  The construction works across the two native coordinate index types. -/
def blockToAmbientSkewAdjointLinearEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    skewAdjointMatricesLieSubalgebra (P.blockSpace hx).pairingMatrix ≃ₗ[ℚ]
      skewAdjointMatricesLieSubalgebra V.pairingMatrix where
  toFun X := by
    let M := P.blockToAmbientRationalMatrix hx
    let N := P.ambientToBlockRationalMatrix hx
    refine ⟨M * X.1 * N, ?_⟩
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
    have hX := X.property
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule] at hX
    have hMN : M * N = 1 :=
      P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx
    have hNM : N * M = 1 :=
      P.ambientToBlockRationalMatrix_mul_blockToAmbientRationalMatrix hx
    have hform : Mᵀ * V.pairingMatrix * M = (P.blockSpace hx).pairingMatrix :=
      P.blockToAmbientRationalMatrix_form_congruence hx
    have hleft : Mᵀ * V.pairingMatrix = (P.blockSpace hx).pairingMatrix * N := by
      calc
        Mᵀ * V.pairingMatrix = (Mᵀ * V.pairingMatrix) *
            (1 : Matrix (Fin n) (Fin n) ℚ) := by rw [Matrix.mul_one]
        _ = (Mᵀ * V.pairingMatrix) * (M * N) := by rw [hMN]
        _ = (Mᵀ * V.pairingMatrix * M) * N := by
          simp only [Matrix.mul_assoc]
        _ = (P.blockSpace hx).pairingMatrix * N := by rw [hform]
    have hright : Nᵀ * (P.blockSpace hx).pairingMatrix = V.pairingMatrix * M := by
      calc
        Nᵀ * (P.blockSpace hx).pairingMatrix =
            Nᵀ * (Mᵀ * V.pairingMatrix * M) := by rw [hform]
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
      _ = Nᵀ * X.1ᵀ * ((P.blockSpace hx).pairingMatrix * N) := by
            rw [hleft]
      _ = Nᵀ * (X.1ᵀ * (P.blockSpace hx).pairingMatrix) * N := by
            simp only [Matrix.mul_assoc]
      _ = Nᵀ * (-((P.blockSpace hx).pairingMatrix * X.1)) * N := by rw [hX]
      _ = -((Nᵀ * (P.blockSpace hx).pairingMatrix) * X.1 * N) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -((V.pairingMatrix * M) * X.1 * N) := by rw [hright]
      _ = -(V.pairingMatrix * (M * X.1 * N)) := by
            simp only [Matrix.mul_assoc]
  invFun Y := by
    let M := P.blockToAmbientRationalMatrix hx
    let N := P.ambientToBlockRationalMatrix hx
    refine ⟨N * Y.1 * M, ?_⟩
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
    have hY := Y.property
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule] at hY
    have hMN : M * N = 1 :=
      P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx
    have hform : Mᵀ * V.pairingMatrix * M = (P.blockSpace hx).pairingMatrix :=
      P.blockToAmbientRationalMatrix_form_congruence hx
    have hleft : Mᵀ * V.pairingMatrix = (P.blockSpace hx).pairingMatrix * N := by
      calc
        Mᵀ * V.pairingMatrix = (Mᵀ * V.pairingMatrix) *
            (1 : Matrix (Fin n) (Fin n) ℚ) := by rw [Matrix.mul_one]
        _ = (Mᵀ * V.pairingMatrix) * (M * N) := by rw [hMN]
        _ = (Mᵀ * V.pairingMatrix * M) * N := by
          simp only [Matrix.mul_assoc]
        _ = (P.blockSpace hx).pairingMatrix * N := by rw [hform]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_neg] at hY ⊢
    calc
      (N * Y.1 * M)ᵀ * (P.blockSpace hx).pairingMatrix =
          (Mᵀ * (Y.1ᵀ * Nᵀ)) * (P.blockSpace hx).pairingMatrix := by
            rw [Matrix.transpose_mul, Matrix.transpose_mul]
      _ = Mᵀ * Y.1ᵀ * (Nᵀ * (P.blockSpace hx).pairingMatrix) := by
            simp only [Matrix.mul_assoc]
      _ = Mᵀ * Y.1ᵀ * (V.pairingMatrix * M) := by
            have hright :
                Nᵀ * (P.blockSpace hx).pairingMatrix = V.pairingMatrix * M := by
              calc
                Nᵀ * (P.blockSpace hx).pairingMatrix =
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
      _ = -(((P.blockSpace hx).pairingMatrix * N) * Y.1 * M) := by
            rw [hleft]
      _ = -((P.blockSpace hx).pairingMatrix * (N * Y.1 * M)) := by
            simp only [Matrix.mul_assoc]
  left_inv X := by
    apply Subtype.ext
    change P.ambientToBlockRationalMatrix hx *
          (P.blockToAmbientRationalMatrix hx * X.1 *
            P.ambientToBlockRationalMatrix hx) *
          P.blockToAmbientRationalMatrix hx = X.1
    calc
      _ = (P.ambientToBlockRationalMatrix hx *
            P.blockToAmbientRationalMatrix hx) * X.1 *
          (P.ambientToBlockRationalMatrix hx *
            P.blockToAmbientRationalMatrix hx) := by
              simp only [Matrix.mul_assoc]
      _ = X.1 := by
        rw [P.ambientToBlockRationalMatrix_mul_blockToAmbientRationalMatrix hx]
        simp
  right_inv Y := by
    apply Subtype.ext
    change P.blockToAmbientRationalMatrix hx *
          (P.ambientToBlockRationalMatrix hx * Y.1 *
            P.blockToAmbientRationalMatrix hx) *
          P.ambientToBlockRationalMatrix hx = Y.1
    calc
      _ = (P.blockToAmbientRationalMatrix hx *
            P.ambientToBlockRationalMatrix hx) * Y.1 *
          (P.blockToAmbientRationalMatrix hx *
            P.ambientToBlockRationalMatrix hx) := by
              simp only [Matrix.mul_assoc]
      _ = Y.1 := by
        rw [P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx]
        simp
  map_add' X Y := by
    apply Subtype.ext
    change P.blockToAmbientRationalMatrix hx * (X.1 + Y.1) *
        P.ambientToBlockRationalMatrix hx =
      P.blockToAmbientRationalMatrix hx * X.1 *
          P.ambientToBlockRationalMatrix hx +
        P.blockToAmbientRationalMatrix hx * Y.1 *
          P.ambientToBlockRationalMatrix hx
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by
    apply Subtype.ext
    change P.blockToAmbientRationalMatrix hx * (a • X.1) *
        P.ambientToBlockRationalMatrix hx =
      a • (P.blockToAmbientRationalMatrix hx * X.1 *
        P.ambientToBlockRationalMatrix hx)
    simp

@[simp]
theorem coe_blockToAmbientSkewAdjointLinearEquiv_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (X : skewAdjointMatricesLieSubalgebra (P.blockSpace hx).pairingMatrix) :
    (P.blockToAmbientSkewAdjointLinearEquiv hx X :
        Matrix (Fin n) (Fin n) ℚ) =
      P.blockToAmbientRationalMatrix hx * X.1 *
        P.ambientToBlockRationalMatrix hx :=
  by rfl

/-- The source fixed tangent basis, transported through the presentation and
reindexed by the forced equality of tangent dimensions. -/
def blockToAmbientSkewAdjointTransportedFinBasis
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Module.Basis
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix)))
      ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix) :=
  ((Matrix.skewAdjointFinBasis (P.blockSpace hx).pairingMatrix).map
      (P.blockToAmbientSkewAdjointLinearEquiv hx)).reindex
    (Fin.castOrderIso
      (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq)

/-- The rational differential modulus of the supplied presentation in the
repository's independently fixed block and ambient tangent bases. -/
def blockToAmbientSkewAdjointDetScalar
    (hx : V.nativeRationalQuadraticForm x ≠ 0) : ℚ :=
  (Matrix.skewAdjointFinBasis V.pairingMatrix).det
    (P.blockToAmbientSkewAdjointTransportedFinBasis hx)

theorem blockToAmbientSkewAdjointDetScalar_ne_zero
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.blockToAmbientSkewAdjointDetScalar hx ≠ 0 := by
  rw [blockToAmbientSkewAdjointDetScalar,
    ← Module.Basis.det_basis
      (P.blockToAmbientSkewAdjointTransportedFinBasis hx)
      (Matrix.skewAdjointFinBasis V.pairingMatrix),
    ← LinearEquiv.coe_det]
  exact Units.ne_zero _

/-- The archimedean absolute value of the rational presentation modulus and
all of its nontrivial p-adic norms multiply to one. -/
theorem blockToAmbientSkewAdjointDetScalar_product_formula
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    ENNReal.ofReal
          |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)| *
        (∏ q ∈ Rat.padicNormPrimeSupport
            (P.blockToAmbientSkewAdjointDetScalar hx),
          Rat.padicNormENNRealAtPrime
            (P.blockToAmbientSkewAdjointDetScalar hx) q) = 1 := by
  exact Rat.ofReal_abs_mul_prod_padicNormENNRealAtPrime_eq_one
    (P.blockToAmbientSkewAdjointDetScalar hx)
    (P.blockToAmbientSkewAdjointDetScalar_ne_zero hx)

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
