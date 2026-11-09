import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant of an upper block linear map

This file isolates the finite-dimensional linear algebra used by geometric
coordinate calculations. A linear endomorphism of a product whose lower-left
block vanishes has determinant equal to the product of its diagonal-block
determinants.
-/

noncomputable section

open Matrix

namespace LinearMap

variable {𝕜 M N : Type*}
  [Field 𝕜]
  [AddCommGroup M] [Module 𝕜 M]
  [AddCommGroup N] [Module 𝕜 N]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Matrix form of an upper block endomorphism in a product basis. -/
theorem toMatrix_prod_eq_fromBlocks_of_apply
    (b : Module.Basis ι 𝕜 M) (c : Module.Basis κ 𝕜 N)
    (L : M × N →ₗ[𝕜] M × N)
    (A : M →ₗ[𝕜] M) (B : N →ₗ[𝕜] M) (D : N →ₗ[𝕜] N)
    (hL : ∀ x y, L (x, y) = (A x + B y, D y)) :
    LinearMap.toMatrix (b.prod c) (b.prod c) L =
      Matrix.fromBlocks
        (LinearMap.toMatrix b b A)
        (LinearMap.toMatrix c b B)
        0
        (LinearMap.toMatrix c c D) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [LinearMap.toMatrix_apply, hL]

/-- Determinant of an upper block endomorphism. -/
theorem det_eq_mul_of_apply_eq_upperBlocks
    (b : Module.Basis ι 𝕜 M) (c : Module.Basis κ 𝕜 N)
    (L : M × N →ₗ[𝕜] M × N)
    (A : M →ₗ[𝕜] M) (B : N →ₗ[𝕜] M) (D : N →ₗ[𝕜] N)
    (hL : ∀ x y, L (x, y) = (A x + B y, D y)) :
    LinearMap.det L = LinearMap.det A * LinearMap.det D := by
  rw [← LinearMap.det_toMatrix (b.prod c) L,
    LinearMap.toMatrix_prod_eq_fromBlocks_of_apply b c L A B D hL,
    Matrix.det_fromBlocks_zero₂₁]
  rw [LinearMap.det_toMatrix, LinearMap.det_toMatrix]

end LinearMap
