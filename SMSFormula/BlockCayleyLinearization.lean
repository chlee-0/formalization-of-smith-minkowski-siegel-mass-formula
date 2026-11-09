import SMSFormula.RationalCliffordSpinDiagonalBlockCayley

/-!
# Linearization of the block Cayley coordinates

The Cayley coordinates of the block points are linear maps of rescaled parameters:

`X_U(u, v) = L_U(σ_U(u, v))`,  `X_T(u) = L_T(σ_T(u))`,

with `L_U(u, v) = ad₊(u) + ad₋(v)`, `L_T(u) = L_U(u, u)|_T`, and the explicit rescalings
`σ_U(u, v) = ((1 + N v) u, (1 + N u) v) / (1 − N u N v)`, `σ_T(u) = (1 + N u) u / (1 − (N u)²)`.
The linear parts are skew-adjoint for the diagonal forms, and their form-adapted elementary
coordinates (strict-upper entries of `D · L`) are explicit matrices of determinants
`8 (f₀f₁f₂)²` and `−8 (f₀f₁f₂)⁵`.  Pure algebra over a field; nothing is chosen.
-/

noncomputable section

open Matrix

namespace RationalQuadraticSpaceMatrix

section Defs

variable (f : Fin 3 → ℚ) (K : Type*) [Field K] [Algebra ℚ K]

local notation "a0" => algebraMap ℚ K (f 0)
local notation "a1" => algebraMap ℚ K (f 1)
local notation "a2" => algebraMap ℚ K (f 2)

/-- The block Cayley rescaling `σ_U(u, v)`. -/
def blockCayleyRescale (w : (Fin 3 → K) × (Fin 3 → K)) :
    (Fin 3 → K) × (Fin 3 → K) :=
  (((1 - blockPureNorm f K w.1 * blockPureNorm f K w.2)⁻¹ * (1 + blockPureNorm f K w.2)) • w.1,
    ((1 - blockPureNorm f K w.1 * blockPureNorm f K w.2)⁻¹ * (1 + blockPureNorm f K w.1)) • w.2)

/-- The ternary Cayley rescaling `σ_T(u)`. -/
def ternaryCayleyRescale (u : Fin 3 → K) : Fin 3 → K :=
  ((1 - blockPureNorm f K u * blockPureNorm f K u)⁻¹ * (1 + blockPureNorm f K u)) • u

/-- The linear part `L_U(u, v)` of the block Cayley coordinate (explicit entries). -/
def blockCayleyLinearMap :
    ((Fin 3 → K) × (Fin 3 → K)) →ₗ[K] Matrix (Fin 4) (Fin 4) K where
  toFun w := !![0, a1 * (w.1 0 + w.2 0), a2 * (w.1 1 + w.2 1), a1 * a2 * (w.2 2 - w.1 2);
    -(a0 * (w.1 0 + w.2 0)), 0, a2 * (w.1 2 + w.2 2), a0 * a2 * (w.1 1 - w.2 1);
    -(a0 * (w.1 1 + w.2 1)), -(a1 * (w.1 2 + w.2 2)), 0, a0 * a1 * (w.2 0 - w.1 0);
    w.1 2 - w.2 2, w.2 1 - w.1 1, w.1 0 - w.2 0, 0]
  map_add' w w' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The linear part `L_T(u)` of the ternary Cayley coordinate (explicit entries). -/
def ternaryCayleyLinearMap :
    (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K where
  toFun u := !![0, 2 * a1 * u 0, 2 * a2 * u 1; -(2 * a0 * u 0), 0, 2 * a2 * u 2; -(2 * a0 * u 1), -(2 * a1 * u 2), 0]
  map_add' u u' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c u := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The elementary coordinate matrix of `L_T`. -/
def ternaryElementaryMatrix : Matrix (Fin 3) (Fin 3) K :=
  diagonal ![2 * a0 * a1, 2 * a0 * a2, 2 * a1 * a2]

/-- The elementary coordinate matrix of `L_U`. -/
def blockElementaryMatrix :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks (diagonal ![a0 * a1, a0 * a2, a1 * a2]) 0 0 (diagonal ![a0 * a1 * a2, -(a0 * a1 * a2), a0 * a1 * a2]) *
    fromBlocks 1 1 (-1) 1

end Defs

section Linear

variable {f : Fin 3 → ℚ} (hδ : f 0 * f 1 * f 2 ≠ 0) (K : Type*) [Field K] [Algebra ℚ K]

local notation "a0" => algebraMap ℚ K (f 0)
local notation "a1" => algebraMap ℚ K (f 1)
local notation "a2" => algebraMap ℚ K (f 2)

omit [Algebra ℚ K] in
theorem blockAdLeft_smul {g0 g1 g2 : K} (h0 : g0 ≠ 0) (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) (c : K) (u : Fin 3 → K) :
    BlockConjugationCoordinates.blockAdLeft g0 g1 g2 (c • u) =
      c • BlockConjugationCoordinates.blockAdLeft g0 g1 g2 u := by
  rw [BlockConjugationCoordinates.blockAdLeft_eq _ _ _ h0 h1 h2,
    BlockConjugationCoordinates.blockAdLeft_eq _ _ _ h0 h1 h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

omit [Algebra ℚ K] in
theorem blockAdRight_smul {g0 g1 g2 : K} (h0 : g0 ≠ 0) (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) (c : K) (u : Fin 3 → K) :
    BlockConjugationCoordinates.blockAdRight g0 g1 g2 (c • u) =
      c • BlockConjugationCoordinates.blockAdRight g0 g1 g2 u := by
  rw [BlockConjugationCoordinates.blockAdRight_eq _ _ _ h0 h1 h2,
    BlockConjugationCoordinates.blockAdRight_eq _ _ _ h0 h1 h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem blockCayleyRescale_diag (u : Fin 3 → K) :
    blockCayleyRescale f K (u, u) = (ternaryCayleyRescale f K u, ternaryCayleyRescale f K u) :=
  rfl

include hδ in
theorem blockAd_add_eq_linearMap (w : (Fin 3 → K) × (Fin 3 → K)) :
    BlockConjugationCoordinates.blockAdLeft a0 a1 a2 w.1 + BlockConjugationCoordinates.blockAdRight a0 a1 a2 w.2 =
      blockCayleyLinearMap f K w := by
  have h0 : a0 ≠ 0 := (map_ne_zero _).2 (diagonalBlock_f_ne_zero hδ 0)
  have h1 : a1 ≠ 0 := (map_ne_zero _).2 (diagonalBlock_f_ne_zero hδ 1)
  have h2 : a2 ≠ 0 := (map_ne_zero _).2 (diagonalBlock_f_ne_zero hδ 2)
  rw [BlockConjugationCoordinates.blockAdLeft_eq _ _ _ h0 h1 h2,
    BlockConjugationCoordinates.blockAdRight_eq _ _ _ h0 h1 h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockCayleyLinearMap] <;> ring

include hδ in
/-- The block Cayley coordinate is linear in the rescaled parameters. -/
theorem blockCayleyX_eq_linearMap (w : (Fin 3 → K) × (Fin 3 → K)) :
    blockCayleyX f K w.1 w.2 = blockCayleyLinearMap f K (blockCayleyRescale f K w) := by
  have h0 : a0 ≠ 0 := (map_ne_zero _).2 (diagonalBlock_f_ne_zero hδ 0)
  have h1 : a1 ≠ 0 := (map_ne_zero _).2 (diagonalBlock_f_ne_zero hδ 1)
  have h2 : a2 ≠ 0 := (map_ne_zero _).2 (diagonalBlock_f_ne_zero hδ 2)
  rw [← blockAd_add_eq_linearMap hδ K]
  simp only [blockCayleyX, BlockConjugationCoordinates.blockCayleyInverse, blockCayleyRescale,
    blockAdLeft_smul K h0 h1 h2, blockAdRight_smul K h0 h1 h2, smul_add, smul_smul]

include hδ in
theorem ternaryCayleyLinearMap_eq (u : Fin 3 → K) :
    ternaryCayleyLinearMap f K u = upperLeftBlock (blockCayleyLinearMap f K (u, u)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ternaryCayleyLinearMap, blockCayleyLinearMap, upperLeftBlock] <;> ring

include hδ in
/-- The ternary Cayley coordinate is linear in the rescaled parameter. -/
theorem ternaryCayleyX_eq_linearMap (u : Fin 3 → K) :
    ternaryCayleyX f K u = ternaryCayleyLinearMap f K (ternaryCayleyRescale f K u) := by
  rw [ternaryCayleyLinearMap_eq hδ K, ← blockCayleyRescale_diag, ← blockCayleyX_eq_linearMap hδ K]

/-! ### Skewness -/

theorem blockCayleyLinearMap_mem (w : (Fin 3 → K) × (Fin 3 → K)) :
    blockCayleyLinearMap f K w ∈
      skewAdjointMatricesLieSubalgebra ((diagonal (diagonalBlockWeights f)).map (algebraMap ℚ K)) := by
  haveI := algebraRat.charZero K
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint,
    Matrix.IsAdjointPair, diagonal_map (map_zero _)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockCayleyLinearMap, diagonalBlockWeights, Matrix.mul_apply, Fin.sum_univ_four] <;> push_cast <;> ring

theorem ternaryCayleyLinearMap_mem (u : Fin 3 → K) :
    ternaryCayleyLinearMap f K u ∈ skewAdjointMatricesLieSubalgebra ((diagonal f).map (algebraMap ℚ K)) := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint,
    Matrix.IsAdjointPair, diagonal_map (map_zero _)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ternaryCayleyLinearMap, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-! ### Elementary coordinates -/

/-- The strict-upper pairs of `Fin 3`, listed as `(0,1), (0,2), (1,2)`. -/
def ternaryPairEquiv : Fin 3 ≃ StrictUpperPair 3 :=
  Equiv.ofBijective ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩] (by decide)

/-- The strict-upper pairs of `Fin 4`, listed as `(0,1), (0,2), (1,2) | (2,3), (1,3), (0,3)`. -/
def blockPairEquiv : Fin 3 ⊕ Fin 3 ≃ StrictUpperPair 4 :=
  Equiv.ofBijective
    (Sum.elim ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩]
      ![⟨(2, 3), by decide⟩, ⟨(1, 3), by decide⟩, ⟨(0, 3), by decide⟩]) (by decide)

theorem ternaryElementary_coordinates (u : Fin 3 → K) (k : Fin 3) :
    ((diagonal f).map (algebraMap ℚ K) * ternaryCayleyLinearMap f K u) (ternaryPairEquiv k).1.1
        (ternaryPairEquiv k).1.2 =
      Matrix.toLin' (ternaryElementaryMatrix f K) u k := by
  rw [diagonal_map (map_zero _)]
  fin_cases k <;>
    simp [ternaryPairEquiv, ternaryCayleyLinearMap, ternaryElementaryMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec_diagonal] <;> ring

theorem blockElementary_coordinates (w : (Fin 3 → K) × (Fin 3 → K)) (k : Fin 3 ⊕ Fin 3) :
    ((diagonal (diagonalBlockWeights f)).map (algebraMap ℚ K) * blockCayleyLinearMap f K w) (blockPairEquiv k).1.1
        (blockPairEquiv k).1.2 =
      Matrix.toLin' (blockElementaryMatrix f K) (Sum.elim w.1 w.2) k := by
  rw [diagonal_map (map_zero _), Matrix.toLin'_apply, blockElementaryMatrix, fromBlocks_multiply]
  rcases k with k | k <;> fin_cases k <;>
    simp [blockPairEquiv, blockCayleyLinearMap, diagonalBlockWeights, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem det_ternaryElementaryMatrix :
    (ternaryElementaryMatrix f K).det = algebraMap ℚ K (8 * (f 0 * f 1 * f 2) ^ 2) := by
  haveI := algebraRat.charZero K
  simp [ternaryElementaryMatrix, det_diagonal, Fin.prod_univ_three]
  push_cast
  ring

theorem det_blockElementaryMatrix :
    (blockElementaryMatrix f K).det = algebraMap ℚ K (-(8 * (f 0 * f 1 * f 2) ^ 5)) := by
  haveI := algebraRat.charZero K
  rw [blockElementaryMatrix, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_one₁₁]
  simp [det_diagonal, Fin.prod_univ_three]
  have h2 : (1 : Matrix (Fin 3) (Fin 3) K) + 1 = diagonal fun _ ↦ 2 := by
    rw [← diagonal_one, diagonal_add]
    norm_num
  rw [h2, det_diagonal, Fin.prod_const]
  push_cast
  ring

end Linear

end RationalQuadraticSpaceMatrix
