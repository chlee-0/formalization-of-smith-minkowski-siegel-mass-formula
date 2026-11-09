import SMSFormula.SpecialOrthogonalRealIdentityLastColumnHomogeneousSpaceTopology
import Mathlib.Algebra.Lie.Classical

/-!
# Tangent decomposition for the identity-model last-column map

For the identity form in rank `n + 1`, a skew-adjoint matrix is determined by
its upper-left rank-`n` skew-adjoint block and the nonfinal entries of its last
column. This module packages that decomposition as a continuous linear
equivalence. It also identifies the differential at identity of the ambient
last-column coordinate map with the second projection and identifies its
kernel with the block-embedded lower-rank tangent carrier.

No quotient measure, disintegration, rank recurrence, or basis determinant is
introduced here.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- The identity-form skew-adjoint tangent carrier in rank `n`. -/
abbrev identitySpecialOrthogonalTangent (n : ℕ) :=
  (skewAdjointMatricesLieSubalgebra
    (1 : Matrix (Fin n) (Fin n) ℝ)).toSubmodule

/-- The skew matrix with upper-left block `B` and nonfinal last column `v`. -/
def identitySpecialOrthogonalSkewBlockMatrix
    (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j =>
    Fin.lastCases
      (Fin.lastCases 0 (fun j => -v j) j)
      (fun i => Fin.lastCases (v i) (fun j => B i j) j)
      i

@[simp]
theorem identitySpecialOrthogonalSkewBlockMatrix_cast_cast
    (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (i j : Fin n) :
    identitySpecialOrthogonalSkewBlockMatrix n B v i.castSucc j.castSucc =
      B i j := by
  simp [identitySpecialOrthogonalSkewBlockMatrix]

@[simp]
theorem identitySpecialOrthogonalSkewBlockMatrix_cast_last
    (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin n) :
    identitySpecialOrthogonalSkewBlockMatrix n B v i.castSucc (Fin.last n) =
      v i := by
  simp [identitySpecialOrthogonalSkewBlockMatrix]

@[simp]
theorem identitySpecialOrthogonalSkewBlockMatrix_last_cast
    (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (j : Fin n) :
    identitySpecialOrthogonalSkewBlockMatrix n B v (Fin.last n) j.castSucc =
      -v j := by
  simp [identitySpecialOrthogonalSkewBlockMatrix]

@[simp]
theorem identitySpecialOrthogonalSkewBlockMatrix_last_last
    (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    identitySpecialOrthogonalSkewBlockMatrix n B v
        (Fin.last n) (Fin.last n) = 0 := by
  simp [identitySpecialOrthogonalSkewBlockMatrix]

/-- Extract the lower-rank skew block and nonfinal last-column coordinates. -/
def identitySpecialOrthogonalTangentSplit
    (n : ℕ) (X : identitySpecialOrthogonalTangent (n + 1)) :
    identitySpecialOrthogonalTangent n × (Fin n → ℝ) := by
  let B := identitySpecialOrthogonalUpperLeftBlock n X.1
  have hX : X.1ᵀ = -X.1 :=
    (LieAlgebra.Orthogonal.mem_so (Fin (n + 1)) ℝ X.1).mp X.2
  have hB : Bᵀ = -B := by
    ext i j
    have hij := congrArg
      (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
        M i.castSucc j.castSucc) hX
    simpa [B, identitySpecialOrthogonalUpperLeftBlock] using hij
  exact
    (⟨B, (LieAlgebra.Orthogonal.mem_so (Fin n) ℝ B).mpr hB⟩,
      fun i => X.1 i.castSucc (Fin.last n))

/-- Reconstruct a rank-`n + 1` skew-adjoint matrix from the split data. -/
def identitySpecialOrthogonalTangentUnsplit
    (n : ℕ) (p : identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :
    identitySpecialOrthogonalTangent (n + 1) := by
  let M := identitySpecialOrthogonalSkewBlockMatrix n p.1.1 p.2
  have hB : p.1.1ᵀ = -p.1.1 :=
    (LieAlgebra.Orthogonal.mem_so (Fin n) ℝ p.1.1).mp p.1.2
  refine ⟨M, (LieAlgebra.Orthogonal.mem_so (Fin (n + 1)) ℝ M).mpr ?_⟩
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last => simp [M]
      | cast j => simp [M]
  | cast i =>
      cases j using Fin.lastCases with
      | last => simp [M]
      | cast j =>
          have hij := congrArg
            (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hB
          simpa [M] using hij

/-- A rank-`n + 1` identity tangent is a lower-rank identity tangent together
with its nonfinal last-column coordinates. -/
def identitySpecialOrthogonalTangentLinearEquiv (n : ℕ) :
    identitySpecialOrthogonalTangent (n + 1) ≃ₗ[ℝ]
      identitySpecialOrthogonalTangent n × (Fin n → ℝ) where
  toFun := identitySpecialOrthogonalTangentSplit n
  invFun := identitySpecialOrthogonalTangentUnsplit n
  map_add' X Y := by
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      rfl
    · funext i
      rfl
  map_smul' c X := by
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      rfl
    · funext i
      rfl
  left_inv X := by
    apply Subtype.ext
    ext i j
    cases i using Fin.lastCases with
    | last =>
        cases j using Fin.lastCases with
        | last =>
            have hX :=
              (LieAlgebra.Orthogonal.mem_so (Fin (n + 1)) ℝ X.1).mp X.2
            have hii := congrArg
              (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
                A (Fin.last n) (Fin.last n)) hX
            have hii' :
                X.1 (Fin.last n) (Fin.last n) =
                  -X.1 (Fin.last n) (Fin.last n) := by
              simpa using hii
            simp only [identitySpecialOrthogonalTangentUnsplit,
              identitySpecialOrthogonalTangentSplit,
              identitySpecialOrthogonalSkewBlockMatrix_last_last]
            linarith
        | cast j =>
            have hX :=
              (LieAlgebra.Orthogonal.mem_so (Fin (n + 1)) ℝ X.1).mp X.2
            have hij := congrArg
              (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
                A (Fin.last n) j.castSucc) hX
            have hij' :
                X.1 j.castSucc (Fin.last n) =
                  -X.1 (Fin.last n) j.castSucc := by
              simpa using hij
            simp only [identitySpecialOrthogonalTangentUnsplit,
              identitySpecialOrthogonalTangentSplit,
              identitySpecialOrthogonalSkewBlockMatrix_last_cast]
            linarith
    | cast i =>
        cases j using Fin.lastCases with
        | last =>
            simp [identitySpecialOrthogonalTangentUnsplit,
              identitySpecialOrthogonalTangentSplit]
        | cast j =>
            simp [identitySpecialOrthogonalTangentUnsplit,
              identitySpecialOrthogonalTangentSplit,
              identitySpecialOrthogonalUpperLeftBlock]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      simp [identitySpecialOrthogonalTangentUnsplit,
        identitySpecialOrthogonalTangentSplit,
        identitySpecialOrthogonalUpperLeftBlock]
    · funext i
      simp [identitySpecialOrthogonalTangentUnsplit,
        identitySpecialOrthogonalTangentSplit]

/-- The identity tangent decomposition as a continuous linear equivalence. -/
noncomputable def identitySpecialOrthogonalTangentContinuousLinearEquiv
    (n : ℕ) :
    identitySpecialOrthogonalTangent (n + 1) ≃L[ℝ]
      identitySpecialOrthogonalTangent n × (Fin n → ℝ) :=
  (identitySpecialOrthogonalTangentLinearEquiv n).toContinuousLinearEquiv

/-- The ambient linear map taking the nonfinal entries of the last column. -/
def identitySpecialOrthogonalAmbientLastColumnLinearMap (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →ₗ[ℝ] (Fin n → ℝ) where
  toFun X := fun i => X i.castSucc (Fin.last n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The continuous ambient nonfinal-last-column linear map. -/
noncomputable def
    identitySpecialOrthogonalAmbientLastColumnContinuousLinearMap (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →L[ℝ] (Fin n → ℝ) :=
  ⟨identitySpecialOrthogonalAmbientLastColumnLinearMap n,
    LinearMap.continuous_of_finiteDimensional _⟩

/-- The derivative of the ambient last-column coordinate map is the same
constant linear map at every matrix. -/
theorem hasFDerivAt_identitySpecialOrthogonalAmbientLastColumn
    (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    HasFDerivAt
      (fun X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
        fun i => X i.castSucc (Fin.last n))
      (identitySpecialOrthogonalAmbientLastColumnContinuousLinearMap n) A :=
  (identitySpecialOrthogonalAmbientLastColumnContinuousLinearMap n).hasFDerivAt

/-- The actual ambient derivative is the nonfinal-last-column linear map. -/
theorem fderiv_identitySpecialOrthogonalAmbientLastColumn
    (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    fderiv ℝ
        (fun X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
          fun i => X i.castSucc (Fin.last n)) A =
      identitySpecialOrthogonalAmbientLastColumnContinuousLinearMap n :=
  (hasFDerivAt_identitySpecialOrthogonalAmbientLastColumn n A).fderiv

/-- Restriction of the ambient last-column coordinates to the tangent. -/
def identitySpecialOrthogonalTangentLastColumnLinearMap (n : ℕ) :
    identitySpecialOrthogonalTangent (n + 1) →ₗ[ℝ] (Fin n → ℝ) where
  toFun X := fun i => X.1 i.castSucc (Fin.last n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The continuous tangent last-column map. -/
noncomputable def
    identitySpecialOrthogonalTangentLastColumnContinuousLinearMap (n : ℕ) :
    identitySpecialOrthogonalTangent (n + 1) →L[ℝ] (Fin n → ℝ) :=
  ⟨identitySpecialOrthogonalTangentLastColumnLinearMap n,
    LinearMap.continuous_of_finiteDimensional _⟩

/-- Restricting the ambient last-column map along tangent inclusion gives the
tangent last-column map. -/
theorem identitySpecialOrthogonalAmbientLastColumn_comp_tangentInclusion
    (n : ℕ) :
    (identitySpecialOrthogonalAmbientLastColumnContinuousLinearMap n).comp
        (identitySpecialOrthogonalTangent (n + 1)).subtypeL =
      identitySpecialOrthogonalTangentLastColumnContinuousLinearMap n := by
  ext X i
  rfl

@[simp]
theorem identitySpecialOrthogonalTangentContinuousLinearEquiv_snd
    (n : ℕ) (X : identitySpecialOrthogonalTangent (n + 1)) :
    (identitySpecialOrthogonalTangentContinuousLinearEquiv n X).2 =
      identitySpecialOrthogonalTangentLastColumnContinuousLinearMap n X :=
  rfl

/-- Under the tangent decomposition, the tangent last-column map is exactly
the second projection. -/
theorem identitySpecialOrthogonalTangentLastColumn_eq_snd_comp
    (n : ℕ) :
    identitySpecialOrthogonalTangentLastColumnContinuousLinearMap n =
      (ContinuousLinearMap.snd ℝ
        (identitySpecialOrthogonalTangent n) (Fin n → ℝ)).comp
          (identitySpecialOrthogonalTangentContinuousLinearEquiv n :
            identitySpecialOrthogonalTangent (n + 1) →L[ℝ]
              identitySpecialOrthogonalTangent n × (Fin n → ℝ)) := by
  ext X i
  rfl

/-- At identity, the ambient last-column differential restricted to the
skew-adjoint tangent is the second projection under the decomposition. -/
theorem
    fderiv_identitySpecialOrthogonalAmbientLastColumn_one_comp_tangentInclusion
    (n : ℕ) :
    (fderiv ℝ
        (fun X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
          fun i => X i.castSucc (Fin.last n))
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).comp
          (identitySpecialOrthogonalTangent (n + 1)).subtypeL =
      (ContinuousLinearMap.snd ℝ
        (identitySpecialOrthogonalTangent n) (Fin n → ℝ)).comp
          (identitySpecialOrthogonalTangentContinuousLinearEquiv n :
            identitySpecialOrthogonalTangent (n + 1) →L[ℝ]
              identitySpecialOrthogonalTangent n × (Fin n → ℝ)) := by
  rw [fderiv_identitySpecialOrthogonalAmbientLastColumn,
    identitySpecialOrthogonalAmbientLastColumn_comp_tangentInclusion,
    identitySpecialOrthogonalTangentLastColumn_eq_snd_comp]

/-- Embed the lower-rank identity tangent as a final-row/final-column zero
block. -/
def identitySpecialOrthogonalTangentBlockEmbedLinearMap (n : ℕ) :
    identitySpecialOrthogonalTangent n →ₗ[ℝ]
      identitySpecialOrthogonalTangent (n + 1) where
  toFun B := identitySpecialOrthogonalTangentUnsplit n (B, 0)
  map_add' B C := by
    apply Subtype.ext
    ext i j
    cases i using Fin.lastCases <;>
      cases j using Fin.lastCases <;>
      simp [identitySpecialOrthogonalTangentUnsplit, add_apply]
  map_smul' c B := by
    apply Subtype.ext
    ext i j
    cases i using Fin.lastCases <;>
      cases j using Fin.lastCases <;>
      simp [identitySpecialOrthogonalTangentUnsplit]

/-- The continuous lower-rank tangent block embedding. -/
noncomputable def
    identitySpecialOrthogonalTangentBlockEmbedContinuousLinearMap (n : ℕ) :
    identitySpecialOrthogonalTangent n →L[ℝ]
      identitySpecialOrthogonalTangent (n + 1) :=
  ⟨identitySpecialOrthogonalTangentBlockEmbedLinearMap n,
    LinearMap.continuous_of_finiteDimensional _⟩

/-- The kernel of the identity last-column tangent map is exactly the
block-embedded lower-rank tangent carrier. -/
theorem ker_identitySpecialOrthogonalTangentLastColumnLinearMap (n : ℕ) :
    LinearMap.ker (identitySpecialOrthogonalTangentLastColumnLinearMap n) =
      LinearMap.range
        (identitySpecialOrthogonalTangentBlockEmbedLinearMap n) := by
  ext X
  constructor
  · intro hX
    rw [LinearMap.mem_ker] at hX
    refine ⟨(identitySpecialOrthogonalTangentSplit n X).1, ?_⟩
    apply Subtype.ext
    ext i j
    cases i using Fin.lastCases with
    | last =>
        cases j using Fin.lastCases with
        | last =>
            simp [identitySpecialOrthogonalTangentBlockEmbedLinearMap,
              identitySpecialOrthogonalTangentUnsplit]
            have hskew :=
              (LieAlgebra.Orthogonal.mem_so (Fin (n + 1)) ℝ X.1).mp X.2
            have hii := congrArg
              (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
                A (Fin.last n) (Fin.last n)) hskew
            have hii' :
                X.1 (Fin.last n) (Fin.last n) =
                  -X.1 (Fin.last n) (Fin.last n) := by
              simpa using hii
            linarith
        | cast j =>
            simp [identitySpecialOrthogonalTangentBlockEmbedLinearMap,
              identitySpecialOrthogonalTangentUnsplit]
            have hskew :=
              (LieAlgebra.Orthogonal.mem_so (Fin (n + 1)) ℝ X.1).mp X.2
            have hij := congrArg
              (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
                A (Fin.last n) j.castSucc) hskew
            have hij' :
                X.1 j.castSucc (Fin.last n) =
                  -X.1 (Fin.last n) j.castSucc := by
              simpa using hij
            have hcol : X.1 j.castSucc (Fin.last n) = 0 :=
              congrFun hX j
            linarith
    | cast i =>
        cases j using Fin.lastCases with
        | last =>
            simpa [identitySpecialOrthogonalTangentBlockEmbedLinearMap,
              identitySpecialOrthogonalTangentUnsplit] using
                (congrFun hX i).symm
        | cast j =>
            simp [identitySpecialOrthogonalTangentBlockEmbedLinearMap,
              identitySpecialOrthogonalTangentUnsplit,
              identitySpecialOrthogonalTangentSplit,
              identitySpecialOrthogonalUpperLeftBlock]
  · rintro ⟨B, rfl⟩
    rw [LinearMap.mem_ker]
    funext i
    simp [identitySpecialOrthogonalTangentLastColumnLinearMap,
      identitySpecialOrthogonalTangentBlockEmbedLinearMap,
      identitySpecialOrthogonalTangentUnsplit]

end PositiveDefiniteIntegralLattice
