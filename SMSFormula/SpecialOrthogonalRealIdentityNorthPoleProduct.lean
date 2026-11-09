import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleSection

/-!
# Identity-model north-pole product parametrization

This file combines the lower-rank identity inverse chart, embedded
as a final block, with the explicit north-pole section. The section is
multiplied on the left, so the lower block does not change its last column.

The resulting ambient matrix map is smooth on the exact product domain,
equals identity at zero, and has derivative the full identity
tangent unsplit map. No local inverse, change of variables, or measure
comparison is asserted.
-/

open scoped Matrix Matrix.Norms.Operator ContDiff

noncomputable section

open Metric Set Matrix

namespace PositiveDefiniteIntegralLattice

/-- The scalar-extended rational identity tangent used by the
lower-rank chart. -/
abbrev identitySpecialOrthogonalMappedTangent (n : ℕ) :=
  (skewAdjointMatricesLieSubalgebra
    ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))).toSubmodule

/-- The lower-rank inverse identity chart on its native tangent carrier. -/
noncomputable def identitySpecialOrthogonalLowerInverseCoordinateMatrix
    (n : ℕ) (X : identitySpecialOrthogonalMappedTangent n) :
    Matrix (Fin n) (Fin n) ℝ :=
  specialFormPreservingSmoothRealInverseCoordinateMatrix
    (1 : Matrix (Fin n) (Fin n) ℚ)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    X

@[simp]
theorem identitySpecialOrthogonalLowerInverseCoordinateMatrix_zero
    (n : ℕ) :
    identitySpecialOrthogonalLowerInverseCoordinateMatrix n 0 = 1 := by
  simp [identitySpecialOrthogonalLowerInverseCoordinateMatrix]

theorem hasFDerivAt_identitySpecialOrthogonalLowerInverseCoordinateMatrix_zero
    (n : ℕ) :
    HasFDerivAt
      (identitySpecialOrthogonalLowerInverseCoordinateMatrix n)
      (identitySpecialOrthogonalMappedTangent n).subtypeL 0 :=
  hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix_zero
    (1 : Matrix (Fin n) (Fin n) ℚ)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero

/-- Linear upper-left block embedding with zero final row and column. -/
def identitySpecialOrthogonalAmbientBlockLinearMap (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ where
  toFun A := identitySpecialOrthogonalSkewBlockMatrix n A 0
  map_add' A B := by
    ext i j
    cases i using Fin.lastCases <;>
      cases j using Fin.lastCases <;>
      simp
  map_smul' c A := by
    ext i j
    cases i using Fin.lastCases <;>
      cases j using Fin.lastCases <;>
      simp

noncomputable def identitySpecialOrthogonalAmbientBlockContinuousLinearMap
    (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  ⟨identitySpecialOrthogonalAmbientBlockLinearMap n,
    LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem identitySpecialOrthogonalAmbientBlockContinuousLinearMap_apply
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    identitySpecialOrthogonalAmbientBlockContinuousLinearMap n A =
      identitySpecialOrthogonalSkewBlockMatrix n A 0 :=
  rfl

theorem identitySpecialOrthogonalLastBlockMatrix_eq
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    identitySpecialOrthogonalLastBlockMatrix n A =
      identitySpecialOrthogonalAmbientBlockContinuousLinearMap n A +
        identitySpecialOrthogonalLastBlockMatrix n 0 := by
  ext i j
  cases i using Fin.lastCases <;>
    cases j using Fin.lastCases <;>
    simp

theorem hasFDerivAt_identitySpecialOrthogonalLastBlockMatrix
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    HasFDerivAt
      (identitySpecialOrthogonalLastBlockMatrix n)
      (identitySpecialOrthogonalAmbientBlockContinuousLinearMap n) A := by
  rw [show identitySpecialOrthogonalLastBlockMatrix n =
      fun B => identitySpecialOrthogonalAmbientBlockContinuousLinearMap n B +
        identitySpecialOrthogonalLastBlockMatrix n 0 by
    funext B
    exact identitySpecialOrthogonalLastBlockMatrix_eq n B]
  exact
    (identitySpecialOrthogonalAmbientBlockContinuousLinearMap n).hasFDerivAt.add_const _

/-- The lower-rank inverse chart embedded in the ambient final block. -/
noncomputable def identitySpecialOrthogonalLowerBlockChartMatrix
    (n : ℕ) (X : identitySpecialOrthogonalMappedTangent n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  identitySpecialOrthogonalLastBlockMatrix n
    (identitySpecialOrthogonalLowerInverseCoordinateMatrix n X)

noncomputable def identitySpecialOrthogonalLowerBlockChartDerivative
    (n : ℕ) :
    identitySpecialOrthogonalMappedTangent n →L[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (identitySpecialOrthogonalAmbientBlockContinuousLinearMap n).comp
    (identitySpecialOrthogonalMappedTangent n).subtypeL

@[simp]
theorem identitySpecialOrthogonalLowerBlockChartMatrix_zero
    (n : ℕ) :
    identitySpecialOrthogonalLowerBlockChartMatrix n 0 = 1 := by
  simp [identitySpecialOrthogonalLowerBlockChartMatrix]

theorem hasFDerivAt_identitySpecialOrthogonalLowerBlockChartMatrix_zero
    (n : ℕ) :
    HasFDerivAt
      (identitySpecialOrthogonalLowerBlockChartMatrix n)
      (identitySpecialOrthogonalLowerBlockChartDerivative n) 0 := by
  exact
    (hasFDerivAt_identitySpecialOrthogonalLastBlockMatrix n
      (identitySpecialOrthogonalLowerInverseCoordinateMatrix n 0)).comp 0
      (hasFDerivAt_identitySpecialOrthogonalLowerInverseCoordinateMatrix_zero n)

theorem identitySpecialOrthogonalLowerBlockChartDerivative_apply
    (n : ℕ) (X : identitySpecialOrthogonalMappedTangent n) :
    identitySpecialOrthogonalLowerBlockChartDerivative n X =
      (identitySpecialOrthogonalTangentUnsplit n
        (identitySpecialOrthogonalMappedIdentityTangentEquiv n X, 0)).1 := by
  ext i j
  cases i using Fin.lastCases <;>
    cases j using Fin.lastCases <;>
    simp [identitySpecialOrthogonalLowerBlockChartDerivative,
      identitySpecialOrthogonalTangentUnsplit]

/-- The exact lower-rank identity-chart target. -/
def identitySpecialOrthogonalLowerChartTargetSet (n : ℕ) :
    Set (identitySpecialOrthogonalMappedTangent n) :=
  (specialFormPreservingSmoothRealIdentityChart
    (1 : Matrix (Fin n) (Fin n) ℚ)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero).target

theorem isOpen_identitySpecialOrthogonalLowerChartTargetSet (n : ℕ) :
    IsOpen (identitySpecialOrthogonalLowerChartTargetSet n) := by
  exact
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero).open_target

theorem contDiffOn_identitySpecialOrthogonalLowerInverseCoordinateMatrix
    (n : ℕ) :
    ContDiffOn ℝ ∞
      (identitySpecialOrthogonalLowerInverseCoordinateMatrix n)
      (identitySpecialOrthogonalLowerChartTargetSet n) := by
  exact
    contDiffOn_specialFormPreservingSmoothRealInverseCoordinateMatrix
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
      (1 : specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)))

theorem contDiff_identitySpecialOrthogonalLastBlockMatrix (n : ℕ) :
    ContDiff ℝ ∞ (identitySpecialOrthogonalLastBlockMatrix n) := by
  rw [show identitySpecialOrthogonalLastBlockMatrix n =
      fun B => identitySpecialOrthogonalAmbientBlockContinuousLinearMap n B +
        identitySpecialOrthogonalLastBlockMatrix n 0 by
    funext B
    exact identitySpecialOrthogonalLastBlockMatrix_eq n B]
  exact
    (identitySpecialOrthogonalAmbientBlockContinuousLinearMap n).contDiff.add
      contDiff_const

theorem contDiffOn_identitySpecialOrthogonalLowerBlockChartMatrix
    (n : ℕ) :
    ContDiffOn ℝ ∞
      (identitySpecialOrthogonalLowerBlockChartMatrix n)
      (identitySpecialOrthogonalLowerChartTargetSet n) := by
  exact
    (contDiff_identitySpecialOrthogonalLastBlockMatrix n).comp_contDiffOn
      (contDiffOn_identitySpecialOrthogonalLowerInverseCoordinateMatrix n)

/-- The exact product domain of the lower identity chart and the north-pole
coordinate ball. -/
def identitySpecialOrthogonalNorthPoleProductDomainSet (n : ℕ) :
    Set (identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :=
  identitySpecialOrthogonalLowerChartTargetSet n ×ˢ
    Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1

theorem isOpen_identitySpecialOrthogonalNorthPoleProductDomainSet (n : ℕ) :
    IsOpen (identitySpecialOrthogonalNorthPoleProductDomainSet n) :=
  (isOpen_identitySpecialOrthogonalLowerChartTargetSet n).prod
    Metric.isOpen_ball

theorem zero_mem_identitySpecialOrthogonalNorthPoleProductDomainSet (n : ℕ) :
    (0 : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) ∈
        identitySpecialOrthogonalNorthPoleProductDomainSet n := by
  exact
    ⟨zero_mem_specialFormPreservingSmoothRealIdentityChart_target
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero,
      by simp⟩

/-- The local lower-rank/north-pole product parametrization in ambient
matrix coordinates. The section is on the left so the final column is
unchanged by the lower-rank block. -/
noncomputable def identitySpecialOrthogonalNorthPoleProductMatrix
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  identitySpecialOrthogonalNorthPoleSectionMatrix n p.2 *
    identitySpecialOrthogonalLowerBlockChartMatrix n p.1

@[simp]
theorem identitySpecialOrthogonalNorthPoleProductMatrix_zero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductMatrix n 0 = 1 := by
  simp [identitySpecialOrthogonalNorthPoleProductMatrix]

theorem identitySpecialOrthogonalNorthPoleProductMatrix_lastColumn
    (n : ℕ)
    (X : identitySpecialOrthogonalMappedTangent n)
    (v : EuclideanSpace ℝ (Fin n))
    (i : Fin (n + 1)) :
    identitySpecialOrthogonalNorthPoleProductMatrix n (X, v)
        i (Fin.last n) =
      identitySpecialOrthogonalNorthPoleInverseVector n v i := by
  rw [identitySpecialOrthogonalNorthPoleProductMatrix, Matrix.mul_apply,
    Fin.sum_univ_castSucc]
  cases i using Fin.lastCases <;>
    simp [identitySpecialOrthogonalLowerBlockChartMatrix]

theorem contDiffOn_identitySpecialOrthogonalNorthPoleProductMatrix
    (n : ℕ) :
    ContDiffOn ℝ ∞
      (identitySpecialOrthogonalNorthPoleProductMatrix n)
      (identitySpecialOrthogonalNorthPoleProductDomainSet n) := by
  have hsection : ContDiffOn ℝ ∞
      (fun p : identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n) =>
        identitySpecialOrthogonalNorthPoleSectionMatrix n p.2)
      (identitySpecialOrthogonalNorthPoleProductDomainSet n) :=
    (contDiffOn_identitySpecialOrthogonalNorthPoleSectionMatrix n).comp
      contDiff_snd.contDiffOn (by
        rintro ⟨X, v⟩ ⟨hX, hv⟩
        exact hv)
  have hblock : ContDiffOn ℝ ∞
      (fun p : identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n) =>
        identitySpecialOrthogonalLowerBlockChartMatrix n p.1)
      (identitySpecialOrthogonalNorthPoleProductDomainSet n) :=
    (contDiffOn_identitySpecialOrthogonalLowerBlockChartMatrix n).comp
      contDiff_fst.contDiffOn (by
        rintro ⟨X, v⟩ ⟨hX, hv⟩
        exact hX)
  exact hsection.mul hblock

/-- The lower-rank group point represented by an exact native chart
coordinate. -/
noncomputable def identitySpecialOrthogonalLowerChartGroup
    (n : ℕ) (X : identitySpecialOrthogonalLowerChartTargetSet n) :
    specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) :=
  (specialFormPreservingSmoothRealIdentityChart
    (1 : Matrix (Fin n) (Fin n) ℚ)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero).symm X.1

theorem coe_identitySpecialOrthogonalLowerChartGroup
    (n : ℕ) (X : identitySpecialOrthogonalLowerChartTargetSet n) :
    (identitySpecialOrthogonalLowerChartGroup n X).1.1.1 =
      identitySpecialOrthogonalLowerInverseCoordinateMatrix n X.1 := by
  let F := (1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)
  have hF : F.IsSymm := by
    simp [F, Matrix.IsSymm]
  have hdet : F.det ≠ 0 := by
    simp [F]
  have hchar : ringChar ℝ ≠ 2 := by
    norm_num
  have htarget :
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero).target =
        Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
          F hF hdet hchar :=
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
      F hF hdet hchar 1
  let Xc : Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      F hF hdet hchar :=
    ⟨X.1, htarget ▸ X.2⟩
  change
    ((specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar 1).symm X.1).1.1.1 =
      (Matrix.symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar).symm
          (0, (Matrix.symmetricSkewAdjointOperatorKerContinuousLinearEquiv
            F hF).symm X.1)
  simpa [Xc] using
    coe_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_symm_apply
      F hF hdet hchar 1 Xc

end PositiveDefiniteIntegralLattice
