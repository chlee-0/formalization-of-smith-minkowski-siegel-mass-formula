import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductJacobianNormalization

/-!
# Pointwise derivative of the identity north-pole product

This file records the derivative of the lower-chart/north-pole product at an
arbitrary point of its exact domain.  It also left-trivializes that ambient
derivative and isolates the two diagonal blocks relevant to the eventual
product-density cocycle.

The mixed lower-to-transverse block remains implicit.  No determinant
factorization, measure comparison, fiber disintegration, or rank recurrence
is asserted here.
-/

open scoped Matrix Matrix.Norms.Operator ContDiff

noncomputable section

open Matrix Metric Set

namespace PositiveDefiniteIntegralLattice

/-- The derivative of the north-pole product matrix at an arbitrary product
coordinate, written by the product rule. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductPointwiseDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    (identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) →L[ℝ]
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  identitySpecialOrthogonalNorthPoleSectionMatrix n p.2 •
      ((fderiv ℝ
        (identitySpecialOrthogonalLowerBlockChartMatrix n) p.1).comp
        (ContinuousLinearMap.fst ℝ
          (identitySpecialOrthogonalMappedTangent n)
          (EuclideanSpace ℝ (Fin n)))) +
    MulOpposite.op
        (identitySpecialOrthogonalLowerBlockChartMatrix n p.1) •
      ((fderiv ℝ
        (identitySpecialOrthogonalNorthPoleSectionMatrix n) p.2).comp
        (ContinuousLinearMap.snd ℝ
          (identitySpecialOrthogonalMappedTangent n)
          (EuclideanSpace ℝ (Fin n))))

theorem
    identitySpecialOrthogonalNorthPoleProductPointwiseDerivative_apply
    (n : ℕ)
    (p q : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p q =
      fderiv ℝ (identitySpecialOrthogonalNorthPoleSectionMatrix n) p.2 q.2 *
          identitySpecialOrthogonalLowerBlockChartMatrix n p.1 +
        identitySpecialOrthogonalNorthPoleSectionMatrix n p.2 *
          fderiv ℝ (identitySpecialOrthogonalLowerBlockChartMatrix n) p.1
            q.1 := by
  simp [identitySpecialOrthogonalNorthPoleProductPointwiseDerivative,
    add_comm]

/-- The product-rule derivative is the actual derivative at every point of
the exact product domain. -/
theorem
    hasFDerivAt_identitySpecialOrthogonalNorthPoleProductMatrix_pointwise
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    HasFDerivAt
      (identitySpecialOrthogonalNorthPoleProductMatrix n)
      (identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p) p := by
  have hsection :
      HasFDerivAt
        (fun q : identitySpecialOrthogonalMappedTangent n ×
            EuclideanSpace ℝ (Fin n) =>
          identitySpecialOrthogonalNorthPoleSectionMatrix n q.2)
        ((fderiv ℝ
          (identitySpecialOrthogonalNorthPoleSectionMatrix n) p.2).comp
            (ContinuousLinearMap.snd ℝ
              (identitySpecialOrthogonalMappedTangent n)
              (EuclideanSpace ℝ (Fin n)))) p := by
    exact
      (((contDiffOn_identitySpecialOrthogonalNorthPoleSectionMatrix n).contDiffAt
        (Metric.isOpen_ball.mem_nhds hp.2)).differentiableAt (by simp)
        ).hasFDerivAt.comp p
          (ContinuousLinearMap.snd ℝ
            (identitySpecialOrthogonalMappedTangent n)
            (EuclideanSpace ℝ (Fin n))).hasFDerivAt
  have hblock :
      HasFDerivAt
        (fun q : identitySpecialOrthogonalMappedTangent n ×
            EuclideanSpace ℝ (Fin n) =>
          identitySpecialOrthogonalLowerBlockChartMatrix n q.1)
        ((fderiv ℝ
          (identitySpecialOrthogonalLowerBlockChartMatrix n) p.1).comp
            (ContinuousLinearMap.fst ℝ
              (identitySpecialOrthogonalMappedTangent n)
              (EuclideanSpace ℝ (Fin n)))) p := by
    exact
      (((contDiffOn_identitySpecialOrthogonalLowerBlockChartMatrix n).contDiffAt
        ((isOpen_identitySpecialOrthogonalLowerChartTargetSet n).mem_nhds
          hp.1)).differentiableAt (by simp)).hasFDerivAt.comp p
          (ContinuousLinearMap.fst ℝ
            (identitySpecialOrthogonalMappedTangent n)
            (EuclideanSpace ℝ (Fin n))).hasFDerivAt
  simpa only [
    identitySpecialOrthogonalNorthPoleProductMatrix,
    identitySpecialOrthogonalNorthPoleProductPointwiseDerivative] using
    hsection.mul' hblock

theorem
    fderiv_identitySpecialOrthogonalNorthPoleProductMatrix_pointwise
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    fderiv ℝ (identitySpecialOrthogonalNorthPoleProductMatrix n) p =
      identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p :=
  (hasFDerivAt_identitySpecialOrthogonalNorthPoleProductMatrix_pointwise
    n hp).fderiv

/-- The ambient continuous linear map extracting the complete final column. -/
def identitySpecialOrthogonalAmbientFullLastColumnLinearMap (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) where
  toFun A := WithLp.toLp 2 (fun i => A i (Fin.last n))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def
    identitySpecialOrthogonalAmbientFullLastColumnContinuousLinearMap
    (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  ⟨identitySpecialOrthogonalAmbientFullLastColumnLinearMap n,
    LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem
    identitySpecialOrthogonalAmbientFullLastColumnContinuousLinearMap_apply
    (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) :
    identitySpecialOrthogonalAmbientFullLastColumnContinuousLinearMap n A i =
      A i (Fin.last n) :=
  rfl

/-- The complete final-column block of the arbitrary product derivative is
exactly the derivative of the north-pole inverse vector. -/
theorem
    identitySpecialOrthogonalNorthPoleProductPointwiseDerivative_lastColumn
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    (identitySpecialOrthogonalAmbientFullLastColumnContinuousLinearMap n).comp
        (identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p) =
      (identitySpecialOrthogonalNorthPoleInverseVectorDerivative n p.2).comp
        (ContinuousLinearMap.snd ℝ
          (identitySpecialOrthogonalMappedTangent n)
          (EuclideanSpace ℝ (Fin n))) := by
  have hleft :
      HasFDerivAt
        (fun q : identitySpecialOrthogonalMappedTangent n ×
            EuclideanSpace ℝ (Fin n) =>
          identitySpecialOrthogonalAmbientFullLastColumnContinuousLinearMap n
            (identitySpecialOrthogonalNorthPoleProductMatrix n q))
        ((identitySpecialOrthogonalAmbientFullLastColumnContinuousLinearMap
          n).comp
          (identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p))
        p :=
    (identitySpecialOrthogonalAmbientFullLastColumnContinuousLinearMap n
      ).hasFDerivAt.comp p
      (hasFDerivAt_identitySpecialOrthogonalNorthPoleProductMatrix_pointwise
        n hp)
  have hinverse :
      HasFDerivAt
        (fun q : identitySpecialOrthogonalMappedTangent n ×
            EuclideanSpace ℝ (Fin n) =>
          identitySpecialOrthogonalNorthPoleInverseVector n q.2)
        ((identitySpecialOrthogonalNorthPoleInverseVectorDerivative n p.2).comp
          (ContinuousLinearMap.snd ℝ
            (identitySpecialOrthogonalMappedTangent n)
            (EuclideanSpace ℝ (Fin n)))) p :=
    ((hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleInverseVector
      hp.2).hasFDerivAt (Metric.isOpen_ball.mem_nhds hp.2)).comp p
        (ContinuousLinearMap.snd ℝ
          (identitySpecialOrthogonalMappedTangent n)
          (EuclideanSpace ℝ (Fin n))).hasFDerivAt
  apply hleft.unique
  convert hinverse using 1
  funext q
  ext i
  exact
    identitySpecialOrthogonalNorthPoleProductMatrix_lastColumn
      n q.1 q.2 i

/-- The left-trivialized arbitrary product derivative in ambient matrix
coordinates.  Its tangent-carrier closure is deliberately not bundled here. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    (identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) →L[ℝ]
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (ContinuousLinearMap.mulLeftRight ℝ
    (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ 1).comp
      (identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p)

theorem
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_apply
    (n : ℕ)
    (p q : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative n p q =
      (identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ *
        identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p q :=
  by
    change ((identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ *
      identitySpecialOrthogonalNorthPoleProductPointwiseDerivative n p q) * 1 = _
    exact mul_one _

/-- The moving derivative of the native lower identity inverse chart. -/
noncomputable def
    identitySpecialOrthogonalLowerChartMovingDerivative
    (n : ℕ) (X : identitySpecialOrthogonalMappedTangent n) :
    identitySpecialOrthogonalMappedTangent n →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ :=
  (ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ)
    (identitySpecialOrthogonalLowerInverseCoordinateMatrix n X)⁻¹ 1).comp
      (fderiv ℝ
        (identitySpecialOrthogonalLowerInverseCoordinateMatrix n) X)

theorem identitySpecialOrthogonalLowerChartMovingDerivative_apply
    (n : ℕ) (X H : identitySpecialOrthogonalMappedTangent n) :
    identitySpecialOrthogonalLowerChartMovingDerivative n X H =
      (identitySpecialOrthogonalLowerInverseCoordinateMatrix n X)⁻¹ *
        fderiv ℝ
          (identitySpecialOrthogonalLowerInverseCoordinateMatrix n) X H := by
  change ((identitySpecialOrthogonalLowerInverseCoordinateMatrix n X)⁻¹ *
    fderiv ℝ (identitySpecialOrthogonalLowerInverseCoordinateMatrix n) X H) * 1 = _
  exact mul_one _

/-- At every exact lower-chart coordinate, differentiating the ambient final
block is the zero-final-coordinate block embedding of the native derivative.
-/
theorem
    fderiv_identitySpecialOrthogonalLowerBlockChartMatrix_pointwise
    (n : ℕ)
    {X : identitySpecialOrthogonalMappedTangent n}
    (hX : X ∈ identitySpecialOrthogonalLowerChartTargetSet n) :
    fderiv ℝ (identitySpecialOrthogonalLowerBlockChartMatrix n) X =
      (identitySpecialOrthogonalAmbientBlockContinuousLinearMap n).comp
        (fderiv ℝ
          (identitySpecialOrthogonalLowerInverseCoordinateMatrix n) X) := by
  have hinverse :
      HasFDerivAt
        (identitySpecialOrthogonalLowerInverseCoordinateMatrix n)
        (fderiv ℝ
          (identitySpecialOrthogonalLowerInverseCoordinateMatrix n) X) X :=
    (((contDiffOn_identitySpecialOrthogonalLowerInverseCoordinateMatrix n
      ).contDiffAt
        ((isOpen_identitySpecialOrthogonalLowerChartTargetSet n).mem_nhds hX)
      ).differentiableAt (by simp)).hasFDerivAt
  exact
    ((hasFDerivAt_identitySpecialOrthogonalLastBlockMatrix n
      (identitySpecialOrthogonalLowerInverseCoordinateMatrix n X)).comp X
        hinverse).fderiv

/-- Final identity-block embedding commutes with nonsingular inversion. -/
theorem identitySpecialOrthogonalLastBlockMatrix_nonsing_inv
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) :
    (identitySpecialOrthogonalLastBlockMatrix n A)⁻¹ =
      identitySpecialOrthogonalLastBlockMatrix n A⁻¹ := by
  have hblock :
      IsUnit (identitySpecialOrthogonalLastBlockMatrix n A).det := by
    rw [identitySpecialOrthogonalLastBlockMatrix_det]
    exact hA
  have hright :
      identitySpecialOrthogonalLastBlockMatrix n A *
          identitySpecialOrthogonalLastBlockMatrix n A⁻¹ = 1 := by
    rw [← identitySpecialOrthogonalLastBlockMatrix_mul,
      Matrix.mul_nonsing_inv A hA,
      identitySpecialOrthogonalLastBlockMatrix_one]
  calc
    (identitySpecialOrthogonalLastBlockMatrix n A)⁻¹ =
        (identitySpecialOrthogonalLastBlockMatrix n A)⁻¹ * 1 := by
      rw [Matrix.mul_one]
    _ =
        (identitySpecialOrthogonalLastBlockMatrix n A)⁻¹ *
          (identitySpecialOrthogonalLastBlockMatrix n A *
            identitySpecialOrthogonalLastBlockMatrix n A⁻¹) := by
      rw [hright]
    _ =
        ((identitySpecialOrthogonalLastBlockMatrix n A)⁻¹ *
          identitySpecialOrthogonalLastBlockMatrix n A) *
            identitySpecialOrthogonalLastBlockMatrix n A⁻¹ := by
      rw [Matrix.mul_assoc]
    _ = identitySpecialOrthogonalLastBlockMatrix n A⁻¹ := by
      rw [Matrix.nonsing_inv_mul _ hblock, Matrix.one_mul]

/-- On a pure lower-fiber direction, left trivialization cancels the
north-pole section and leaves precisely the block embedding of the native
lower identity-chart moving derivative. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_fst
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (H : identitySpecialOrthogonalMappedTangent n) :
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
        n p (H, 0) =
      identitySpecialOrthogonalAmbientBlockContinuousLinearMap n
        (identitySpecialOrthogonalLowerChartMovingDerivative n p.1 H) := by
  let S := identitySpecialOrthogonalNorthPoleSectionMatrix n p.2
  let A := identitySpecialOrthogonalLowerInverseCoordinateMatrix n p.1
  let dA :=
    fderiv ℝ
      (identitySpecialOrthogonalLowerInverseCoordinateMatrix n) p.1 H
  have hSdet : IsUnit S.det := by
    rw [show S.det = 1 by
      exact identitySpecialOrthogonalNorthPoleSectionMatrix_det n p.2 hp.2]
    exact isUnit_one
  have hAdet : IsUnit A.det := by
    have hdet :
        (identitySpecialOrthogonalLowerInverseCoordinateMatrix n p.1).det =
          1 := by
      simpa [identitySpecialOrthogonalLowerInverseCoordinateMatrix] using
        det_specialFormPreservingSmoothRealInverseCoordinateMatrix
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm identityRationalForm_det_ne_zero
          (1 : specialFormPreservingMatrixSubgroup
            ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)))
          ⟨p.1, hp.1⟩
    rw [show A.det = 1 by exact hdet]
    exact isUnit_one
  have hblockDerivative :
      fderiv ℝ
          (identitySpecialOrthogonalLowerBlockChartMatrix n) p.1 H =
        identitySpecialOrthogonalAmbientBlockContinuousLinearMap n dA := by
    rw [
      fderiv_identitySpecialOrthogonalLowerBlockChartMatrix_pointwise n hp.1]
    rfl
  rw [
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_apply,
    identitySpecialOrthogonalNorthPoleProductPointwiseDerivative_apply,
    map_zero, zero_mul, zero_add, hblockDerivative,
    identitySpecialOrthogonalNorthPoleProductMatrix]
  simp only [identitySpecialOrthogonalLowerBlockChartMatrix,
    identitySpecialOrthogonalAmbientBlockContinuousLinearMap_apply,
    identitySpecialOrthogonalLowerChartMovingDerivative_apply]
  rw [Matrix.mul_inv_rev, Matrix.mul_assoc,
    ← Matrix.mul_assoc
      (identitySpecialOrthogonalNorthPoleSectionMatrix n p.2)⁻¹
      (identitySpecialOrthogonalNorthPoleSectionMatrix n p.2),
    Matrix.nonsing_inv_mul _ (by simpa [S] using hSdet), Matrix.one_mul]
  rw [identitySpecialOrthogonalLastBlockMatrix_nonsing_inv n
    (identitySpecialOrthogonalLowerInverseCoordinateMatrix n p.1)
    (by simpa [A] using hAdet)]
  ext i j
  cases i using Fin.lastCases <;>
    cases j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc,
      identitySpecialOrthogonalSkewBlockMatrix, dA]

/-- Ambient upper-left-block extraction as a continuous linear map. -/
def identitySpecialOrthogonalAmbientUpperLeftLinearMap (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →ₗ[ℝ]
      Matrix (Fin n) (Fin n) ℝ where
  toFun A := identitySpecialOrthogonalUpperLeftBlock n A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def
    identitySpecialOrthogonalAmbientUpperLeftContinuousLinearMap
    (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ :=
  ⟨identitySpecialOrthogonalAmbientUpperLeftLinearMap n,
    LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem identitySpecialOrthogonalAmbientUpperLeftContinuousLinearMap_apply
    (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    identitySpecialOrthogonalAmbientUpperLeftContinuousLinearMap n A =
      identitySpecialOrthogonalUpperLeftBlock n A :=
  rfl

/-- Ambient matrix block extraction.  On the identity skew-adjoint tangent
carrier this is the underlying pair of the tangent split. -/
def identitySpecialOrthogonalAmbientTangentSplitLinearMap (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →ₗ[ℝ]
      Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) where
  toFun A :=
    (identitySpecialOrthogonalUpperLeftBlock n A,
      fun i => A i.castSucc (Fin.last n))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def
    identitySpecialOrthogonalAmbientTangentSplitContinuousLinearMap
    (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) :=
  ⟨identitySpecialOrthogonalAmbientTangentSplitLinearMap n,
    LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem identitySpecialOrthogonalAmbientTangentSplitContinuousLinearMap_apply
    (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    identitySpecialOrthogonalAmbientTangentSplitContinuousLinearMap n A =
      (identitySpecialOrthogonalUpperLeftBlock n A,
        fun i => A i.castSucc (Fin.last n)) :=
  rfl

theorem identitySpecialOrthogonalAmbientTangentSplit_eq_tangentSplit
    (n : ℕ) (X : identitySpecialOrthogonalTangent (n + 1)) :
    identitySpecialOrthogonalAmbientTangentSplitContinuousLinearMap n X.1 =
      ((identitySpecialOrthogonalTangentContinuousLinearEquiv n X).1.1,
        (identitySpecialOrthogonalTangentContinuousLinearEquiv n X).2) :=
  rfl

@[simp]
theorem
    identitySpecialOrthogonalAmbientLastColumnContinuousLinearMap_apply
    (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n) :
    identitySpecialOrthogonalAmbientLastColumnContinuousLinearMap n A i =
      A i.castSucc (Fin.last n) :=
  rfl

/-- Injection of a transverse direction into the product source. -/
def identitySpecialOrthogonalNorthPoleProductSndInjectionLinearMap
    (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n) where
  toFun h := (0, h)
  map_add' h k := by
    ext <;> simp
  map_smul' c h := by
    ext <;> simp

noncomputable def
    identitySpecialOrthogonalNorthPoleProductSndInjectionContinuousLinearMap
    (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ]
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n) :=
  ⟨identitySpecialOrthogonalNorthPoleProductSndInjectionLinearMap n,
    LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem
    identitySpecialOrthogonalNorthPoleProductSndInjectionContinuousLinearMap_apply
    (n : ℕ) (h : EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleProductSndInjectionContinuousLinearMap
        n h = (0, h) :=
  by
    ext <;> simp [
      identitySpecialOrthogonalNorthPoleProductSndInjectionContinuousLinearMap,
      identitySpecialOrthogonalNorthPoleProductSndInjectionLinearMap]

/-- The lower-row mixed block of the left-trivialized product derivative.
It is left unevaluated. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductMixedDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (identitySpecialOrthogonalAmbientUpperLeftContinuousLinearMap n).comp
    ((identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
      n p).comp
      (identitySpecialOrthogonalNorthPoleProductSndInjectionContinuousLinearMap
        n))

/-- The transverse diagonal block of the left-trivialized product
derivative. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductTransverseDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ) :=
  (identitySpecialOrthogonalAmbientLastColumnContinuousLinearMap n).comp
    ((identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
      n p).comp
      (identitySpecialOrthogonalNorthPoleProductSndInjectionContinuousLinearMap
        n))

/-- The transverse block is the nonfinal part of the represented inverse
matrix applied to the derivative of the north-pole inverse vector. -/
theorem
    identitySpecialOrthogonalNorthPoleProductTransverseDerivative_apply
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (h : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    identitySpecialOrthogonalNorthPoleProductTransverseDerivative n p h i =
      ∑ k : Fin (n + 1),
        (identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹
            i.castSucc k *
          identitySpecialOrthogonalNorthPoleInverseVectorDerivative
            n p.2 h k := by
  have hcolumn :=
    congrArg
      (fun L :
          (identitySpecialOrthogonalMappedTangent n ×
            EuclideanSpace ℝ (Fin n)) →L[ℝ]
              EuclideanSpace ℝ (Fin (n + 1)) =>
        L (0, h))
      (identitySpecialOrthogonalNorthPoleProductPointwiseDerivative_lastColumn
        n hp)
  simp only [
    identitySpecialOrthogonalNorthPoleProductTransverseDerivative,
    ContinuousLinearMap.comp_apply,
    identitySpecialOrthogonalNorthPoleProductSndInjectionContinuousLinearMap_apply,
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_apply]
  change
    ((identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ *
      identitySpecialOrthogonalNorthPoleProductPointwiseDerivative
        n p (0, h)) i.castSucc (Fin.last n) = _
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hkcolumn := congrArg
    (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x k) hcolumn
  simpa using hkcolumn

/-- After ambient block extraction, the arbitrary left-trivialized derivative
is block triangular: the pure lower block is the lower moving
derivative, the transverse diagonal block is explicit above, and the mixed
block is left unevaluated. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLeftTrivialized_block_decomposition
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (H : identitySpecialOrthogonalMappedTangent n)
    (h : EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalAmbientTangentSplitContinuousLinearMap n
        (identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
          n p (H, h)) =
      (identitySpecialOrthogonalLowerChartMovingDerivative n p.1 H +
          identitySpecialOrthogonalNorthPoleProductMixedDerivative n p h,
        identitySpecialOrthogonalNorthPoleProductTransverseDerivative
          n p h) := by
  have hdecomp :
      (H, h) =
        (H, (0 : EuclideanSpace ℝ (Fin n))) + (0, h) := by
    ext <;> simp
  rw [hdecomp, map_add, map_add,
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_fst
      n hp H]
  apply Prod.ext
  · simp only [Prod.fst_add,
      identitySpecialOrthogonalAmbientTangentSplitContinuousLinearMap_apply,
      identitySpecialOrthogonalNorthPoleProductMixedDerivative,
      ContinuousLinearMap.comp_apply,
      identitySpecialOrthogonalNorthPoleProductSndInjectionContinuousLinearMap_apply,
      identitySpecialOrthogonalAmbientUpperLeftContinuousLinearMap_apply]
    congr 1
    ext i j
    simp [identitySpecialOrthogonalUpperLeftBlock]
  · funext i
    simp [identitySpecialOrthogonalNorthPoleProductTransverseDerivative]

end PositiveDefiniteIntegralLattice
