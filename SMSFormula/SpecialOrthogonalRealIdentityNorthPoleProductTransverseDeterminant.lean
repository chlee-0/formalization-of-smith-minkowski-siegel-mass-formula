import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductTangentClosure
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleConeDeterminant

/-!
# Transverse determinant of the identity north-pole product

This file computes the determinant of the transverse diagonal block in the
left-trivialized north-pole product derivative.  It adjoins one radial cone
direction at the fixed auxiliary radius `1 / 2`.  The resulting square map is
block diagonal after left trivialization, while its full determinant is
already known from the radial-cone calculation.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace PositiveDefiniteIntegralLattice

open Matrix Metric Set

/-- The transverse derivative in plain function coordinates on both sides. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  (identitySpecialOrthogonalNorthPoleProductTransverseDerivative
      n p).toLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin n => ℝ)).symm.toLinearEquiv.toLinearMap

@[simp]
theorem
    identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative_apply
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n))
    (f : Fin n → ℝ) :
    identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
        n p f =
      identitySpecialOrthogonalNorthPoleProductTransverseDerivative n p
        (WithLp.toLp 2 f) :=
  rfl

/-- The auxiliary cone point at radius `1 / 2`. -/
def identitySpecialOrthogonalNorthPoleProductHalfConePoint
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) × ℝ :=
  (p.2, (2 : ℝ)⁻¹)

theorem identitySpecialOrthogonalNorthPoleProductHalfConePoint_mem
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    identitySpecialOrthogonalNorthPoleProductHalfConePoint n p ∈
      identitySpecialOrthogonalNorthPoleConeDomainSet n := by
  refine ⟨hp.2, ?_⟩
  norm_num [identitySpecialOrthogonalNorthPoleProductHalfConePoint,
    inv_eq_one_div]

/-- Left-trivialize the square cone derivative by the represented product
matrix, all in plain function coordinates. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  (Matrix.toLin'
      (identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹).comp
    (identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n
      (identitySpecialOrthogonalNorthPoleProductHalfConePoint n p))

/-- The full left-trivialized half-cone determinant is the cone
Jacobian, since the represented product matrix has determinant one. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_det
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
          n p) =
      ((2 : ℝ)⁻¹) ^ n /
        identitySpecialOrthogonalNorthPoleFinalCoordinate p.2 := by
  rw [identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative,
    LinearMap.det_comp, LinearMap.det_toLin', Matrix.det_nonsing_inv,
    identitySpecialOrthogonalNorthPoleProductMatrix_det n hp,
    Ring.inverse_one, one_mul]
  exact identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_det
    n (identitySpecialOrthogonalNorthPoleProductHalfConePoint n p)
      (identitySpecialOrthogonalNorthPoleProductHalfConePoint_mem n hp)

/-- On a nonfinal source direction, the half-cone square derivative is one
half of the last column of the left-trivialized product derivative. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_nonfinal
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (f : Fin n → ℝ) (k : Fin (n + 1)) :
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
        n p (Fin.lastCases 0 f) k =
      (2 : ℝ)⁻¹ *
        identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
          n p (0, WithLp.toLp 2 f) k (Fin.last n) := by
  let h : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 f
  have hcone :=
    identitySpecialOrthogonalNorthPoleConeDerivative_apply_of_mem
      n
      (identitySpecialOrthogonalNorthPoleProductHalfConePoint_mem n hp)
      (h, 0)
  have hcolumn :=
    congrArg
      (fun L :
          (identitySpecialOrthogonalMappedTangent n ×
            EuclideanSpace ℝ (Fin n)) →L[ℝ]
              EuclideanSpace ℝ (Fin (n + 1)) =>
        L (0, h))
      (identitySpecialOrthogonalNorthPoleProductPointwiseDerivative_lastColumn
        n hp)
  have hsource :
      (identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv n).symm
          (Fin.lastCases 0 f) =
        (h, 0) := by
    ext i
    · simp [identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv,
        h]
    · simp [identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv]
  have hcoordinate :
      identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n
          (identitySpecialOrthogonalNorthPoleProductHalfConePoint n p)
          (Fin.lastCases 0 f) =
        fun i =>
          identitySpecialOrthogonalNorthPoleConeDerivative n
            (identitySpecialOrthogonalNorthPoleProductHalfConePoint n p)
            (h, 0) i := by
    change
      (PiLp.continuousLinearEquiv 2 ℝ
          (fun _ : Fin (n + 1) => ℝ))
        (identitySpecialOrthogonalNorthPoleConeDerivative n
          (identitySpecialOrthogonalNorthPoleProductHalfConePoint n p)
          ((identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv
            n).symm (Fin.lastCases 0 f))) =
        _
    rw [hsource]
    rfl
  change
    Matrix.toLin'
        (identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹
      (identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n
        (identitySpecialOrthogonalNorthPoleProductHalfConePoint n p)
        (Fin.lastCases 0 f)) k =
      _
  rw [hcoordinate]
  change
    ((identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ *ᵥ
      identitySpecialOrthogonalNorthPoleConeDerivative n
        (identitySpecialOrthogonalNorthPoleProductHalfConePoint n p)
        (h, 0)) k =
      _
  rw [hcone]
  simp only [zero_smul, add_zero]
  simp only [identitySpecialOrthogonalNorthPoleProductHalfConePoint]
  have hsmul :
      (((2 : ℝ)⁻¹ •
          identitySpecialOrthogonalNorthPoleInverseVectorDerivative
            n p.2 h).ofLp : Fin (n + 1) → ℝ) =
        (2 : ℝ)⁻¹ •
          (identitySpecialOrthogonalNorthPoleInverseVectorDerivative
            n p.2 h).ofLp := by
    rfl
  rw [hsmul]
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_apply]
  change
    (2 : ℝ)⁻¹ *
        (((identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ *ᵥ
          identitySpecialOrthogonalNorthPoleInverseVectorDerivative
            n p.2 h) k) =
      (2 : ℝ)⁻¹ *
        (((identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ *
          identitySpecialOrthogonalNorthPoleProductPointwiseDerivative
            n p (0, h)) k (Fin.last n))
  congr 1
  rw [Matrix.mul_apply]
  change
    ∑ x,
        (identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ k x *
          identitySpecialOrthogonalNorthPoleInverseVectorDerivative
            n p.2 h x =
      _
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  have hxcolumn := congrArg
    (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y x) hcolumn
  simpa [h] using hxcolumn.symm

/-- A skew-adjoint left-trivialized product derivative has zero final
diagonal entry. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_final_final
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (q : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
        n p q (Fin.last n) (Fin.last n) = 0 := by
  have hskew :=
    (LieAlgebra.Orthogonal.mem_so (Fin (n + 1)) ℝ
      (identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative
        n p q)).mp
      (identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_mem_tangent
        n hp q)
  have hentry := congrArg
    (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      M (Fin.last n) (Fin.last n)) hskew
  simp only [Matrix.transpose_apply, neg_apply] at hentry
  linarith

/-- On nonfinal inputs, the final output of the half-cone derivative
vanishes. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_nonfinal_last
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (f : Fin n → ℝ) :
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
        n p (Fin.lastCases 0 f) (Fin.last n) = 0 := by
  rw [
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_nonfinal
      n hp]
  rw [
    identitySpecialOrthogonalNorthPoleProductLeftTrivializedDerivative_final_final
      n hp]
  simp

/-- The auxiliary radial source direction maps to the final standard basis
vector after left trivialization. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_radial
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (k : Fin (n + 1)) :
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
        n p (Fin.lastCases 1 (fun _ => 0)) k =
      if k = Fin.last n then 1 else 0 := by
  have hsource :
      (identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv n).symm
          (Fin.lastCases 1 (fun _ => 0)) =
        (0, 1) := by
    ext i
    · simp [identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv]
    · simp [identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv]
  have hcone :=
    identitySpecialOrthogonalNorthPoleConeDerivative_apply_of_mem
      n
      (identitySpecialOrthogonalNorthPoleProductHalfConePoint_mem n hp)
      (0, 1)
  have hcoordinate :
      identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n
          (identitySpecialOrthogonalNorthPoleProductHalfConePoint n p)
          (Fin.lastCases 1 (fun _ => 0)) =
        (identitySpecialOrthogonalNorthPoleInverseVector n p.2).ofLp := by
    change
      (PiLp.continuousLinearEquiv 2 ℝ
          (fun _ : Fin (n + 1) => ℝ))
        (identitySpecialOrthogonalNorthPoleConeDerivative n
          (identitySpecialOrthogonalNorthPoleProductHalfConePoint n p)
          ((identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv
            n).symm (Fin.lastCases 1 (fun _ => 0)))) =
        _
    rw [hsource, hcone]
    simp only [identitySpecialOrthogonalNorthPoleProductHalfConePoint,
      map_zero, smul_zero, zero_add, one_smul]
    rfl
  change
    Matrix.toLin'
        (identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹
      (identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n
        (identitySpecialOrthogonalNorthPoleProductHalfConePoint n p)
        (Fin.lastCases 1 (fun _ => 0))) k =
      _
  rw [hcoordinate]
  change
    ((identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ *ᵥ
      (identitySpecialOrthogonalNorthPoleInverseVector n p.2).ofLp) k =
      _
  change
    (∑ x,
      (identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ k x *
        identitySpecialOrthogonalNorthPoleInverseVector n p.2 x) =
      _
  simp_rw [← identitySpecialOrthogonalNorthPoleProductMatrix_lastColumn
    n p.1 p.2]
  rw [← Matrix.mul_apply]
  have hinv :
      (identitySpecialOrthogonalNorthPoleProductMatrix n p)⁻¹ *
          identitySpecialOrthogonalNorthPoleProductMatrix n p =
        1 :=
    Matrix.nonsing_inv_mul _
      (by
        rw [identitySpecialOrthogonalNorthPoleProductMatrix_det n hp]
        exact isUnit_one)
  rw [hinv]
  rw [Matrix.one_apply]

/-- The nonfinal output block is one half of the transverse coordinate
derivative. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_nonfinal_cast
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n)
    (f : Fin n → ℝ) (i : Fin n) :
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
        n p (Fin.lastCases 0 f) i.castSucc =
      (2 : ℝ)⁻¹ *
        identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
          n p f i := by
  rw [
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_nonfinal
      n hp]
  rfl

/-- The block matrix of the left-trivialized half-cone derivative. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks
    ((2 : ℝ)⁻¹ •
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
        (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
          n p))
    0 0 1

/-- In standard coordinates the full auxiliary derivative is block diagonal. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHalfConeCoordinateMatrix
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin (n + 1)))
        (Pi.basisFun ℝ (Fin (n + 1)))
        (identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
          n p) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix n p) := by
  have hlastBasis :
      (Pi.basisFun ℝ (Fin (n + 1))) (Fin.last n) =
        Fin.lastCases 1 (fun _ : Fin n => 0) := by
    funext k
    cases k using Fin.lastCases <;> simp
  have hcastBasis (j : Fin n) :
      (Pi.basisFun ℝ (Fin (n + 1))) j.castSucc =
        Fin.lastCases 0 (Pi.single j 1) := by
    funext k
    cases k using Fin.lastCases <;> simp [Pi.single_apply]
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
          rw [hlastBasis,
            identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_radial
              n hp]
          simp [identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix]
      | cast j =>
          rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
          rw [hcastBasis,
            identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_nonfinal_last
              n hp]
          simp [identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix]
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
          rw [hlastBasis,
            identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_radial
              n hp]
          simp [identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix]
      | cast j =>
          rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
          rw [hcastBasis,
            identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_nonfinal_cast
              n hp]
          simp [identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix]

/-- The determinant of the block-diagonal half-cone matrix factors through
the transverse determinant. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix_det
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    (identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix n p).det =
      ((2 : ℝ)⁻¹) ^ n *
        LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
            n p) := by
  rw [identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul]
  rw [show
    (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
      (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
        n p)).det =
      LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
          n p) by
    exact LinearMap.det_toMatrix
      (Pi.basisFun ℝ (Fin n))
      (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
        n p)]
  simp

/-- The full auxiliary determinant is the half-radius power times the
transverse determinant. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_det_factor
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
          n p) =
      ((2 : ℝ)⁻¹) ^ n *
        LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
            n p) := by
  calc
    LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
          n p) =
        (LinearMap.toMatrix (Pi.basisFun ℝ (Fin (n + 1)))
          (Pi.basisFun ℝ (Fin (n + 1)))
          (identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
            n p)).det := by
      symm
      exact LinearMap.det_toMatrix
        (Pi.basisFun ℝ (Fin (n + 1)))
        (identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative
          n p)
    _ = (Matrix.reindex finSumFinEquiv finSumFinEquiv
          (identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix
            n p)).det := by
      rw [
        identitySpecialOrthogonalNorthPoleProductHalfConeCoordinateMatrix n hp]
    _ =
        (identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix n p).det :=
      Matrix.det_reindex_self finSumFinEquiv
        (identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix n p)
    _ = _ :=
      identitySpecialOrthogonalNorthPoleProductHalfConeBlockMatrix_det n p

/-- The transverse determinant is the reciprocal north-pole final
coordinate. In particular it is independent of the lower chart coordinate. -/
theorem
    identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative_det
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
          n p) =
      1 / identitySpecialOrthogonalNorthPoleFinalCoordinate p.2 := by
  have hfactor :=
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_det_factor
      n hp
  have hcone :=
    identitySpecialOrthogonalNorthPoleProductHalfConeLeftTrivializedDerivative_det
      n hp
  have heq :
      ((2 : ℝ)⁻¹) ^ n *
          LinearMap.det
            (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
              n p) =
        ((2 : ℝ)⁻¹) ^ n /
          identitySpecialOrthogonalNorthPoleFinalCoordinate p.2 :=
    hfactor.symm.trans hcone
  have hpow : ((2 : ℝ)⁻¹) ^ n ≠ 0 := by
    positivity
  rw [div_eq_mul_inv] at heq ⊢
  simp only [one_mul]
  exact mul_left_cancel₀ hpow heq

/-- Absolute transverse Jacobian in the north-pole coordinate. -/
theorem
    abs_identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative_det
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    |LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
          n p)| =
      1 / identitySpecialOrthogonalNorthPoleFinalCoordinate p.2 := by
  rw [
    identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative_det
      n hp,
    abs_of_pos]
  exact one_div_pos.mpr
    (identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hp.2)

/-- Literal inverse-square-root form of the transverse Jacobian. -/
theorem
    abs_identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative_det_eq_inv_sqrt
    (n : ℕ)
    {p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n) :
    |LinearMap.det
        (identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative
          n p)| =
      1 / Real.sqrt (1 - ‖p.2‖ ^ 2) := by
  simpa [identitySpecialOrthogonalNorthPoleFinalCoordinate] using
    abs_identitySpecialOrthogonalNorthPoleProductTransverseCoordinateDerivative_det
      n hp

end PositiveDefiniteIntegralLattice
