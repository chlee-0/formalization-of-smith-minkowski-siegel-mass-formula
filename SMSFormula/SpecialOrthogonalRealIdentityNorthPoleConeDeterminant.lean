import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleCone

/-!
# Determinant of the identity north-pole radial cone

This module puts the cone derivative in standard product/function coordinates,
computes its block matrix, and evaluates its determinant. It does not apply
nonlinear change of variables or identify the sphere-coordinate measure.
-/

open scoped Matrix
noncomputable section

open Metric Set

namespace PositiveDefiniteIntegralLattice

def identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₗ[ℝ]
      (Fin (n + 1) → ℝ) where
  toFun p := Fin.lastCases p.2 (fun i => p.1 i)
  invFun f :=
    (WithLp.toLp 2 (fun i : Fin n => f i.castSucc), f (Fin.last n))
  left_inv p := by
    ext i
    · simp
    · simp
  right_inv f := by
    funext i
    cases i using Fin.lastCases <;> simp
  map_add' p q := by
    funext i
    cases i using Fin.lastCases <;> simp
  map_smul' c p := by
    funext i
    cases i using Fin.lastCases <;> simp

noncomputable def identitySpecialOrthogonalNorthPoleConeCoordinateDerivative
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (n + 1) => ℝ)).toLinearEquiv.toLinearMap.comp
    ((identitySpecialOrthogonalNorthPoleConeDerivative n p).toLinearMap.comp
      (identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv n).symm.toLinearMap)

theorem identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_apply_castSucc
    (n : ℕ) {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n)
    (f : Fin (n + 1) → ℝ) (i : Fin n) :
    identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n p f i.castSucc =
      p.2 * f i.castSucc + f (Fin.last n) * p.1 i := by
  change
    identitySpecialOrthogonalNorthPoleConeDerivative n p
        (WithLp.toLp 2 (fun j : Fin n => f j.castSucc), f (Fin.last n))
        i.castSucc =
      _
  rw [
    identitySpecialOrthogonalNorthPoleConeDerivative_apply_castSucc_of_mem n hp]

theorem identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_apply_last
    (n : ℕ) {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n)
    (f : Fin (n + 1) → ℝ) :
    identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n p f (Fin.last n) =
      p.2 *
          (-(∑ i : Fin n, p.1 i * f i.castSucc) /
            identitySpecialOrthogonalNorthPoleFinalCoordinate p.1) +
        f (Fin.last n) *
          identitySpecialOrthogonalNorthPoleFinalCoordinate p.1 := by
  change
    identitySpecialOrthogonalNorthPoleConeDerivative n p
        (WithLp.toLp 2 (fun j : Fin n => f j.castSucc), f (Fin.last n))
        (Fin.last n) =
      _
  rw [identitySpecialOrthogonalNorthPoleConeDerivative_apply_last_of_mem n hp]
  have hinner :
      inner ℝ p.1 (WithLp.toLp 2 (fun j : Fin n => f j.castSucc)) =
        ∑ i : Fin n, p.1 i * f i.castSucc := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simp
    exact mul_comm _ _
  rw [hinner]

def identitySpecialOrthogonalNorthPoleConeBlockMatrix (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks
    (r • (1 : Matrix (Fin n) (Fin n) ℝ))
    (fun i _ => v i)
    (fun _ j =>
      -r * v j /
        identitySpecialOrthogonalNorthPoleFinalCoordinate v)
    (fun _ _ =>
      identitySpecialOrthogonalNorthPoleFinalCoordinate v)

theorem identitySpecialOrthogonalNorthPoleConeBlockMatrix_det
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hr : 0 < r) :
    (identitySpecialOrthogonalNorthPoleConeBlockMatrix n v r).det =
      r ^ n /
        identitySpecialOrthogonalNorthPoleFinalCoordinate v := by
  let t := identitySpecialOrthogonalNorthPoleFinalCoordinate v
  let A : Matrix (Fin n) (Fin n) ℝ := r • 1
  let B : Matrix (Fin n) (Fin 1) ℝ := fun i _ => v i
  let C : Matrix (Fin 1) (Fin n) ℝ := fun _ j => -r * v j / t
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => t
  have ht : 0 < t :=
    identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hv
  letI : Invertible r := invertibleOfNonzero hr.ne'
  have hinvr : ⅟r = r⁻¹ := invOf_eq_right_inv (mul_inv_cancel₀ hr.ne')
  have hdetA : IsUnit A.det := by
    have hpow : r ^ n ≠ 0 := pow_ne_zero n hr.ne'
    simpa [A, Matrix.det_smul] using (isUnit_iff_ne_zero.mpr hpow)
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hdetA
  have hone_inv :
      (1 : Matrix (Fin n) (Fin n) ℝ)⁻¹ = 1 :=
    Matrix.inv_eq_right_inv (by simp)
  have hschur :
      D - C * ⅟A * B = fun _ _ => t⁻¹ := by
    rw [Matrix.invOf_eq_nonsing_inv]
    rw [show A⁻¹ = r⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) by
      change (r • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = r⁻¹ • 1
      rw [Matrix.inv_smul 1 r (by simp), hinvr, hone_inv]]
    ext i j
    fin_cases i
    fin_cases j
    simp [D, C, B, Matrix.mul_apply]
    have hsumsq : (∑ x : Fin n, v x * v x) = ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Real.norm_eq_abs, sq_abs, pow_two]
    have hsum :
        (∑ j : Fin n, -(r * v j) / t * v j) =
          (-(r / t)) * ∑ j : Fin n, v j * v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum, hsumsq]
    have ht_sq : t ^ 2 = 1 - ‖v‖ ^ 2 := by
      have harg : 0 ≤ 1 - ‖v‖ ^ 2 := by
        have hsqrt : 0 < Real.sqrt (1 - ‖v‖ ^ 2) := by
          simpa [t, identitySpecialOrthogonalNorthPoleFinalCoordinate] using ht
        exact (Real.sqrt_pos.mp hsqrt).le
      simpa [t, identitySpecialOrthogonalNorthPoleFinalCoordinate] using
        Real.sq_sqrt harg
    field_simp [ht.ne', hr.ne']
    nlinarith
  rw [identitySpecialOrthogonalNorthPoleConeBlockMatrix, show
    Matrix.fromBlocks
        (r • (1 : Matrix (Fin n) (Fin n) ℝ))
        (fun i _ => v i)
        (fun _ j => -r * v j /
          identitySpecialOrthogonalNorthPoleFinalCoordinate v)
        (fun _ _ => identitySpecialOrthogonalNorthPoleFinalCoordinate v) =
      Matrix.fromBlocks A B C D by rfl]
  rw [Matrix.det_fromBlocks₁₁, hschur]
  rw [show A.det = r ^ n by simp [A]]
  rw [Matrix.det_fin_one]
  simp [t, div_eq_mul_inv]

theorem identitySpecialOrthogonalNorthPoleConeCoordinateMatrix
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ)
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin (n + 1)))
        (Pi.basisFun ℝ (Fin (n + 1)))
        (identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n p) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (identitySpecialOrthogonalNorthPoleConeBlockMatrix n p.1 p.2) := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
          simp [identitySpecialOrthogonalNorthPoleConeBlockMatrix,
            identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_apply_last n hp]
      | cast j =>
          rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
          simp [identitySpecialOrthogonalNorthPoleConeBlockMatrix,
            identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_apply_last n hp,
            Pi.single_apply]
          ring
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
          simp [identitySpecialOrthogonalNorthPoleConeBlockMatrix,
            identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_apply_castSucc n hp]
      | cast j =>
          rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
          simp [identitySpecialOrthogonalNorthPoleConeBlockMatrix,
            identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_apply_castSucc n hp,
            Matrix.one_apply, Pi.single_apply]

theorem identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_det
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ)
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n) :
    LinearMap.det (identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n p) =
      p.2 ^ n /
        identitySpecialOrthogonalNorthPoleFinalCoordinate p.1 := by
  calc
    LinearMap.det (identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n p) =
        (LinearMap.toMatrix (Pi.basisFun ℝ (Fin (n + 1)))
          (Pi.basisFun ℝ (Fin (n + 1)))
          (identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n p)).det := by
      symm
      exact LinearMap.det_toMatrix
        (Pi.basisFun ℝ (Fin (n + 1)))
        (identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n p)
    _ = (Matrix.reindex finSumFinEquiv finSumFinEquiv
          (identitySpecialOrthogonalNorthPoleConeBlockMatrix n p.1 p.2)).det := by
      rw [identitySpecialOrthogonalNorthPoleConeCoordinateMatrix n p hp]
    _ = (identitySpecialOrthogonalNorthPoleConeBlockMatrix n p.1 p.2).det :=
      Matrix.det_reindex_self finSumFinEquiv
        (identitySpecialOrthogonalNorthPoleConeBlockMatrix n p.1 p.2)
    _ = p.2 ^ n /
        identitySpecialOrthogonalNorthPoleFinalCoordinate p.1 :=
      identitySpecialOrthogonalNorthPoleConeBlockMatrix_det n p.1 p.2 hp.1 hp.2.1

theorem abs_identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_det
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ)
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n) :
    |LinearMap.det (identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n p)| =
      p.2 ^ n /
        identitySpecialOrthogonalNorthPoleFinalCoordinate p.1 := by
  rw [identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_det n p hp]
  rw [abs_of_pos]
  exact div_pos (pow_pos hp.2.1 n)
    (identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hp.1)

end PositiveDefiniteIntegralLattice
