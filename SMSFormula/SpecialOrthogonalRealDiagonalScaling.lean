import SMSFormula.SpecialOrthogonalRealCongruence

/-!
# Real scaling from a positive rational diagonal form to the identity

The square-root scaling used here is real, not rational.  It is kept separate
from rational congruence so that the rational differential-basis
normalization remains visible.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The real inverse-square-root entries which normalize a positive rational
diagonal form. -/
def positiveDiagonalRealScalingEntries
    (d : Fin n → ℚ) : Fin n → ℝ :=
  fun i => (Real.sqrt (d i : ℝ))⁻¹

/-- The underlying real diagonal scaling matrix. -/
def positiveDiagonalRealScalingMatrix
    (d : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (positiveDiagonalRealScalingEntries d)

/-- Every inverse-square-root scaling entry is nonzero. -/
theorem positiveDiagonalRealScalingEntries_ne_zero
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) (i : Fin n) :
    positiveDiagonalRealScalingEntries d i ≠ 0 := by
  apply inv_ne_zero
  apply Real.sqrt_ne_zero'.mpr
  exact_mod_cast hd i

/-- The diagonal scaling matrix has nonzero determinant. -/
theorem positiveDiagonalRealScalingMatrix_det_ne_zero
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    (positiveDiagonalRealScalingMatrix d).det ≠ 0 := by
  rw [positiveDiagonalRealScalingMatrix, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    positiveDiagonalRealScalingEntries_ne_zero d hd i

/-- The inverse-square-root diagonal scaling as a real matrix unit. -/
def positiveDiagonalRealScalingUnit
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    GL (Fin n) ℝ :=
  Matrix.GeneralLinearGroup.mk''
    (positiveDiagonalRealScalingMatrix d)
    (isUnit_iff_ne_zero.mpr
      (positiveDiagonalRealScalingMatrix_det_ne_zero d hd))

@[simp]
theorem coe_positiveDiagonalRealScalingUnit
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    (positiveDiagonalRealScalingUnit d hd :
      Matrix (Fin n) (Fin n) ℝ) =
        positiveDiagonalRealScalingMatrix d :=
  rfl

/-- Scalar inverse-square-root normalization. -/
theorem inv_sqrt_mul_self_mul_inv_sqrt
    {x : ℝ} (hx : 0 < x) :
    (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = 1 := by
  have hsqrt_ne : Real.sqrt x ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hx
  have hsqrt_sq : Real.sqrt x * Real.sqrt x = x := by
    simpa [pow_two] using Real.sq_sqrt hx.le
  calc
    (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ =
        (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) *
          (Real.sqrt x)⁻¹ := by rw [hsqrt_sq]
    _ = ((Real.sqrt x)⁻¹ * Real.sqrt x) *
          (Real.sqrt x * (Real.sqrt x)⁻¹) := by ring
    _ = 1 := by
      rw [inv_mul_cancel₀ hsqrt_ne, mul_inv_cancel₀ hsqrt_ne, one_mul]

/-- The real square-root scaling carries the positive rational diagonal form
exactly to the identity matrix. -/
theorem positiveDiagonalRealScaling_congruence
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    (positiveDiagonalRealScalingUnit d hd :
        Matrix (Fin n) (Fin n) ℝ)ᵀ *
        (Matrix.diagonal d).map (algebraMap ℚ ℝ) *
        (positiveDiagonalRealScalingUnit d hd :
          Matrix (Fin n) (Fin n) ℝ) =
      1 := by
  have hnormalize (i : Fin n) :
      positiveDiagonalRealScalingEntries d i * (d i : ℝ) *
          positiveDiagonalRealScalingEntries d i = 1 := by
    exact inv_sqrt_mul_self_mul_inv_sqrt
      (show 0 < (d i : ℝ) by exact_mod_cast hd i)
  simp only [coe_positiveDiagonalRealScalingUnit,
    positiveDiagonalRealScalingMatrix]
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using hnormalize i
  · simp [hij]

end PositiveDefiniteIntegralLattice

namespace Matrix

variable {n : ℕ}

/-- Real matrix congruence transports the corresponding skew-adjoint tangent
spaces by conjugation. The target form is supplied explicitly so that this
also applies to genuinely real changes of basis. -/
def skewAdjointRealFormCongruenceLinearEquiv
    (F F' : Matrix (Fin n) (Fin n) ℝ) (U : GL (Fin n) ℝ)
    (hU : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
      (U : Matrix (Fin n) (Fin n) ℝ) = F') :
    (skewAdjointMatricesLieSubalgebra F).toSubmodule ≃ₗ[ℝ]
      (skewAdjointMatricesLieSubalgebra F').toSubmodule where
  toFun X := by
    refine ⟨(U⁻¹ : Matrix (Fin n) (Fin n) ℝ) * X.1 *
      (U : Matrix (Fin n) (Fin n) ℝ), ?_⟩
    rw [LieSubalgebra.mem_toSubmodule,
      mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_neg]
    rw [← hU]
    have hX := X.property
    rw [LieSubalgebra.mem_toSubmodule,
      mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule] at hX
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_neg] at hX
    have hUU :
        (U : Matrix (Fin n) (Fin n) ℝ) *
            (U⁻¹ : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hUiTUT :
        (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)ᵀ *
            (U : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hUU, Matrix.transpose_one]
    have hrhs :
        ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
              (U : Matrix (Fin n) (Fin n) ℝ)) *
            ((U⁻¹ : Matrix (Fin n) (Fin n) ℝ) * X.1 *
              (U : Matrix (Fin n) (Fin n) ℝ)) =
          (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (F * X.1) *
            (U : Matrix (Fin n) (Fin n) ℝ) := by
      calc
        _ = (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
              ((U : Matrix (Fin n) (Fin n) ℝ) *
                (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)) * X.1 *
              (U : Matrix (Fin n) (Fin n) ℝ) := by noncomm_ring
        _ = _ := by rw [hUU]; simp [Matrix.mul_assoc]
    calc
      ((U⁻¹ : Matrix (Fin n) (Fin n) ℝ) * X.1 *
          (U : Matrix (Fin n) (Fin n) ℝ))ᵀ *
          ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
            (U : Matrix (Fin n) (Fin n) ℝ)) =
        (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * X.1ᵀ *
          ((U⁻¹ : Matrix (Fin n) (Fin n) ℝ)ᵀ *
            (U : Matrix (Fin n) (Fin n) ℝ)ᵀ) * F *
          (U : Matrix (Fin n) (Fin n) ℝ) := by
            simp only [Matrix.transpose_mul]
            noncomm_ring
      _ = (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (X.1ᵀ * F) *
          (U : Matrix (Fin n) (Fin n) ℝ) := by
            rw [hUiTUT]
            simp [Matrix.mul_assoc]
      _ = (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (-(F * X.1)) *
          (U : Matrix (Fin n) (Fin n) ℝ) := by rw [hX]
      _ = -(((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
          (U : Matrix (Fin n) (Fin n) ℝ)) *
        ((U⁻¹ : Matrix (Fin n) (Fin n) ℝ) * X.1 *
          (U : Matrix (Fin n) (Fin n) ℝ))) := by rw [hrhs]; simp
  invFun Y := by
    refine ⟨(U : Matrix (Fin n) (Fin n) ℝ) * Y.1 *
      (U⁻¹ : Matrix (Fin n) (Fin n) ℝ), ?_⟩
    rw [LieSubalgebra.mem_toSubmodule,
      mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_neg]
    have hY := Y.property
    rw [LieSubalgebra.mem_toSubmodule,
      mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule] at hY
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_neg] at hY
    have hY' :
        Y.1ᵀ * ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
            (U : Matrix (Fin n) (Fin n) ℝ)) =
          -(((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
            (U : Matrix (Fin n) (Fin n) ℝ)) * Y.1) := by
      rw [hU]
      exact hY
    simp only [Matrix.mul_assoc] at hY'
    have hUiU :
        (U⁻¹ : Matrix (Fin n) (Fin n) ℝ) *
            (U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hUU :
        (U : Matrix (Fin n) (Fin n) ℝ) *
            (U⁻¹ : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hUiTUT :
        (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)ᵀ *
            (U : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hUU, Matrix.transpose_one]
    have hcore :
        Y.1ᵀ * ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F) =
          -((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
            (F * ((U : Matrix (Fin n) (Fin n) ℝ) * Y.1 *
              (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)))) := by
      calc
        Y.1ᵀ * ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F) =
            (Y.1ᵀ * ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
              (F * (U : Matrix (Fin n) (Fin n) ℝ)))) *
                (U⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
          calc
            _ = (Y.1ᵀ * ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F)) *
                ((U : Matrix (Fin n) (Fin n) ℝ) *
                  (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)) := by
                    rw [hUU]
                    simp
            _ = _ := by noncomm_ring
        _ = -(((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
              (F * ((U : Matrix (Fin n) (Fin n) ℝ) * Y.1))) *
                (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)) := by
                  rw [hY']
                  simp [Matrix.mul_assoc]
        _ = _ := by simp [Matrix.mul_assoc]
    calc
      ((U : Matrix (Fin n) (Fin n) ℝ) * Y.1 *
          (U⁻¹ : Matrix (Fin n) (Fin n) ℝ))ᵀ * F =
        (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          (Y.1ᵀ * ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F)) := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ =
        (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          (-((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
            (F * ((U : Matrix (Fin n) (Fin n) ℝ) * Y.1 *
              (U⁻¹ : Matrix (Fin n) (Fin n) ℝ))))) := by rw [hcore]
      _ = -(F * ((U : Matrix (Fin n) (Fin n) ℝ) * Y.1 *
          (U⁻¹ : Matrix (Fin n) (Fin n) ℝ))) := by
            simp only [Matrix.mul_neg, Matrix.mul_assoc]
            rw [← Matrix.mul_assoc
              (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)ᵀ
              (U : Matrix (Fin n) (Fin n) ℝ)ᵀ, hUiTUT,
              Matrix.one_mul]
  left_inv X := by
    apply Subtype.ext
    have hUU :
        (U : Matrix (Fin n) (Fin n) ℝ) *
            (U⁻¹ : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    calc
      (U : Matrix (Fin n) (Fin n) ℝ) *
          ((U⁻¹ : Matrix (Fin n) (Fin n) ℝ) * X.1 *
            (U : Matrix (Fin n) (Fin n) ℝ)) *
          (U⁻¹ : Matrix (Fin n) (Fin n) ℝ) =
        ((U : Matrix (Fin n) (Fin n) ℝ) *
          (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)) * X.1 *
          ((U : Matrix (Fin n) (Fin n) ℝ) *
            (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)) := by noncomm_ring
      _ = X.1 := by rw [hUU]; simp
  right_inv Y := by
    apply Subtype.ext
    have hUiU :
        (U⁻¹ : Matrix (Fin n) (Fin n) ℝ) *
            (U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    calc
      (U⁻¹ : Matrix (Fin n) (Fin n) ℝ) *
          ((U : Matrix (Fin n) (Fin n) ℝ) * Y.1 *
            (U⁻¹ : Matrix (Fin n) (Fin n) ℝ)) *
          (U : Matrix (Fin n) (Fin n) ℝ) =
        ((U⁻¹ : Matrix (Fin n) (Fin n) ℝ) *
          (U : Matrix (Fin n) (Fin n) ℝ)) * Y.1 *
          ((U⁻¹ : Matrix (Fin n) (Fin n) ℝ) *
            (U : Matrix (Fin n) (Fin n) ℝ)) := by noncomm_ring
      _ = Y.1 := by rw [hUiU]; simp
  map_add' X Y := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by
    apply Subtype.ext
    simp

/-- The real skew-adjoint congruence equivalence is continuous in finite
dimension. -/
def skewAdjointRealFormCongruenceContinuousLinearEquiv
    (F F' : Matrix (Fin n) (Fin n) ℝ) (U : GL (Fin n) ℝ)
    (hU : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
      (U : Matrix (Fin n) (Fin n) ℝ) = F') :
    (skewAdjointMatricesLieSubalgebra F).toSubmodule ≃L[ℝ]
      (skewAdjointMatricesLieSubalgebra F').toSubmodule :=
  (skewAdjointRealFormCongruenceLinearEquiv F F' U hU)
    |>.toContinuousLinearEquiv

@[simp]
theorem coe_skewAdjointRealFormCongruenceContinuousLinearEquiv_apply
    (F F' : Matrix (Fin n) (Fin n) ℝ) (U : GL (Fin n) ℝ)
    (hU : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
      (U : Matrix (Fin n) (Fin n) ℝ) = F')
    (X : (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
    (skewAdjointRealFormCongruenceContinuousLinearEquiv F F' U hU X :
      Matrix (Fin n) (Fin n) ℝ) =
      (U⁻¹ : Matrix (Fin n) (Fin n) ℝ) * X.1 *
        (U : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

@[simp]
theorem coe_skewAdjointRealFormCongruenceContinuousLinearEquiv_symm_apply
    (F F' : Matrix (Fin n) (Fin n) ℝ) (U : GL (Fin n) ℝ)
    (hU : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
      (U : Matrix (Fin n) (Fin n) ℝ) = F')
    (Y : (skewAdjointMatricesLieSubalgebra F').toSubmodule) :
    ((skewAdjointRealFormCongruenceContinuousLinearEquiv
      F F' U hU).symm Y : Matrix (Fin n) (Fin n) ℝ) =
      (U : Matrix (Fin n) (Fin n) ℝ) * Y.1 *
        (U⁻¹ : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance positiveDiagonalScalingTargetMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance positiveDiagonalScalingTargetBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- Conjugation by a real matrix unit identifies the real special-orthogonal
groups of explicitly congruent forms. -/
def specialFormPreservingRealFormCongruenceContinuousMulEquiv
    (F F' : Matrix (Fin n) (Fin n) ℝ) (U : GL (Fin n) ℝ)
    (hU : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
      (U : Matrix (Fin n) (Fin n) ℝ) = F') :
    specialFormPreservingMatrixSubgroup F ≃ₜ*
      specialFormPreservingMatrixSubgroup F' where
  toFun g := by
    let UM : Matrix (Fin n) (Fin n) ℝ := U
    let UiM : Matrix (Fin n) (Fin n) ℝ :=
      (U⁻¹ : GL (Fin n) ℝ)
    let A : GL (Fin n) ℝ := U⁻¹ * g.1.1 * U
    have hA : A ∈ formPreservingMatrixSubgroup F' := by
      rw [mem_formPreservingMatrixSubgroup_iff, ← hU]
      have hg := g.1.2
      rw [mem_formPreservingMatrixSubgroup_iff] at hg
      have hUU : UM * UiM = 1 := by
        change (U * U⁻¹ : GL (Fin n) ℝ).1 = 1
        simp
      have hUiTUT : UiMᵀ * UMᵀ = 1 := by
        rw [← Matrix.transpose_mul, hUU, Matrix.transpose_one]
      change
        (UiM * (g.1.1 : Matrix (Fin n) (Fin n) ℝ) * UM)ᵀ *
            (UMᵀ * F * UM) *
            (UiM * (g.1.1 : Matrix (Fin n) (Fin n) ℝ) * UM) =
          UMᵀ * F * UM
      calc
        _ = UMᵀ *
            (g.1.1 : Matrix (Fin n) (Fin n) ℝ)ᵀ *
            (UiMᵀ * UMᵀ) * F * (UM * UiM) *
            (g.1.1 : Matrix (Fin n) (Fin n) ℝ) * UM := by
              simp only [Matrix.transpose_mul]
              noncomm_ring
        _ = UMᵀ *
            ((g.1.1 : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
              (g.1.1 : Matrix (Fin n) (Fin n) ℝ)) * UM := by
              rw [hUiTUT, hUU]
              simp [Matrix.mul_assoc]
        _ = _ := by rw [hg]
    let og : formPreservingMatrixSubgroup F' := ⟨A, hA⟩
    refine ⟨og, (mem_specialFormPreservingMatrixSubgroup_iff F' og).mpr ?_⟩
    have hgdet :=
      (mem_specialFormPreservingMatrixSubgroup_iff F g.1).mp g.2
    change
      (UiM * (g.1.1 : Matrix (Fin n) (Fin n) ℝ) * UM).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, hgdet, mul_one,
      ← Matrix.det_mul]
    rw [show UiM * UM = 1 by
      change (U⁻¹ * U : GL (Fin n) ℝ).1 = 1
      simp, Matrix.det_one]
  invFun h := by
    let UM : Matrix (Fin n) (Fin n) ℝ := U
    let UiM : Matrix (Fin n) (Fin n) ℝ :=
      (U⁻¹ : GL (Fin n) ℝ)
    let A : GL (Fin n) ℝ := U * h.1.1 * U⁻¹
    have hA : A ∈ formPreservingMatrixSubgroup F := by
      rw [mem_formPreservingMatrixSubgroup_iff]
      have hh := h.1.2
      rw [mem_formPreservingMatrixSubgroup_iff] at hh
      have hUiU : UiM * UM = 1 := by
        change (U⁻¹ * U : GL (Fin n) ℝ).1 = 1
        simp
      have hUUi : UM * UiM = 1 := by
        change (U * U⁻¹ : GL (Fin n) ℝ).1 = 1
        simp
      have hUiTUT : UiMᵀ * UMᵀ = 1 := by
        rw [← Matrix.transpose_mul, hUUi, Matrix.transpose_one]
      have hcore :
          (h.1.1 : Matrix (Fin n) (Fin n) ℝ)ᵀ *
              (UMᵀ * F * UM) *
              (h.1.1 : Matrix (Fin n) (Fin n) ℝ) =
            UMᵀ * F * UM := by
        rw [hU]
        exact hh
      change
        (UM * (h.1.1 : Matrix (Fin n) (Fin n) ℝ) * UiM)ᵀ *
            F *
            (UM * (h.1.1 : Matrix (Fin n) (Fin n) ℝ) * UiM) = F
      calc
        _ = UiMᵀ *
            ((h.1.1 : Matrix (Fin n) (Fin n) ℝ)ᵀ *
              (UMᵀ * F * UM) *
              (h.1.1 : Matrix (Fin n) (Fin n) ℝ)) * UiM := by
              simp only [Matrix.transpose_mul]
              noncomm_ring
        _ = UiMᵀ * (UMᵀ * F * UM) * UiM := by rw [hcore]
        _ = (UiMᵀ * UMᵀ) * F * (UM * UiM) := by noncomm_ring
        _ = _ := by rw [hUiTUT, hUUi]; simp
    let og : formPreservingMatrixSubgroup F := ⟨A, hA⟩
    refine ⟨og, (mem_specialFormPreservingMatrixSubgroup_iff F og).mpr ?_⟩
    have hhdet :=
      (mem_specialFormPreservingMatrixSubgroup_iff F' h.1).mp h.2
    change
      (UM * (h.1.1 : Matrix (Fin n) (Fin n) ℝ) * UiM).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, hhdet, mul_one,
      ← Matrix.det_mul]
    rw [show UM * UiM = 1 by
      change (U * U⁻¹ : GL (Fin n) ℝ).1 = 1
      simp, Matrix.det_one]
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    group
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    group
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    change
      U⁻¹ * (g.1.1 * h.1.1) * U =
        (U⁻¹ * g.1.1 * U) * (U⁻¹ * h.1.1 * U)
    group
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop

@[simp]
theorem coe_specialFormPreservingRealFormCongruenceContinuousMulEquiv_apply
    (F F' : Matrix (Fin n) (Fin n) ℝ) (U : GL (Fin n) ℝ)
    (hU : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
      (U : Matrix (Fin n) (Fin n) ℝ) = F')
    (g : specialFormPreservingMatrixSubgroup F) :
    ((specialFormPreservingRealFormCongruenceContinuousMulEquiv
      F F' U hU g).1.1.1 : Matrix (Fin n) (Fin n) ℝ) =
      ((U⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * g.1.1.1 *
        (U : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

@[simp]
theorem coe_specialFormPreservingRealFormCongruenceContinuousMulEquiv_symm_apply
    (F F' : Matrix (Fin n) (Fin n) ℝ) (U : GL (Fin n) ℝ)
    (hU : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * F *
      (U : Matrix (Fin n) (Fin n) ℝ) = F')
    (g : specialFormPreservingMatrixSubgroup F') :
    ((specialFormPreservingRealFormCongruenceContinuousMulEquiv
      F F' U hU).symm g).1.1.1 =
      (U : Matrix (Fin n) (Fin n) ℝ) * g.1.1.1 *
        ((U⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

/-- The real inverse-square-root scaling identifies the special-orthogonal
group of a positive rational diagonal form with the identity-form group. -/
def positiveDiagonalSpecialOrthogonalContinuousMulEquiv
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    specialFormPreservingMatrixSubgroup
        ((Matrix.diagonal d).map (algebraMap ℚ ℝ)) ≃ₜ*
      specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) :=
  specialFormPreservingRealFormCongruenceContinuousMulEquiv
    ((Matrix.diagonal d).map (algebraMap ℚ ℝ))
    ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))
    (positiveDiagonalRealScalingUnit d hd) (by
      simpa using positiveDiagonalRealScaling_congruence d hd)

@[simp]
theorem coe_positiveDiagonalSpecialOrthogonalContinuousMulEquiv_apply
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (g : specialFormPreservingMatrixSubgroup
      ((Matrix.diagonal d).map (algebraMap ℚ ℝ))) :
    ((positiveDiagonalSpecialOrthogonalContinuousMulEquiv
      d hd g).1.1.1 : Matrix (Fin n) (Fin n) ℝ) =
      ((positiveDiagonalRealScalingUnit d hd)⁻¹ :
          GL (Fin n) ℝ) *
        g.1.1.1 * positiveDiagonalRealScalingUnit d hd :=
  rfl

@[simp]
theorem coe_positiveDiagonalSpecialOrthogonalContinuousMulEquiv_symm_apply
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (g : specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :
    ((positiveDiagonalSpecialOrthogonalContinuousMulEquiv
      d hd).symm g).1.1.1 =
      positiveDiagonalRealScalingUnit d hd * g.1.1.1 *
        ((positiveDiagonalRealScalingUnit d hd)⁻¹ :
          GL (Fin n) ℝ) :=
  rfl

/-- The tangent equivalence induced by real inverse-square-root diagonal
scaling. -/
def positiveDiagonalSkewAdjointContinuousLinearEquiv
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    (skewAdjointMatricesLieSubalgebra
      ((Matrix.diagonal d).map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  Matrix.skewAdjointRealFormCongruenceContinuousLinearEquiv
    ((Matrix.diagonal d).map (algebraMap ℚ ℝ))
    ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))
    (positiveDiagonalRealScalingUnit d hd) (by
      simpa using positiveDiagonalRealScaling_congruence d hd)

@[simp]
theorem coe_positiveDiagonalSkewAdjointContinuousLinearEquiv_apply
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (X : (skewAdjointMatricesLieSubalgebra
      ((Matrix.diagonal d).map (algebraMap ℚ ℝ))).toSubmodule) :
    (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd X :
      Matrix (Fin n) (Fin n) ℝ) =
      ((positiveDiagonalRealScalingUnit d hd :
        Matrix (Fin n) (Fin n) ℝ)⁻¹) * X.1 *
        (positiveDiagonalRealScalingUnit d hd :
          Matrix (Fin n) (Fin n) ℝ) :=
  rfl

@[simp]
theorem coe_positiveDiagonalSkewAdjointContinuousLinearEquiv_symm_apply
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (Y : (skewAdjointMatricesLieSubalgebra
      ((1 : Matrix (Fin n) (Fin n) ℚ).map
        (algebraMap ℚ ℝ))).toSubmodule) :
    ((positiveDiagonalSkewAdjointContinuousLinearEquiv d hd).symm Y :
      Matrix (Fin n) (Fin n) ℝ) =
      (positiveDiagonalRealScalingUnit d hd :
          Matrix (Fin n) (Fin n) ℝ) * Y.1 *
        ((positiveDiagonalRealScalingUnit d hd :
          Matrix (Fin n) (Fin n) ℝ)⁻¹) :=
  rfl

/-- The real determinant comparing the square-root-scaled diagonal tangent
basis with the independently fixed rational identity-form tangent basis. -/
def positiveDiagonalSkewAdjointDetScalar
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) : ℝ :=
  Matrix.skewAdjointRealLinearEquivDetScalar
    (Matrix.diagonal d) 1
    (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd)

/-- The real diagonal-to-identity tangent basis comparison is nonzero. -/
theorem positiveDiagonalSkewAdjointDetScalar_ne_zero
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    positiveDiagonalSkewAdjointDetScalar d hd ≠ 0 :=
  Matrix.skewAdjointRealLinearEquivDetScalar_ne_zero
    (Matrix.diagonal d) 1
    (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd)

/-- Real diagonal scaling transports the rationally normalized tangent
coordinate measure by the reciprocal absolute basis determinant. -/
theorem map_positiveDiagonalSkewAdjointRealCoordinateDetMeasure
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    Measure.map (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd)
        (Matrix.skewAdjointRealCoordinateDetMeasure
          (Matrix.diagonal d) 0) =
      (Real.toNNReal
        |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹ •
        Matrix.skewAdjointRealCoordinateDetMeasure
          (1 : Matrix (Fin n) (Fin n) ℚ) 0 :=
  Matrix.map_skewAdjointRealCoordinateDetMeasure_linearEquiv
    (Matrix.diagonal d) 1
    (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd)

end PositiveDefiniteIntegralLattice
