import SMSFormula.PadicCayleyLeftTrivializedEndomorphism
import SMSFormula.PadicCayleyDeterminant

/-!
# Inverse of the intrinsic left-trivialized p-adic Cayley differential

The explicit inverse candidate

`K ↦ 2⁻¹ • ((1 + X) * K * (1 - X))`

preserves the transported skew-adjoint model. When the rational form is
nonsingular and `X` lies in the Cayley source, both Cayley numerators are
units and this candidate is a continuous linear inverse to the intrinsic
left-trivialized derivative.

This file does not compute a determinant, transport a measure, or glue
charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The explicit ambient continuous linear candidate for the inverse
left-trivialized derivative. -/
def skewAdjointPadicCayleyLeftTrivializedInverseAmbient
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
        Matrix ι ι ℚ_[p] :=
  ((2 : ℚ_[p])⁻¹) •
    ((ContinuousLinearMap.mulLeftRight ℚ_[p] (Matrix ι ι ℚ_[p])
      (1 + (X : Matrix ι ι ℚ_[p]))
      (1 - (X : Matrix ι ι ℚ_[p]))).comp
        (skewAdjointPadicAmbientInclusion F p))

@[simp]
theorem skewAdjointPadicCayleyLeftTrivializedInverseAmbient_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X K : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyLeftTrivializedInverseAmbient F p X K =
      (2 : ℚ_[p])⁻¹ •
        ((1 + (X : Matrix ι ι ℚ_[p])) *
          (K : Matrix ι ι ℚ_[p]) *
          (1 - (X : Matrix ι ι ℚ_[p]))) :=
  rfl

/-- The explicit inverse candidate preserves transported skew-adjointness. -/
theorem skewAdjointPadicCayleyLeftTrivializedInverseAmbient_mem
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X K : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyLeftTrivializedInverseAmbient F p X K ∈
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  let Fp : Matrix ι ι ℚ_[p] := F.map (algebraMap ℚ ℚ_[p])
  let Xm : Matrix ι ι ℚ_[p] := X
  let Km : Matrix ι ι ℚ_[p] := K
  let A : Matrix ι ι ℚ_[p] := 1 - Xm
  let B : Matrix ι ι ℚ_[p] := 1 + Xm
  rw [skewAdjointPadicCayleyLeftTrivializedInverseAmbient_apply]
  change (2 : ℚ_[p])⁻¹ • (B * Km * A) ∈
    (skewAdjointMatricesLieSubalgebra Fp).toSubmodule
  apply (skewAdjointMatricesLieSubalgebra Fp).toSubmodule.smul_mem
  have hXker : skewAdjointOperator Fp Xm = 0 := by
    exact LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff Fp Xm).mpr X.property)
  have hKker : skewAdjointOperator Fp Km = 0 := by
    exact LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff Fp Km).mpr K.property)
  have hXskew : Xmᵀ * Fp = -(Fp * Xm) :=
    eq_neg_of_add_eq_zero_left hXker
  have hKskew : Kmᵀ * Fp = -(Fp * Km) :=
    eq_neg_of_add_eq_zero_left hKker
  have hplus : Bᵀ * Fp = Fp * A := by
    dsimp [A, B]
    rw [Matrix.transpose_add]
    simp only [Matrix.transpose_one]
    calc
      (1 + Xmᵀ) * Fp = Fp + Xmᵀ * Fp := by noncomm_ring
      _ = Fp - Fp * Xm := by rw [hXskew]; noncomm_ring
      _ = Fp * (1 - Xm) := by noncomm_ring
  have hminus : Aᵀ * Fp = Fp * B := by
    dsimp [A, B]
    rw [Matrix.transpose_sub]
    simp only [Matrix.transpose_one]
    calc
      (1 - Xmᵀ) * Fp = Fp - Xmᵀ * Fp := by noncomm_ring
      _ = Fp + Fp * Xm := by rw [hXskew]; noncomm_ring
      _ = Fp * (1 + Xm) := by noncomm_ring
  apply (mem_ker_skewAdjointOperator_iff Fp (B * Km * A)).mp
  rw [LinearMap.mem_ker, skewAdjointOperator_apply]
  have hskew :
      (B * Km * A)ᵀ * Fp = -(Fp * (B * Km * A)) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    calc
      Aᵀ * (Kmᵀ * Bᵀ) * Fp =
          Aᵀ * Kmᵀ * (Bᵀ * Fp) := by noncomm_ring
      _ = Aᵀ * Kmᵀ * (Fp * A) := by rw [hplus]
      _ = Aᵀ * (Kmᵀ * Fp) * A := by noncomm_ring
      _ = Aᵀ * (-(Fp * Km)) * A := by rw [hKskew]
      _ = -(Aᵀ * Fp * Km * A) := by noncomm_ring
      _ = -(Fp * B * Km * A) := by rw [hminus]
      _ = -(Fp * (B * Km * A)) := by noncomm_ring
  rw [hskew, neg_add_cancel]

/-- The explicit inverse candidate as a continuous linear endomorphism of
the transported skew-adjoint model. -/
def skewAdjointPadicCayleyLeftTrivializedInverse
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointPadicCayleyLeftTrivializedInverseAmbient F p X).codRestrict _
    (fun K =>
      skewAdjointPadicCayleyLeftTrivializedInverseAmbient_mem F p X K)

@[simp]
theorem coe_skewAdjointPadicCayleyLeftTrivializedInverse_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X K : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointPadicCayleyLeftTrivializedInverse F p X K :
        Matrix ι ι ℚ_[p]) =
      (2 : ℚ_[p])⁻¹ •
        ((1 + (X : Matrix ι ι ℚ_[p])) *
          (K : Matrix ι ι ℚ_[p]) *
          (1 - (X : Matrix ι ι ℚ_[p]))) :=
  rfl

/-- Nonsingularity of the rational form makes the plus Cayley numerator a
unit whenever the minus numerator satisfies the source condition. -/
theorem isUnit_one_add_of_mem_skewAdjointPadicCayleySource
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    IsUnit (1 + (X : Matrix ι ι ℚ_[p])) := by
  let A : Matrix ι ι ℚ_[p] := 1 - X
  let B : Matrix ι ι ℚ_[p] := 1 + X
  change IsUnit A at hX
  apply (Matrix.isUnit_iff_isUnit_det B).mpr
  rw [skewAdjointPadicCayley_det_one_add_eq_det_one_sub F p hF X]
  exact (Matrix.isUnit_iff_isUnit_det A).mp hX

/-- The explicit inverse candidate is a left inverse to the intrinsic
left-trivialized derivative for a nonsingular rational form. -/
@[simp]
theorem skewAdjointPadicCayleyLeftTrivializedInverse_apply_endomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyLeftTrivializedInverse F p X
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism F p X hX H) =
      H := by
  let A : Matrix ι ι ℚ_[p] := 1 - X
  let B : Matrix ι ι ℚ_[p] := 1 + X
  let Hm : Matrix ι ι ℚ_[p] := H
  have hAunit : IsUnit A := by
    exact hX
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  have hBunit : IsUnit B :=
    isUnit_one_add_of_mem_skewAdjointPadicCayleySource F p hF X hX
  have hBdet : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  apply Subtype.ext
  rw [coe_skewAdjointPadicCayleyLeftTrivializedInverse_apply,
    coe_skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply]
  change
    (2 : ℚ_[p])⁻¹ •
        (B * (2 • (B⁻¹ * Hm * A⁻¹)) * A) =
      Hm
  rw [two_nsmul, ← two_smul ℚ_[p]]
  calc
    (2 : ℚ_[p])⁻¹ •
        (B * ((2 : ℚ_[p]) • (B⁻¹ * Hm * A⁻¹)) * A) =
      B * (B⁻¹ * Hm * A⁻¹) * A := by
        rw [mul_smul_comm, smul_mul_assoc, smul_smul]
        norm_num
    _ = (B * B⁻¹) * Hm * (A⁻¹ * A) := by noncomm_ring
    _ = Hm := by
      rw [Matrix.mul_nonsing_inv B hBdet,
        Matrix.nonsing_inv_mul A hAdet, one_mul, Matrix.mul_one]

/-- The intrinsic left-trivialized derivative is a left inverse to the
explicit inverse candidate for a nonsingular rational form. -/
@[simp]
theorem skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply_inverse
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X K : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyLeftTrivializedEndomorphism F p X hX
        (skewAdjointPadicCayleyLeftTrivializedInverse F p X K) =
      K := by
  let A : Matrix ι ι ℚ_[p] := 1 - X
  let B : Matrix ι ι ℚ_[p] := 1 + X
  let Km : Matrix ι ι ℚ_[p] := K
  have hAunit : IsUnit A := by
    exact hX
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  have hBunit : IsUnit B :=
    isUnit_one_add_of_mem_skewAdjointPadicCayleySource F p hF X hX
  have hBdet : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  apply Subtype.ext
  rw [coe_skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply,
    coe_skewAdjointPadicCayleyLeftTrivializedInverse_apply]
  change
    2 •
        (B⁻¹ * ((2 : ℚ_[p])⁻¹ • (B * Km * A)) * A⁻¹) =
      Km
  rw [two_nsmul, ← two_smul ℚ_[p]]
  calc
    (2 : ℚ_[p]) •
        (B⁻¹ * ((2 : ℚ_[p])⁻¹ • (B * Km * A)) * A⁻¹) =
      B⁻¹ * (B * Km * A) * A⁻¹ := by
        rw [mul_smul_comm, smul_mul_assoc, smul_smul]
        norm_num
    _ = (B⁻¹ * B) * Km * (A * A⁻¹) := by noncomm_ring
    _ = Km := by
      rw [Matrix.nonsing_inv_mul B hBdet,
        Matrix.mul_nonsing_inv A hAdet, one_mul, Matrix.mul_one]

end Matrix
