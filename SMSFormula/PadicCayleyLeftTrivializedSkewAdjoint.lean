import SMSFormula.PadicCayleyLeftTrivializedDifferential

/-!
# Skew-adjoint closure of the left-trivialized p-adic Cayley differential

The left-trivialized pointwise Cayley derivative carries a transported
skew-adjoint tangent vector back into the same skew-adjoint model. This file
packages that pointwise output, but does not bundle an intrinsic continuous
linear endomorphism, compute its determinant, or transport a measure.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The left-trivialized Cayley derivative of a transported skew-adjoint
tangent vector is again skew-adjoint. -/
theorem skewAdjointPadicCayleyLeftTrivializedDerivative_mem
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyLeftTrivializedDerivative F p X H ∈
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  let Fp : Matrix ι ι ℚ_[p] := F.map (algebraMap ℚ ℚ_[p])
  let Xm : Matrix ι ι ℚ_[p] := X
  let Hm : Matrix ι ι ℚ_[p] := H
  let A : Matrix ι ι ℚ_[p] := 1 - Xm
  let B : Matrix ι ι ℚ_[p] := 1 + Xm
  change IsUnit A at hX
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  rw [skewAdjointPadicCayleyLeftTrivializedDerivative_apply F p X H hX]
  change 2 • (B⁻¹ * Hm * A⁻¹) ∈
    (skewAdjointMatricesLieSubalgebra Fp).toSubmodule
  apply
    (skewAdjointMatricesLieSubalgebra Fp).toSubmodule.nsmul_mem
  by_cases hBdet : IsUnit B.det
  · have hAtdet : IsUnit Aᵀ.det := by
      rw [Matrix.det_transpose]
      exact hAdet
    have hBtdet : IsUnit Bᵀ.det := by
      rw [Matrix.det_transpose]
      exact hBdet
    have hXker : skewAdjointOperator Fp Xm = 0 := by
      exact LinearMap.mem_ker.mp
        ((mem_ker_skewAdjointOperator_iff Fp Xm).mpr X.property)
    have hHker : skewAdjointOperator Fp Hm = 0 := by
      exact LinearMap.mem_ker.mp
        ((mem_ker_skewAdjointOperator_iff Fp Hm).mpr H.property)
    have hXskew : Xmᵀ * Fp = -(Fp * Xm) :=
      eq_neg_of_add_eq_zero_left hXker
    have hHskew : Hmᵀ * Fp = -(Fp * Hm) :=
      eq_neg_of_add_eq_zero_left hHker
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
    have hBinvF : (Bᵀ)⁻¹ * Fp = Fp * A⁻¹ := by
      calc
        (Bᵀ)⁻¹ * Fp = (Bᵀ)⁻¹ * Fp * 1 := by rw [Matrix.mul_one]
        _ = (Bᵀ)⁻¹ * Fp * (A * A⁻¹) := by
          rw [Matrix.mul_nonsing_inv A hAdet]
        _ = (Bᵀ)⁻¹ * (Fp * A) * A⁻¹ := by noncomm_ring
        _ = (Bᵀ)⁻¹ * (Bᵀ * Fp) * A⁻¹ := by rw [hplus]
        _ = Fp * A⁻¹ := by
          rw [Matrix.nonsing_inv_mul_cancel_left Bᵀ Fp hBtdet]
    have hAinvF : (Aᵀ)⁻¹ * Fp = Fp * B⁻¹ := by
      calc
        (Aᵀ)⁻¹ * Fp = (Aᵀ)⁻¹ * Fp * 1 := by rw [Matrix.mul_one]
        _ = (Aᵀ)⁻¹ * Fp * (B * B⁻¹) := by
          rw [Matrix.mul_nonsing_inv B hBdet]
        _ = (Aᵀ)⁻¹ * (Fp * B) * B⁻¹ := by noncomm_ring
        _ = (Aᵀ)⁻¹ * (Aᵀ * Fp) * B⁻¹ := by rw [hminus]
        _ = Fp * B⁻¹ := by
          rw [Matrix.nonsing_inv_mul_cancel_left Aᵀ Fp hAtdet]
    apply
      (mem_ker_skewAdjointOperator_iff Fp
        (B⁻¹ * Hm * A⁻¹)).mp
    rw [LinearMap.mem_ker, skewAdjointOperator_apply]
    have hskew :
        (B⁻¹ * Hm * A⁻¹)ᵀ * Fp =
          -(Fp * (B⁻¹ * Hm * A⁻¹)) := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_nonsing_inv, Matrix.transpose_nonsing_inv]
      calc
        (Aᵀ)⁻¹ * (Hmᵀ * (Bᵀ)⁻¹) * Fp =
            (Aᵀ)⁻¹ * Hmᵀ * ((Bᵀ)⁻¹ * Fp) := by noncomm_ring
        _ = (Aᵀ)⁻¹ * Hmᵀ * (Fp * A⁻¹) := by rw [hBinvF]
        _ = (Aᵀ)⁻¹ * (Hmᵀ * Fp) * A⁻¹ := by noncomm_ring
        _ = (Aᵀ)⁻¹ * (-(Fp * Hm)) * A⁻¹ := by rw [hHskew]
        _ = -((Aᵀ)⁻¹ * Fp * Hm * A⁻¹) := by noncomm_ring
        _ = -(Fp * B⁻¹ * Hm * A⁻¹) := by rw [hAinvF]
        _ = -(Fp * (B⁻¹ * Hm * A⁻¹)) := by noncomm_ring
    rw [hskew, neg_add_cancel]
  · have hBinv : B⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit B hBdet
    have hzero : B⁻¹ * Hm * A⁻¹ = 0 := by
      rw [hBinv, zero_mul, zero_mul]
    rw [hzero]
    exact (skewAdjointMatricesLieSubalgebra Fp).zero_mem

/-- The point of the transported skew-adjoint model represented by the
left-trivialized pointwise Cayley derivative. -/
def skewAdjointPadicCayleyLeftTrivializedPoint
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨skewAdjointPadicCayleyLeftTrivializedDerivative F p X H,
    skewAdjointPadicCayleyLeftTrivializedDerivative_mem F p X H hX⟩

/-- The packaged left-trivialized tangent point has the literal ambient
matrix formula. -/
@[simp]
theorem coe_skewAdjointPadicCayleyLeftTrivializedPoint
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicCayleyLeftTrivializedPoint F p X H hX :
        Matrix ι ι ℚ_[p]) =
      2 • ((1 + (X : Matrix ι ι ℚ_[p]))⁻¹ *
        (H : Matrix ι ι ℚ_[p]) *
        (1 - (X : Matrix ι ι ℚ_[p]))⁻¹) :=
  skewAdjointPadicCayleyLeftTrivializedDerivative_apply F p X H hX

end Matrix
