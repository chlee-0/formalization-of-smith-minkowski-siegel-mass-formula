import SMSFormula.PadicCayleyRestrictedPointwiseDifferential

/-!
# Left-trivialized pointwise p-adic Cayley differential

Left multiplication by the inverse Cayley image transforms the restricted
pointwise derivative into the ambient formula

`H ↦ 2 • ((1 + X)⁻¹ * H * (1 - X)⁻¹)`.

No skew-adjoint closure, intrinsic endomorphism, determinant, measure
transport, chart gluing, or stabilizer-volume calculation is introduced.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The restricted pointwise Cayley derivative, left translated back by the
inverse ambient Cayley image. -/
def skewAdjointPadicCayleyLeftTrivializedDerivative
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
        Matrix ι ι ℚ_[p] :=
  (ContinuousLinearMap.mulLeftRight ℚ_[p] (Matrix ι ι ℚ_[p])
    (skewAdjointPadicCayleyForwardMatrix F p X)⁻¹ 1).comp
      (skewAdjointPadicCayleyForwardDerivative F p X)

/-- The left-trivialized derivative has one inverse Cayley numerator on the
left and one inverse denominator on the right. -/
theorem skewAdjointPadicCayleyLeftTrivializedDerivative_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyLeftTrivializedDerivative F p X H =
      2 • ((1 + (X : Matrix ι ι ℚ_[p]))⁻¹ *
        (H : Matrix ι ι ℚ_[p]) *
        (1 - (X : Matrix ι ι ℚ_[p]))⁻¹) := by
  let Xm : Matrix ι ι ℚ_[p] := X
  let A : Matrix ι ι ℚ_[p] := 1 - Xm
  let B : Matrix ι ι ℚ_[p] := 1 + Xm
  change IsUnit A at hX
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  have hcomm : A * B = B * A := by
    dsimp [A, B]
    noncomm_ring
  have hBinvComm : B * A⁻¹ = A⁻¹ * B := by
    apply hX.mul_left_cancel
    calc
      A * (B * A⁻¹) = B := by
        rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv A hAdet, Matrix.mul_one]
      _ = A * (A⁻¹ * B) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAdet,
          Matrix.one_mul]
  have hleft :
      (padicCayleyForwardMatrix p Xm)⁻¹ * A⁻¹ = B⁻¹ := by
    rw [padicCayleyForwardMatrix, hBinvComm, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv A hAdet, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv A hAdet, Matrix.mul_one]
  change
    (padicCayleyForwardMatrix p Xm)⁻¹ *
        (2 • (A⁻¹ * (H : Matrix ι ι ℚ_[p]) * A⁻¹)) * 1 =
      2 • (B⁻¹ * (H : Matrix ι ι ℚ_[p]) * A⁻¹)
  rw [Matrix.mul_one, mul_smul_comm]
  congr 1
  calc
    (padicCayleyForwardMatrix p Xm)⁻¹ *
        (A⁻¹ * (H : Matrix ι ι ℚ_[p]) * A⁻¹) =
      ((padicCayleyForwardMatrix p Xm)⁻¹ * A⁻¹) *
        (H : Matrix ι ι ℚ_[p]) * A⁻¹ := by noncomm_ring
    _ = B⁻¹ * (H : Matrix ι ι ℚ_[p]) * A⁻¹ := by rw [hleft]

end Matrix
