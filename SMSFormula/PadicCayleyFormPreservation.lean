import SMSFormula.PadicCayleyAlgebra

/-!
# Form preservation of the p-adic Cayley map

For a matrix skew-adjoint with respect to the scalar extension of a rational
form, the two Cayley numerators `1 + X` and `1 - X` induce the same form.
Cancelling the invertible source denominator proves that the Cayley forward
matrix preserves the form.

This file does not prove determinant one, package an `SO`-valued map, add
topology, or transport a measure.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The plus and minus Cayley numerators induce the same form for every
transported skew-adjoint matrix. -/
theorem skewAdjointPadicCayley_numerator_form_eq
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (1 + (X : Matrix ι ι ℚ_[p]))ᵀ *
          F.map (algebraMap ℚ ℚ_[p]) *
          (1 + (X : Matrix ι ι ℚ_[p])) =
      (1 - (X : Matrix ι ι ℚ_[p]))ᵀ *
          F.map (algebraMap ℚ ℚ_[p]) *
          (1 - (X : Matrix ι ι ℚ_[p])) := by
  let Fp : Matrix ι ι ℚ_[p] := F.map (algebraMap ℚ ℚ_[p])
  let Xm : Matrix ι ι ℚ_[p] := X
  have hker : skewAdjointOperator Fp Xm = 0 := by
    exact LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff Fp Xm).mpr X.property)
  have hskew : Xmᵀ * Fp = -(Fp * Xm) :=
    eq_neg_of_add_eq_zero_left hker
  change (1 + Xm)ᵀ * Fp * (1 + Xm) =
    (1 - Xm)ᵀ * Fp * (1 - Xm)
  rw [Matrix.transpose_add, Matrix.transpose_sub]
  simp only [Matrix.transpose_one]
  have hplus :
      (1 + Xmᵀ) * Fp * (1 + Xm) =
        Fp + Xmᵀ * Fp * Xm := by
    calc
      (1 + Xmᵀ) * Fp * (1 + Xm) =
          Fp + Xmᵀ * Fp + Fp * Xm + Xmᵀ * Fp * Xm := by
        noncomm_ring
      _ = Fp + Xmᵀ * Fp * Xm := by
        rw [hskew]
        noncomm_ring
  have hminus :
      (1 - Xmᵀ) * Fp * (1 - Xm) =
        Fp + Xmᵀ * Fp * Xm := by
    calc
      (1 - Xmᵀ) * Fp * (1 - Xm) =
          Fp - Xmᵀ * Fp - Fp * Xm + Xmᵀ * Fp * Xm := by
        noncomm_ring
      _ = Fp + Xmᵀ * Fp * Xm := by
        rw [hskew]
        noncomm_ring
  exact hplus.trans hminus.symm

/-- On the explicit unit source, the transported skew-adjoint Cayley forward
matrix preserves the scalar-extended rational form. -/
theorem skewAdjointPadicCayleyForwardMatrix_formPreserving
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : (X : Matrix ι ι ℚ_[p]) ∈ padicCayleySource p) :
    (skewAdjointPadicCayleyForwardMatrix F p X)ᵀ *
          F.map (algebraMap ℚ ℚ_[p]) *
          skewAdjointPadicCayleyForwardMatrix F p X =
      F.map (algebraMap ℚ ℚ_[p]) := by
  let Fp : Matrix ι ι ℚ_[p] := F.map (algebraMap ℚ ℚ_[p])
  let Xm : Matrix ι ι ℚ_[p] := X
  let A : Matrix ι ι ℚ_[p] := 1 - Xm
  let B : Matrix ι ι ℚ_[p] := 1 + Xm
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  have hAtdet : IsUnit Aᵀ.det := by
    rw [Matrix.det_transpose]
    exact hAdet
  have hnum : Bᵀ * Fp * B = Aᵀ * Fp * A := by
    exact skewAdjointPadicCayley_numerator_form_eq F p X
  change (B * A⁻¹)ᵀ * Fp * (B * A⁻¹) = Fp
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  calc
    (Aᵀ)⁻¹ * Bᵀ * Fp * (B * A⁻¹) =
        (Aᵀ)⁻¹ * (Bᵀ * Fp * B) * A⁻¹ := by
      noncomm_ring
    _ = (Aᵀ)⁻¹ * (Aᵀ * Fp * A) * A⁻¹ := by rw [hnum]
    _ = ((Aᵀ)⁻¹ * Aᵀ) * Fp * (A * A⁻¹) := by noncomm_ring
    _ = Fp := by
      rw [Matrix.nonsing_inv_mul Aᵀ hAtdet,
        Matrix.mul_nonsing_inv A hAdet, one_mul, Matrix.mul_one]

end Matrix
