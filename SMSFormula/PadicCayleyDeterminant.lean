import SMSFormula.PadicCayleyFormPreservation

/-!
# Determinant of the p-adic Cayley map

For a nonsingular rational form, transported skew-adjointness identifies the
determinants of the two Cayley numerators. On the explicit Cayley source, the
forward matrix therefore has determinant one.

This file does not package an `SO`-valued map, add topology, transport a
measure, or compute a stabilizer volume.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem padic_det_map_algebraMap_ne_zero
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) :
    (F.map (algebraMap ℚ ℚ_[p])).det ≠ 0 := by
  have hmap : algebraMap ℚ ℚ_[p] F.det ≠ 0 := by
    intro hz
    apply hF
    apply (algebraMap ℚ ℚ_[p]).injective
    simpa using hz
  have heq :
      (F.map (algebraMap ℚ ℚ_[p])).det =
        algebraMap ℚ ℚ_[p] F.det := by
    simpa [RingHom.mapMatrix_apply] using
      ((algebraMap ℚ ℚ_[p]).map_det F).symm
  rwa [heq]

/-- The two Cayley numerators intertwine the scalar-extended rational form. -/
theorem skewAdjointPadicCayley_numerator_intertwines
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (1 + (X : Matrix ι ι ℚ_[p]))ᵀ *
          F.map (algebraMap ℚ ℚ_[p]) =
      F.map (algebraMap ℚ ℚ_[p]) *
          (1 - (X : Matrix ι ι ℚ_[p])) := by
  let Fp : Matrix ι ι ℚ_[p] := F.map (algebraMap ℚ ℚ_[p])
  let Xm : Matrix ι ι ℚ_[p] := X
  have hker : skewAdjointOperator Fp Xm = 0 := by
    exact LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff Fp Xm).mpr X.property)
  have hskew : Xmᵀ * Fp = -(Fp * Xm) :=
    eq_neg_of_add_eq_zero_left hker
  change (1 + Xm)ᵀ * Fp = Fp * (1 - Xm)
  rw [Matrix.transpose_add]
  simp only [Matrix.transpose_one]
  calc
    (1 + Xmᵀ) * Fp = Fp + Xmᵀ * Fp := by noncomm_ring
    _ = Fp - Fp * Xm := by
      rw [hskew]
      noncomm_ring
    _ = Fp * (1 - Xm) := by noncomm_ring

/-- For a nonsingular rational form, the plus and minus Cayley numerators
have equal determinants. -/
theorem skewAdjointPadicCayley_det_one_add_eq_det_one_sub
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (1 + (X : Matrix ι ι ℚ_[p])).det =
      (1 - (X : Matrix ι ι ℚ_[p])).det := by
  let Fp : Matrix ι ι ℚ_[p] := F.map (algebraMap ℚ ℚ_[p])
  let A : Matrix ι ι ℚ_[p] := 1 - X
  let B : Matrix ι ι ℚ_[p] := 1 + X
  have hintertwines : Bᵀ * Fp = Fp * A :=
    skewAdjointPadicCayley_numerator_intertwines F p X
  have hdet := congrArg Matrix.det hintertwines
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hFp : Fp.det ≠ 0 :=
    padic_det_map_algebraMap_ne_zero F p hF
  change B.det = A.det
  apply mul_right_cancel₀ hFp
  calc
    B.det * Fp.det = Fp.det * A.det := hdet
    _ = A.det * Fp.det := mul_comm _ _

/-- On the explicit source, the transported skew-adjoint p-adic Cayley
forward matrix has determinant one. -/
theorem skewAdjointPadicCayleyForwardMatrix_det_one
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : (X : Matrix ι ι ℚ_[p]) ∈ padicCayleySource p) :
    (skewAdjointPadicCayleyForwardMatrix F p X).det = 1 := by
  let A : Matrix ι ι ℚ_[p] := 1 - X
  let B : Matrix ι ι ℚ_[p] := 1 + X
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  have hBA : B.det = A.det :=
    skewAdjointPadicCayley_det_one_add_eq_det_one_sub F p hF X
  change (B * A⁻¹).det = 1
  rw [Matrix.det_mul, hBA, mul_comm]
  exact Matrix.det_nonsing_inv_mul_det A hAdet

end Matrix
