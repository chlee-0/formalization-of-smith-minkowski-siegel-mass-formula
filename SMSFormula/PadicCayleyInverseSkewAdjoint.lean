import SMSFormula.PadicCayleySpecialOrthogonal

/-!
# Skew-adjointness of the inverse p-adic Cayley formula

For a special-orthogonal matrix in the explicit inverse domain, the ambient
Cayley inverse matrix is skew-adjoint for the scalar-extended rational form.
This file packages that matrix in the transported skew-adjoint model.

No forward/inverse equivalence, topology, local equivalence, measure
transport, chart gluing, or stabilizer-volume calculation is introduced.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The explicit inverse domain restricted to the special-orthogonal matrix
carrier. -/
def padicCayleySpecialOrthogonalInverseDomain
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Set (specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p]))) :=
  {g | (g : Matrix ι ι ℚ_[p]) ∈ padicCayleyInverseDomain p}

/-- The inverse Cayley matrix also satisfies the right cross-multiplied
identity. -/
theorem padicCayleyInverseMatrix_cross_right
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p])
    (hg : g ∈ padicCayleyInverseDomain p) :
    padicCayleyInverseMatrix p g * (g + 1) = g - 1 := by
  let C : Matrix ι ι ℚ_[p] := g + 1
  let D : Matrix ι ι ℚ_[p] := g - 1
  have hCdet : IsUnit C.det :=
    (Matrix.isUnit_iff_isUnit_det C).mp hg
  change (C⁻¹ * D) * C = D
  calc
    (C⁻¹ * D) * C = C⁻¹ * (D * C) := by rw [Matrix.mul_assoc]
    _ = C⁻¹ * (C * D) := by
      congr 1
      dsimp [C, D]
      noncomm_ring
    _ = (C⁻¹ * C) * D := by rw [Matrix.mul_assoc]
    _ = D := by rw [Matrix.nonsing_inv_mul C hCdet, one_mul]

/-- The inverse Cayley matrix of a special-orthogonal inverse-domain point
lies in the kernel of the skew-adjoint operator. -/
theorem skewAdjointOperator_padicCayleyInverseMatrix_eq_zero
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (g : specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p])))
    (hg : (g : Matrix ι ι ℚ_[p]) ∈ padicCayleyInverseDomain p) :
    skewAdjointOperator (F.map (algebraMap ℚ ℚ_[p]))
        (padicCayleyInverseMatrix p g) = 0 := by
  let Fp : Matrix ι ι ℚ_[p] := F.map (algebraMap ℚ ℚ_[p])
  let gm : Matrix ι ι ℚ_[p] := g
  let C : Matrix ι ι ℚ_[p] := gm + 1
  let D : Matrix ι ι ℚ_[p] := gm - 1
  let X : Matrix ι ι ℚ_[p] := padicCayleyInverseMatrix p gm
  have hCdet : IsUnit C.det :=
    (Matrix.isUnit_iff_isUnit_det C).mp hg
  have hCtdet : IsUnit Cᵀ.det := by
    rw [Matrix.det_transpose]
    exact hCdet
  have hcross : X * C = D :=
    padicCayleyInverseMatrix_cross_right p gm hg
  have hcrossT : Cᵀ * Xᵀ = Dᵀ := by
    simpa only [Matrix.transpose_mul] using
      congrArg Matrix.transpose hcross
  have hform : gmᵀ * Fp * gm = Fp :=
    (formPreservingConstraint_eq_zero_iff Fp gm).mp g.property.1
  have hcleared : Cᵀ * (Xᵀ * Fp + Fp * X) * C = 0 := by
    calc
      Cᵀ * (Xᵀ * Fp + Fp * X) * C =
          (Cᵀ * Xᵀ) * Fp * C + Cᵀ * Fp * (X * C) := by
        noncomm_ring
      _ = Dᵀ * Fp * C + Cᵀ * Fp * D := by rw [hcrossT, hcross]
      _ = 0 := by
        dsimp [C, D]
        rw [Matrix.transpose_add, Matrix.transpose_sub]
        simp only [Matrix.transpose_one]
        calc
          (gmᵀ - 1) * Fp * (gm + 1) +
              (gmᵀ + 1) * Fp * (gm - 1) =
            (gmᵀ * Fp * gm - Fp) + (gmᵀ * Fp * gm - Fp) := by
              noncomm_ring
          _ = 0 := by rw [hform]; simp
  change Xᵀ * Fp + Fp * X = 0
  calc
    Xᵀ * Fp + Fp * X =
        ((Cᵀ)⁻¹ * Cᵀ) * (Xᵀ * Fp + Fp * X) * (C * C⁻¹) := by
      rw [Matrix.nonsing_inv_mul Cᵀ hCtdet,
        Matrix.mul_nonsing_inv C hCdet, one_mul, Matrix.mul_one]
    _ = (Cᵀ)⁻¹ * (Cᵀ * (Xᵀ * Fp + Fp * X) * C) * C⁻¹ := by
      noncomm_ring
    _ = 0 := by rw [hcleared, Matrix.mul_zero, Matrix.zero_mul]

/-- The inverse Cayley formula, packaged in the transported skew-adjoint
model on the explicit special-orthogonal inverse domain. -/
def padicCayleySpecialOrthogonalInverseSkewAdjoint
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    padicCayleySpecialOrthogonalInverseDomain F p →
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  fun g ↦
    ⟨padicCayleyInverseMatrix p g.1,
      (mem_ker_skewAdjointOperator_iff _ _).mp
        (skewAdjointOperator_padicCayleyInverseMatrix_eq_zero
          F p g.1 g.2)⟩

@[simp]
theorem coe_padicCayleySpecialOrthogonalInverseSkewAdjoint
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    (padicCayleySpecialOrthogonalInverseSkewAdjoint F p g :
        Matrix ι ι ℚ_[p]) =
      (((g.1 : specialOrthogonalMatrixSet
          (F.map (algebraMap ℚ ℚ_[p]))) : Matrix ι ι ℚ_[p]) + 1)⁻¹ *
        (((g.1 : specialOrthogonalMatrixSet
          (F.map (algebraMap ℚ ℚ_[p]))) : Matrix ι ι ℚ_[p]) - 1) :=
  rfl

end Matrix
