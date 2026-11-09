import SMSFormula.PadicCayleyEquiv

/-!
# Openness of the p-adic Cayley domains

The ambient Cayley source and inverse domain are continuous affine preimages
of the open unit set in the finite p-adic matrix ring. Restricting along the
transported skew-adjoint and special-orthogonal carrier inclusions gives the
open source and target of the algebraic Cayley equivalence.

No continuity of the Cayley formulas, homeomorphism, measure transport, chart
gluing, or stabilizer-volume calculation is introduced.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ambient p-adic Cayley source is open in the matrix space. -/
theorem isOpen_padicCayleySource
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (padicCayleySource (ι := ι) p) := by
  change IsOpen {X : Matrix ι ι ℚ_[p] | IsUnit (1 - X)}
  have hcontinuous :
      Continuous (fun X : Matrix ι ι ℚ_[p] ↦ 1 - X) := by fun_prop
  simp_rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact isClosed_singleton.isOpen_compl.preimage hcontinuous.matrix_det

/-- The ambient p-adic Cayley inverse domain is open in the matrix space. -/
theorem isOpen_padicCayleyInverseDomain
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (padicCayleyInverseDomain (ι := ι) p) := by
  change IsOpen {g : Matrix ι ι ℚ_[p] | IsUnit (g + 1)}
  have hcontinuous :
      Continuous (fun g : Matrix ι ι ℚ_[p] ↦ g + 1) := by fun_prop
  simp_rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact isClosed_singleton.isOpen_compl.preimage hcontinuous.matrix_det

/-- The explicit transported skew-adjoint Cayley source is open in the
transported skew-adjoint model. -/
theorem isOpen_skewAdjointPadicCayleySource
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (skewAdjointPadicCayleySource F p) := by
  change IsOpen
    ((fun X :
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ↦
        (X : Matrix ι ι ℚ_[p])) ⁻¹' padicCayleySource p)
  exact (isOpen_padicCayleySource p).preimage continuous_subtype_val

/-- The explicit special-orthogonal Cayley inverse domain is open in the
special-orthogonal matrix carrier. -/
theorem isOpen_padicCayleySpecialOrthogonalInverseDomain
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (padicCayleySpecialOrthogonalInverseDomain F p) := by
  change IsOpen
    ((fun g :
        specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p])) ↦
        (g : Matrix ι ι ℚ_[p])) ⁻¹' padicCayleyInverseDomain p)
  exact (isOpen_padicCayleyInverseDomain p).preimage continuous_subtype_val

end Matrix
