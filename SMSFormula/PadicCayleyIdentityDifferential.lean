import SMSFormula.PadicCayleyHomeomorph
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Identity and differential of the p-adic Cayley map

The explicit transported skew-adjoint source contains zero, and the
special-orthogonal inverse domain contains the matrix identity. At zero, the
ambient p-adic Cayley forward map has derivative `H ↦ 2 • H`.

No top-form or measure transport, chart gluing, or stabilizer-volume
calculation is introduced.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Zero lies in the ambient p-adic Cayley source. -/
@[simp]
theorem zero_mem_padicCayleySource
    (p : ℕ) [Fact (Nat.Prime p)] :
    (0 : Matrix ι ι ℚ_[p]) ∈ padicCayleySource p := by
  change IsUnit (1 - (0 : Matrix ι ι ℚ_[p]))
  simp

/-- Zero lies in the explicit transported skew-adjoint Cayley source. -/
@[simp]
theorem zero_mem_skewAdjointPadicCayleySource
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (0 : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
        skewAdjointPadicCayleySource F p := by
  exact zero_mem_padicCayleySource p

/-- The special-orthogonal matrix identity lies in the explicit p-adic
Cayley inverse domain. -/
@[simp]
theorem specialOrthogonalMatrixIdentity_mem_padicCayleyInverseDomain
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    specialOrthogonalMatrixIdentity (F.map (algebraMap ℚ ℚ_[p])) ∈
      padicCayleySpecialOrthogonalInverseDomain F p := by
  change IsUnit ((1 : Matrix ι ι ℚ_[p]) + 1)
  rw [← two_smul ℚ_[p] (1 : Matrix ι ι ℚ_[p]),
    smul_eq_diagonal_mul, Matrix.mul_one]
  exact (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ_[p]) ≠ 0)).map
    (Matrix.scalar ι)

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of the ambient p-adic Cayley forward map at zero is
scalar multiplication by `2`. -/
theorem hasFDerivAt_padicCayleyForwardMatrix_zero
    (p : ℕ) [Fact (Nat.Prime p)] :
    HasFDerivAt
      (padicCayleyForwardMatrix (ι := ι) p)
      ((2 : ℚ_[p]) •
        ContinuousLinearMap.id ℚ_[p] (Matrix ι ι ℚ_[p]))
      0 := by
  letI : CompleteSpace (Matrix ι ι ℚ_[p]) :=
    FiniteDimensional.complete ℚ_[p] _
  change HasFDerivAt
    (fun X : Matrix ι ι ℚ_[p] ↦ (1 + X) * (1 - X)⁻¹)
    ((2 : ℚ_[p]) •
      ContinuousLinearMap.id ℚ_[p] (Matrix ι ι ℚ_[p]))
    0
  simp_rw [nonsing_inv_eq_ringInverse]
  let I := ContinuousLinearMap.id ℚ_[p] (Matrix ι ι ℚ_[p])
  have hnum :
      HasFDerivAt
        (fun X : Matrix ι ι ℚ_[p] ↦ 1 + X) I 0 := by
    simpa [I] using
      (hasFDerivAt_id (𝕜 := ℚ_[p])
        (0 : Matrix ι ι ℚ_[p])).const_add
          (1 : Matrix ι ι ℚ_[p])
  have hden :
      HasFDerivAt
        (fun X : Matrix ι ι ℚ_[p] ↦ 1 - X) (-I) 0 := by
    simpa [I] using
      (hasFDerivAt_id (𝕜 := ℚ_[p])
        (0 : Matrix ι ι ℚ_[p])).const_sub
          (1 : Matrix ι ι ℚ_[p])
  have hinverseOne :
      HasFDerivAt
        (Ring.inverse :
          Matrix ι ι ℚ_[p] → Matrix ι ι ℚ_[p])
        (-ContinuousLinearMap.mulLeftRight ℚ_[p]
          (Matrix ι ι ℚ_[p]) 1 1)
        1 := by
    simpa using
      (hasFDerivAt_ringInverse
        (𝕜 := ℚ_[p]) (1 : (Matrix ι ι ℚ_[p])ˣ))
  have hinverse :
      HasFDerivAt
        (fun X : Matrix ι ι ℚ_[p] ↦ Ring.inverse (1 - X))
        ((-ContinuousLinearMap.mulLeftRight ℚ_[p]
          (Matrix ι ι ℚ_[p]) 1 1).comp (-I))
        0 := by
    have hinverseAtDenominator :
        HasFDerivAt
          (Ring.inverse :
            Matrix ι ι ℚ_[p] → Matrix ι ι ℚ_[p])
          (-ContinuousLinearMap.mulLeftRight ℚ_[p]
            (Matrix ι ι ℚ_[p]) 1 1)
          (1 - (0 : Matrix ι ι ℚ_[p])) := by
      simpa using hinverseOne
    simpa only [Function.comp_apply] using
      hinverseAtDenominator.comp 0 hden
  convert hnum.mul' hinverse using 1
  ext H i j
  simp [I, two_mul, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.mulLeftRight_apply]

end Matrix
