import SMSFormula.PadicCayleyTangentModulus
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Pointwise differential of the ambient p-adic Cayley map

At every point where `1 - X` is invertible, the ambient Cayley derivative is

`H ↦ 2 • ((1 - X)⁻¹ * H * (1 - X)⁻¹)`.

No restricted tangent determinant, measure transport, chart gluing, or
stabilizer-volume calculation is introduced.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The explicit ambient derivative of the p-adic Cayley map at `X`. -/
def padicCayleyForwardDerivative
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p]) :
    Matrix ι ι ℚ_[p] →L[ℚ_[p]] Matrix ι ι ℚ_[p] :=
  (2 : ℚ_[p]) •
    ContinuousLinearMap.mulLeftRight ℚ_[p] (Matrix ι ι ℚ_[p])
      (1 - X)⁻¹ (1 - X)⁻¹

@[simp]
theorem padicCayleyForwardDerivative_apply
    (p : ℕ) [Fact (Nat.Prime p)] (X H : Matrix ι ι ℚ_[p]) :
    padicCayleyForwardDerivative p X H =
      2 • ((1 - X)⁻¹ * H * (1 - X)⁻¹) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The ambient p-adic Cayley map has the explicit two-sided inverse
denominator derivative at every point of its source. -/
theorem hasFDerivAt_padicCayleyForwardMatrix
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) :
    HasFDerivAt
      (padicCayleyForwardMatrix (ι := ι) p)
      (padicCayleyForwardDerivative p X)
      X := by
  letI : CompleteSpace (Matrix ι ι ℚ_[p]) :=
    FiniteDimensional.complete ℚ_[p] _
  change IsUnit (1 - X) at hX
  change HasFDerivAt
    (fun Y : Matrix ι ι ℚ_[p] ↦ (1 + Y) * (1 - Y)⁻¹)
    (padicCayleyForwardDerivative p X)
    X
  simp_rw [nonsing_inv_eq_ringInverse]
  let I := ContinuousLinearMap.id ℚ_[p] (Matrix ι ι ℚ_[p])
  have hnum :
      HasFDerivAt
        (fun Y : Matrix ι ι ℚ_[p] ↦ 1 + Y) I X := by
    simpa [I] using
      (hasFDerivAt_id (𝕜 := ℚ_[p]) X).const_add
        (1 : Matrix ι ι ℚ_[p])
  have hden :
      HasFDerivAt
        (fun Y : Matrix ι ι ℚ_[p] ↦ 1 - Y) (-I) X := by
    simpa [I] using
      (hasFDerivAt_id (𝕜 := ℚ_[p]) X).const_sub
        (1 : Matrix ι ι ℚ_[p])
  have hinverseAtDenominator :
      HasFDerivAt
        (Ring.inverse :
          Matrix ι ι ℚ_[p] → Matrix ι ι ℚ_[p])
        (-ContinuousLinearMap.mulLeftRight ℚ_[p]
          (Matrix ι ι ℚ_[p]) (1 - X)⁻¹ (1 - X)⁻¹)
        (1 - X) := by
    have hunitInv :
        (↑hX.unit⁻¹ : Matrix ι ι ℚ_[p]) = (1 - X)⁻¹ := by
      rw [Matrix.coe_units_inv, hX.unit_spec]
    simpa only [hX.unit_spec, hunitInv] using
      (hasFDerivAt_ringInverse (𝕜 := ℚ_[p]) hX.unit)
  have hinverse :
      HasFDerivAt
        (fun Y : Matrix ι ι ℚ_[p] ↦ Ring.inverse (1 - Y))
        ((-ContinuousLinearMap.mulLeftRight ℚ_[p]
          (Matrix ι ι ℚ_[p]) (1 - X)⁻¹ (1 - X)⁻¹).comp (-I))
        X := by
    simpa only [Function.comp_apply] using
      hinverseAtDenominator.comp X hden
  convert hnum.mul' hinverse using 1
  ext H i j
  simp [padicCayleyForwardDerivative, I, two_mul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have hsum := padicCayleyForwardMatrix_add_one p X hX
  have hsum' :
      (1 + X) * (1 - X)⁻¹ + 1 =
        padicCayleyTwoMatrix (ι := ι) p * (1 - X)⁻¹ := by
    exact hsum
  have hmatrix :
      (1 - X)⁻¹ * H * (1 - X)⁻¹ +
          (1 - X)⁻¹ * H * (1 - X)⁻¹ =
        (1 + X) * ((1 - X)⁻¹ * H * (1 - X)⁻¹) +
          H * (1 - X)⁻¹ := by
    calc
      (1 - X)⁻¹ * H * (1 - X)⁻¹ +
          (1 - X)⁻¹ * H * (1 - X)⁻¹ =
          2 • ((1 - X)⁻¹ * H * (1 - X)⁻¹) := by module
      _ = (padicCayleyTwoMatrix (ι := ι) p * (1 - X)⁻¹) *
          H * (1 - X)⁻¹ := by
            rw [padicCayleyTwoMatrix, Matrix.scalar_apply]
            rw [show
              ((Matrix.diagonal fun _ : ι ↦ (2 : ℚ_[p])) * (1 - X)⁻¹) *
                  H * (1 - X)⁻¹ =
                (Matrix.diagonal fun _ : ι ↦ (2 : ℚ_[p])) *
                  ((1 - X)⁻¹ * H * (1 - X)⁻¹) by noncomm_ring]
            exact Matrix.smul_eq_diagonal_mul
              ((1 - X)⁻¹ * H * (1 - X)⁻¹) (2 : ℚ_[p])
      _ = ((1 + X) * (1 - X)⁻¹ + 1) * H * (1 - X)⁻¹ := by
            rw [hsum']
      _ = (1 + X) * ((1 - X)⁻¹ * H * (1 - X)⁻¹) +
          H * (1 - X)⁻¹ := by noncomm_ring
  exact congrArg (fun M : Matrix ι ι ℚ_[p] ↦ M i j) hmatrix

end Matrix
