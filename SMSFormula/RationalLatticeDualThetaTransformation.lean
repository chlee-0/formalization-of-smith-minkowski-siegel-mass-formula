import SMSFormula.RationalAdeleVectorComplexGaussianTheta
import SMSFormula.RationalAdeleVectorPolarDeterminant

/-!
# The theta inversion law of a dual-lattice coset, for complex `τ`

Let `L` be an integral lattice with form matrix `F` and polar matrix `S = 2F` (the
`realPolarMatrix`).  The dual lattice is `L^# = S⁻¹ ℤⁿ`.  Write `q(v) = ½ vᵀ S v`, so that
`q(S⁻¹u) = ½ uᵀ S⁻¹ u` (`polarDualNorm u`) for an integer vector `u`, and
`B(S⁻¹u₀, S⁻¹u) = u₀ᵀ S⁻¹ u`.

For `τ` in the upper half-plane and an integer vector `u₀` define

* the coset theta with representative `u₀`: `θ_{u₀}(τ) = Σ_{y ∈ ℤⁿ} e(τ q(y + S⁻¹u₀))`;
* the dual theta with character: `Θ_{u₀}(τ) = Σ_{u ∈ ℤⁿ} e(τ q(S⁻¹u)) e(-u₀ᵀ S⁻¹ u)`.

The inversion law is

`θ_{u₀}(-1/τ) = ((-iτ)^{1/2})ⁿ · √det(S⁻¹) · Θ_{u₀}(τ)`,

obtained from the complex-scale matrix Poisson theorem
(`tsum_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear_eq_centered_inv`) applied to the
positive definite `S⁻¹` at the scale `b = -iτ` (`Re b = Im τ > 0`) with the real shift `-S⁻¹u₀`.
The grouping of `Θ` by discriminant classes is a separate step.  Nothing is chosen.
-/

noncomputable section

open Matrix Complex

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-- The dual vector `S⁻¹ u` of an integer vector (real coordinates). -/
def polarDualReal (u : Fin n → ℤ) : Fin n → ℝ :=
  L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹ *ᵥ integerVectorReal u

/-- The dual norm `q(S⁻¹u) = ½ uᵀ S⁻¹ u`. -/
def polarDualNorm (u : Fin n → ℤ) : ℝ :=
  (integerVectorReal u ⬝ᵥ L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹ *ᵥ
    integerVectorReal u) / 2

/-- The dual pairing `B(S⁻¹u₀, S⁻¹u) = u₀ᵀ S⁻¹ u`. -/
def polarDualPairing (u₀ u : Fin n → ℤ) : ℝ :=
  integerVectorReal u₀ ⬝ᵥ L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹ *ᵥ integerVectorReal u

/-- The coset theta with representative `u₀`: `Σ_y e(τ q(y + S⁻¹u₀))`. -/
def polarCosetThetaRep (τ : ℂ) (u₀ : Fin n → ℤ) : ℂ :=
  ∑' y : Fin n → ℤ, complexCenteredMatrixGaussianSummand
    L.rationalQuadraticSpaceMatrix.realPolarMatrix (-I * τ) (-L.polarDualReal u₀) y

/-- The summand `e(τ q(S⁻¹u)) e(-u₀ᵀ S⁻¹ u)` of the dual theta with character. -/
def polarDualCharThetaSummand (τ : ℂ) (u₀ u : Fin n → ℤ) : ℂ :=
  exp (2 * Real.pi * I * τ * (L.polarDualNorm u : ℂ)) *
    exp (-(2 * Real.pi * I * (L.polarDualPairing u₀ u : ℂ)))

/-- The dual theta with character: `Σ_u e(τ q(S⁻¹u)) e(-u₀ᵀ S⁻¹ u)`. -/
def polarDualCharTheta (τ : ℂ) (u₀ : Fin n → ℤ) : ℂ :=
  ∑' u : Fin n → ℤ, L.polarDualCharThetaSummand τ u₀ u

theorem realPolarMatrix_inv_isSymm :
    (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).IsSymm := by
  have h := L.rationalQuadraticSpaceMatrix.realPolarMatrix_isSymm
  unfold Matrix.IsSymm at h ⊢
  rw [Matrix.transpose_nonsing_inv, h]

/-- The shifted summand at `S⁻¹`, scale `-iτ` and real shift `-S⁻¹u₀` is the dual-theta summand. -/
theorem shiftedMatrixGaussianSummand_inv_eq_polarDualCharThetaSummand (τ : ℂ)
    (u₀ u : Fin n → ℤ) :
    shiftedMatrixGaussianSummand L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹ (-I * τ)
        (pureImaginaryLinear (-L.polarDualReal u₀)) u =
      L.polarDualCharThetaSummand τ u₀ u := by
  unfold shiftedMatrixGaussianSummand polarDualCharThetaSummand
  rw [← Complex.exp_add]
  congr 1
  have hsymm : L.polarDualReal u₀ ⬝ᵥ integerVectorReal u = L.polarDualPairing u₀ u := by
    unfold polarDualReal polarDualPairing
    rw [dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose,
      (L.realPolarMatrix_inv_isSymm).eq, dotProduct_comm]
  have hlin : ∑ i, pureImaginaryLinear (-L.polarDualReal u₀) i * ((u i : ℤ) : ℂ) =
      -(I * ((L.polarDualPairing u₀ u : ℝ) : ℂ)) := by
    rw [← hsymm]
    simp only [pureImaginaryLinear, Pi.neg_apply, dotProduct, integerVectorReal]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hlin]
  unfold polarDualNorm
  push_cast
  ring

/-- `(-iτ)⁻¹ = -i(-1/τ)`. -/
theorem neg_I_mul_inv (τ : ℂ) : (-I * τ)⁻¹ = -I * (-τ⁻¹) := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · simp
  field_simp
  rw [I_sq]

/-- The coset inversion law, over the full dual lattice:
`θ_{u₀}(-1/τ) = ((-iτ)^{1/2})ⁿ · √det(S⁻¹) · Θ_{u₀}(τ)`. -/
theorem polarCosetThetaRep_neg_inv {τ : ℂ} (hτ : 0 < τ.im) (u₀ : Fin n → ℤ) :
    L.polarCosetThetaRep (-τ⁻¹) u₀ =
      ((-I * τ) ^ (1 / 2 : ℂ)) ^ n *
          (Real.sqrt (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det : ℂ) *
        L.polarDualCharTheta τ u₀ := by
  have hS : (L.rationalQuadraticSpaceMatrix.realPolarMatrix).PosDef :=
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef
  have hb : 0 < (-I * τ).re := by simpa using hτ
  have h := tsum_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear_eq_centered_inv n
    (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹) hS.inv hb (-L.polarDualReal u₀)
  have hSinv : (L.rationalQuadraticSpaceMatrix.realPolarMatrix)⁻¹⁻¹ =
      L.rationalQuadraticSpaceMatrix.realPolarMatrix :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 hS.det_pos.ne')
  rw [hSinv, neg_I_mul_inv] at h
  simp only [L.shiftedMatrixGaussianSummand_inv_eq_polarDualCharThetaSummand] at h
  change L.polarDualCharTheta τ u₀ =
    complexShiftedMatrixThetaNormalization (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹)
      (-I * τ) * L.polarCosetThetaRep (-τ⁻¹) u₀ at h
  have hdet : 0 < (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det := hS.inv.det_pos
  have hsq : (Real.sqrt (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hdet).ne'
  have hbne : (-I * τ) ≠ 0 := fun h0 ↦ by simp [h0] at hb
  have hpow : ((-I * τ) ^ (1 / 2 : ℂ)) ^ n ≠ 0 :=
    pow_ne_zero _ ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hbne)
  have hpow' : ((-(τ * I)) ^ (1 / 2 : ℂ)) ^ n ≠ 0 := by
    rwa [show -(τ * I) = -I * τ by ring]
  rw [h, complexShiftedMatrixThetaNormalization, Fintype.card_fin]
  field_simp

end PositiveDefiniteIntegralLattice
