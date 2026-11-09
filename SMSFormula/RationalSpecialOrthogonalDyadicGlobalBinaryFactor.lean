import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicNormalizationProvenance
import SMSFormula.RationalSpecialOrthogonalRealArchimedeanNormalization
import SMSFormula.RationalSpecialOrthogonalBadPrimeUnitNormalization

/-!
# The global real/dyadic binary factor split

The real Gamma/archimedean coefficient and Schulze--Pillot's dyadic
`|2|₂^{-n}` coefficient are both exactly `2^n`.  This module proves their
reciprocal cancellation directly, inserts that cancellation into the closed
real determinant composition, and records separately that the inverse dyadic
Cayley tangent modulus is still `2^d`.

Thus the rank-`d` layer exposed by the finite dyadic correspondence is not
already contained in the rank-`n` real/dyadic coefficient cancellation.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix Matrix.Norms.Operator NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_dyadic_global_binary_factor_audit :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The real Gamma/archimedean coefficient and the dyadic
Schulze--Pillot `|2|₂^{-n}` coefficient cancel reciprocally in `ENNReal`. -/
theorem
    ENNReal_ofReal_realGamma_mul_archimedean_mul_inv_dyadicTwoCoefficient_eq_one
    (n : ℕ) [NeZero n] :
    ENNReal.ofReal
          (specialOrthogonalRealGammaFactor n *
            archimedeanMassFactor n) *
        (ENNReal.ofReal
          (((twoPadicNormInvPow 2 n : ℚ) : ℝ)))⁻¹ =
      1 := by
  rw [specialOrthogonalRealGammaFactor_mul_archimedeanMassFactor]
  rw [twoPadicNormInvPow_eq_two_pow]
  rw [show (((((2 : ℚ) ^ n : ℚ) : ℝ))) = (2 : ℝ) ^ n by norm_num]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
  exact ENNReal.mul_inv_cancel (by positivity) (by simp)

/-- After cancelling the dyadic `2^n` coefficient, the closed real
determinant composition retains only the rational comparison determinant and
the form-determinant factor.  No tangent-rank power `2^d` occurs here. -/
theorem
    skewAdjointRealDeterminantGammaArchimedeanFactor_mul_inv_dyadicTwoCoefficient_closed
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ)
    (diag : Fin n → ℚ) (hdiag_pos : ∀ i, 0 < diag i)
    (hdiag : Matrix.skewAdjointCongruenceForm F W = Matrix.diagonal diag)
    [NeZero n] :
    ((|Matrix.skewAdjointRealCongruenceDetScalar F W|⁻¹ *
          (|positiveDiagonalSkewAdjointDetScalar diag hdiag_pos|⁻¹ *
            (|(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
              specialOrthogonalRealGammaFactor n))) *
          archimedeanMassFactor n) *
        (((twoPadicNormInvPow 2 n : ℚ) : ℝ))⁻¹ =
      |(Matrix.skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)| *
        (Real.sqrt |((F.det : ℚ) : ℝ)|) ^ (n - 1) := by
  rw [skewAdjointRealDeterminantGammaArchimedeanFactor_closed
    F hF hdet W diag hdiag_pos hdiag]
  rw [twoPadicNormInvPow_eq_two_pow]
  rw [show (((((2 : ℚ) ^ n : ℚ) : ℝ))) = (2 : ℝ) ^ n by norm_num]
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  calc
    |(Matrix.skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)| *
          ((2 : ℝ) ^ n *
            (Real.sqrt |((F.det : ℚ) : ℝ)|) ^ (n - 1)) *
        ((2 : ℝ) ^ n)⁻¹ =
      (|(Matrix.skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)| *
          (Real.sqrt |((F.det : ℚ) : ℝ)|) ^ (n - 1)) *
        ((2 : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ htwo, mul_one]

/-- The inverse dyadic intrinsic Cayley tangent modulus is independently the
rank-`d` factor `2^d`.  The preceding rank-`n` cancellation therefore does not
absorb this binary layer. -/
theorem
    ENNReal_inv_dyadicCayleyTangentModulus_eq_two_pow_tangentRank
    (L : PositiveDefiniteIntegralLattice n) :
    (↑(‖LinearMap.det
          (skewAdjointPadicCayleyTangentFactor
            L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹ =
      (2 : ℝ≥0∞) ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) := by
  have hnorm :
      ‖LinearMap.det
          (skewAdjointPadicCayleyTangentFactor
            L.rationalFormMatrix 2).toLinearMap‖₊ ≠ 0 := by
    rw [Matrix.nnnorm_det_skewAdjointPadicCayleyTangentFactor_two]
    positivity
  rw [← ENNReal.coe_inv hnorm]
  exact_mod_cast
    Matrix.inv_nnnorm_det_skewAdjointPadicCayleyTangentFactor_two
      L.rationalFormMatrix

end PositiveDefiniteIntegralLattice
