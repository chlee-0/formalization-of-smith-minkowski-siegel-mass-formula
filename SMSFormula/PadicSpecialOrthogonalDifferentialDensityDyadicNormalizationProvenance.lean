import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientCardinality
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicResidueCardinalityBoundary

/-!
# Comparing the two dyadic binary normalizations

The finite correspondence forces exponent `(v₂(pairingDeterminant)+2)*d`,
whereas the analytic dyadic gauge statement has exponent
`(v₂(pairingDeterminant)+1)*d`.  This module combines the two statements without
altering either normalization, records the residual equality required
by the pointwise target, and isolates the exact coefficient produced
by the Cayley tangent norm and the selected Schulze--Pillot normalization.

No dyadic gauge value or corrected normalization is asserted here.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_dyadic_normalization_provenance_audit :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- After substituting the completed finite correspondence, the current
dyadic gauge target is equivalent to equality of the two adjacent certified
binary exponents.  No cancellation of the quotient count is used. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_dyadic_adjacent_power_residual
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
        localPadicSpecialOrthogonalDifferentialDyadicPrime ↔
      2 ^
            ((padicValInt 2 L.pairingDeterminant + 2) *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          associatedBilinearDualQuotientCount L 2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              2) =
        2 ^
            ((padicValInt 2 L.pairingDeterminant + 1) *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          associatedBilinearDualQuotientCount L 2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              2) := by
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_dyadicResidueCardinalityPrimePower,
    L.dyadicResidueImage_ncard_mul_ordinaryReductionRangeCard_eq_two_pow_add_two_pairingDeterminantVal_mul_quotientCount]

/-- At the dyadic prime the current explicit two/Gram factor cancels the
selected Schulze--Pillot coefficient completely, leaving only the selected
depth prime power.  In particular, this interface contributes no tangent-rank
power of two. -/
theorem
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_mul_selectedCoordinateNormalization_two
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        L.selectedCoordinateNormalizationENNReal 2 =
      ((2 : ℝ≥0∞) ^
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra
              L.rationalFormMatrix)))⁻¹ := by
  simpa only [
    localPadicSpecialOrthogonalDifferentialDyadicPrime,
    L.localDensityDenominatorExponent_eq_mul_finrank_skewAdjoint_rationalFormMatrix] using
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_mul_selectedCoordinateNormalizationENNReal
      localPadicSpecialOrthogonalDifferentialDyadicPrime

/-- Combining the literal dyadic Cayley tangent density with the preceding
complete coefficient cancellation gives exactly the inverse power at depth
`k+1`.  Together with the residual theorem, this shows that the unmatched
binary layer is not hidden in the fixed/form comparison norm or in a partial
two/Gram cancellation; deciding on which side it belongs remains a separate
normalization question. -/
theorem
    dyadicIntrinsicTwoNorm_mul_explicitFactor_mul_selectedNormalization_eq_inv_two_pow_succ_depth
    (L : PositiveDefiniteIntegralLattice n) :
    (↑(((2 : ℝ≥0)⁻¹) ^
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) : ℝ≥0∞) *
      (L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        L.selectedCoordinateNormalizationENNReal 2) =
      ((2 : ℝ≥0∞) ^
        ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
            1) *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra
              L.rationalFormMatrix)))⁻¹ := by
  let d :=
    Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  have htwo :
      (((((2 : ℝ≥0)⁻¹) ^ d : ℝ≥0) : ℝ≥0∞)) =
        ((2 : ℝ≥0∞) ^ d)⁻¹ := by
    change
      (↑(((2 : ℝ≥0)⁻¹) ^ d) : ℝ≥0∞) =
        (↑((2 : ℝ≥0) ^ d) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by positivity : (2 : ℝ≥0) ^ d ≠ 0)]
    congr 1
    exact inv_pow (2 : ℝ≥0) d
  rw [show
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        L.selectedCoordinateNormalizationENNReal 2 =
      ((2 : ℝ≥0∞) ^ (k * d))⁻¹ by
        simpa only [k, d] using
          L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_mul_selectedCoordinateNormalization_two]
  change
    (((((2 : ℝ≥0)⁻¹) ^ d : ℝ≥0) : ℝ≥0∞)) *
        ((2 : ℝ≥0∞) ^ (k * d))⁻¹ =
      ((2 : ℝ≥0∞) ^ ((k + 1) * d))⁻¹
  rw [htwo]
  rw [← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp))]
  rw [← pow_add]
  congr 2
  ring

end PositiveDefiniteIntegralLattice
