import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientCardinality
import SMSFormula.PadicSpecialOrthogonalDifferentialBadPrimeFiniteReductionBoundary
import SMSFormula.PadicCayleyTangentModulus

/-!
# The dyadic density gauge identity

This module specializes the general pointwise gauge-defect reduction to the
prime two.  It simplifies only the dyadic norm, the selected density
denominator exponent, and the explicit Schulze--Pillot two factor.  The
resulting equivalence keeps the density-source coordinate measure, the complete
ordinary reduction range, the rational comparison norm, and the
associated-bilinear quotient count unevaluated.

No dyadic density-source mass or pointwise gauge value is computed.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The dyadic prime as an element of the prime subtype. -/
abbrev localPadicSpecialOrthogonalDifferentialDyadicPrime :
    {p : ℕ // Nat.Prime p} :=
  ⟨2, Nat.prime_two⟩

/-- The explicit two/Gram gauge factor at the dyadic prime, with the selected
Schulze--Pillot power of two made literal. -/
theorem
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_two
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
        localPadicSpecialOrthogonalDifferentialDyadicPrime =
      (ENNReal.ofReal
        ((((2 : ℚ) ^ n : ℚ) : ℝ) *
          gramDetPadicNormFactor L 2))⁻¹ := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
    localPadicSpecialOrthogonalDifferentialDyadicPrime
  rw [twoPadicNormInvPow_eq_two_pow]

/-- At the dyadic prime, the intrinsic normalization has exactly the
factor `(2⁻¹)^d` in front of the density-source coordinate measure. -/
theorem
    localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_two
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
        2 =
      ((((2 : ℝ≥0)⁻¹) ^
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) : ℝ≥0) :
          ℝ≥0∞) *
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix 2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
            2) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold
    localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
  rw [Matrix.nnnorm_two_dyadic]
  norm_cast

/-- The selected dyadic coordinate normalization with both the rank power of
two and the selected density-depth exponent exposed. -/
theorem
    selectedCoordinateNormalizationENNReal_two
    (L : PositiveDefiniteIntegralLattice n) :
    L.selectedCoordinateNormalizationENNReal 2 =
      ENNReal.ofReal
        (((((2 : ℚ) ^ n) *
              ((2 : ℚ) ^
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                    2 *
                  Module.finrank ℚ
                    (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹ :
            ℚ) : ℝ) *
          gramDetPadicNormFactor L 2) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold selectedCoordinateNormalizationENNReal
  rw [twoPadicNormInvPow_eq_two_pow]
  rw [
    L.localDensityDenominatorExponent_eq_mul_finrank_skewAdjoint_rationalFormMatrix]
  norm_num

/-- The dyadic pointwise gauge target is exactly the displayed density-source
coordinate-mass equality.  No outer containment, additive saturation, or
residue-cardinality formula for the dyadic source is used. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_dyadicCoordinateMass
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
        localPadicSpecialOrthogonalDifferentialDyadicPrime ↔
      (((((2 : ℝ≥0)⁻¹) ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) :
            ℝ≥0) : ℝ≥0∞) *
          skewAdjointPadicCoordinateMeasure L.rationalFormMatrix 2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              2)) *
          (Nat.card
              (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                2) : ℝ≥0∞) =
        ((2 : ℝ≥0∞) ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹ *
          L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
            localPadicSpecialOrthogonalDifferentialDyadicPrime *
          (associatedBilinearDualQuotientCount L 2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                2) : ℝ≥0∞) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_intrinsicCoordinate_mul_ordinaryReductionRangeCard_eq_inv_primePow_mul_comparison_mul_quotientCount
      localPadicSpecialOrthogonalDifferentialDyadicPrime]
  rw [
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_two,
    L.localDensityDenominatorExponent_eq_mul_finrank_skewAdjoint_rationalFormMatrix]
  rfl

/-- The existing compact-open partition evaluates the dyadic density-source
coordinate measure at one literal, though noncanonical, common level. -/
theorem
    exists_dyadicDensityCongruenceSource_coordinateMeasure_commonBall
    (L : PositiveDefiniteIntegralLattice n) :
    ∃ level : ℕ,
      ∃ balls : Finset (Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule),
        ∃ center :
            Set (skewAdjointMatricesLieSubalgebra
                (L.rationalFormMatrix.map
                  (algebraMap ℚ ℚ_[2]))).toSubmodule →
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
                2,
          (∀ B ∈ balls,
            B = skewAdjointPadicTranslatedUniformCoordinateBall
              L.rationalFormMatrix 2 level (center B)) ∧
          (↑balls : Set (Set (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map
              (algebraMap ℚ ℚ_[2]))).toSubmodule)).PairwiseDisjoint id ∧
          (⋃ B ∈ balls, B) =
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              2 ∧
          skewAdjointPadicCoordinateMeasure L.rationalFormMatrix 2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
                2) =
            (balls.card : ℝ≥0∞) *
              ((2 : ℝ≥0∞) ^
                (level * Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹ := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact
    L.exists_localPadicSpecialOrthogonalDifferentialDensityCongruenceSource_coordinateMeasure_commonBall
      2

/-- The dyadic gauge identity in terms of common-ball coordinate data.  The common
level and ball count are existential and are not identified with the
selected-depth finite reduction carriers. -/
theorem
    exists_dyadicCommonBallData_gaugeDefect_eq_explicitTwoGramGaugeFactor_iff
    (L : PositiveDefiniteIntegralLattice n) :
    ∃ level : ℕ,
      ∃ balls : Finset (Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule),
        ∃ center :
            Set (skewAdjointMatricesLieSubalgebra
                (L.rationalFormMatrix.map
                  (algebraMap ℚ ℚ_[2]))).toSubmodule →
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
                2,
          (∀ B ∈ balls,
            B = skewAdjointPadicTranslatedUniformCoordinateBall
              L.rationalFormMatrix 2 level (center B)) ∧
          (↑balls : Set (Set (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map
              (algebraMap ℚ ℚ_[2]))).toSubmodule)).PairwiseDisjoint id ∧
          (⋃ B ∈ balls, B) =
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              2 ∧
          (L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime
                localPadicSpecialOrthogonalDifferentialDyadicPrime *
              (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
                localPadicSpecialOrthogonalDifferentialDyadicPrime)⁻¹ =
            L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
              localPadicSpecialOrthogonalDifferentialDyadicPrime ↔
            (((((2 : ℝ≥0)⁻¹) ^
                    Module.finrank ℚ
                      (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) :
                  ℝ≥0) : ℝ≥0∞) *
                ((balls.card : ℝ≥0∞) *
                  ((2 : ℝ≥0∞) ^
                    (level * Module.finrank ℚ
                      (skewAdjointMatricesLieSubalgebra
                        L.rationalFormMatrix)))⁻¹)) *
                (Nat.card
                    (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                      2) : ℝ≥0∞) =
              ((2 : ℝ≥0∞) ^
                  (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                      2 *
                    Module.finrank ℚ
                      (skewAdjointMatricesLieSubalgebra
                        L.rationalFormMatrix)))⁻¹ *
                L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
                  localPadicSpecialOrthogonalDifferentialDyadicPrime *
                (associatedBilinearDualQuotientCount L 2
                    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                      2) : ℝ≥0∞)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨level, balls, center, hcenter, hpairwise, hcover, hmeasure⟩ :=
    L.exists_dyadicDensityCongruenceSource_coordinateMeasure_commonBall
  refine ⟨level, balls, center, hcenter, hpairwise, hcover, ?_⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_dyadicCoordinateMass,
    hmeasure]

end PositiveDefiniteIntegralLattice
