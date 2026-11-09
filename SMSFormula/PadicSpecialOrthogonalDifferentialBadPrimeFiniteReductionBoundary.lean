import SMSFormula.PadicSpecialOrthogonalDifferentialBadPrimeGaugeDefect
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceIntrinsicCoordinateMass

/-!
# The bad-prime gauge defect in common finite-reduction coordinates

The pointwise gauge-defect target contains the reciprocal of the selected
dyadic/Gram coefficient, while the selected coordinate normalization contains
that same coefficient multiplied by the inverse prime power at the chosen
density-congruence depth.  Their product therefore leaves exactly that inverse
prime power.

This module substitutes that cancellation and the existing finite common-level
coordinate-ball decomposition into the pointwise target.  The resulting
formula retains the selected ball count, common level, ordinary reduction
cardinality, associated-bilinear quotient count, and complete fiber excess.
No finite-set equivalence between the chosen coordinate balls and either
finite reduction carrier is asserted.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped BigOperators ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The explicit reciprocal dyadic/Gram gauge factor cancels those same
coefficients in the selected coordinate normalization, leaving the literal
inverse prime power at the selected density-congruence depth. -/
theorem
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_mul_selectedCoordinateNormalizationENNReal
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q *
        L.selectedCoordinateNormalizationENNReal q.1 =
      ((q.1 : ℝ≥0∞) ^
        localDensityDenominatorExponent n
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            q.1))⁻¹ := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let e :=
    localDensityDenominatorExponent n
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
  let A : ℝ := ((twoPadicNormInvPow q.1 n : ℚ) : ℝ)
  let G : ℝ := gramDetPadicNormFactor L q.1
  let R : ℝ := (((q.1 : ℚ) ^ e : ℚ) : ℝ)
  have hA : 0 < A := by
    dsimp only [A]
    exact_mod_cast twoPadicNormInvPow_pos q.1 n
  have hG : 0 < G := by
    dsimp only [G]
    exact gramDetPadicNormFactor_pos L q.1
  have hR : 0 < R := by
    dsimp only [R]
    exact_mod_cast pow_pos (by exact_mod_cast q.2.pos : (0 : ℚ) < q.1) e
  have hbase0 : ENNReal.ofReal (A * G) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hA hG)
  have hbasetop : ENNReal.ofReal (A * G) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
  unfold selectedCoordinateNormalizationENNReal
  change
    (ENNReal.ofReal (A * G))⁻¹ *
        ENNReal.ofReal
          (((((twoPadicNormInvPow q.1 n : ℚ) *
            ((q.1 : ℚ) ^ e)⁻¹ : ℚ) : ℝ)) * G) =
      ((q.1 : ℝ≥0∞) ^ e)⁻¹
  rw [show
    (((((twoPadicNormInvPow q.1 n : ℚ) *
        ((q.1 : ℚ) ^ e)⁻¹ : ℚ) : ℝ)) * G) =
      (A * R⁻¹) * G by
    dsimp only [A, R]
    norm_num]
  rw [show (A * R⁻¹) * G = (A * G) * R⁻¹ by ring]
  rw [ENNReal.ofReal_mul (mul_nonneg hA.le hG.le)]
  rw [ENNReal.ofReal_inv_of_pos hR]
  rw [show ENNReal.ofReal R = (q.1 : ℝ≥0∞) ^ e by
    dsimp only [R]
    simp]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hbase0 hbasetop, one_mul]

/-- After the dyadic/Gram cancellation, the pointwise gauge-defect identity is
exactly a comparison between the intrinsic coordinate mass times the ordinary
reduction range and the selected inverse prime power times the rational
comparison norm and associated-bilinear quotient count. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_intrinsicCoordinate_mul_ordinaryReductionRangeCard_eq_inv_primePow_mul_comparison_mul_quotientCount
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q ↔
      L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
            q.1 *
          (Nat.card
              (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                q.1) : ℝ≥0∞) =
        ((q.1 : ℝ≥0∞) ^
            localDensityDenominatorExponent n
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                q.1))⁻¹ *
          L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q *
          (associatedBilinearDualQuotientCount L q.1
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                q.1) : ℝ≥0∞) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_coordinateMeasure_mul_ordinaryReductionRangeCard
      q]
  rw [← mul_assoc,
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_mul_selectedCoordinateNormalizationENNReal
      q]

/-- The same reduced target with the ordinary reduction cardinal split
literally into its associated-bilinear quotient count and selected fiber
excess. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_intrinsicCoordinate_mul_quotientCount_add_fiberExcess_eq_inv_primePow_mul_comparison_mul_quotientCount
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q ↔
      L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
            q.1 *
          ((associatedBilinearDualQuotientCount L q.1
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                  q.1) +
              L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess q.1 :
            ℕ) : ℝ≥0∞) =
        ((q.1 : ℝ≥0∞) ^
            localDensityDenominatorExponent n
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                q.1))⁻¹ *
          L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q *
          (associatedBilinearDualQuotientCount L q.1
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                q.1) : ℝ≥0∞) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_intrinsicCoordinate_mul_ordinaryReductionRangeCard_eq_inv_primePow_mul_comparison_mul_quotientCount
      q]
  rw [
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_add_fiberExcess
      q.1]

/-- A common finite-data form of the pointwise gauge identity.  It uses the
chosen finite common-level coordinate partition and states the pointwise gauge
identity using its exact ball count and mass, together with the ordinary finite
reduction range.

The theorem supplies no map from `balls` to that reduction range
or to the associated-bilinear quotient family. -/
theorem
    exists_commonBallData_gaugeDefect_eq_explicitTwoGramGaugeFactor_iff
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    ∃ level : ℕ,
      ∃ balls : Finset (Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))).toSubmodule),
        ∃ center :
            Set (skewAdjointMatricesLieSubalgebra
                (L.rationalFormMatrix.map
                  (algebraMap ℚ ℚ_[q.1]))).toSubmodule →
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
                q.1,
          (∀ B ∈ balls,
            B = skewAdjointPadicTranslatedUniformCoordinateBall
              L.rationalFormMatrix q.1 level (center B)) ∧
          (↑balls : Set (Set (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map
              (algebraMap ℚ ℚ_[q.1]))).toSubmodule)).PairwiseDisjoint id ∧
          (⋃ B ∈ balls, B) =
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              q.1 ∧
          balls.Nonempty ∧
          (L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
                (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
                  q)⁻¹ =
              L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
                q ↔
            ((‖(2 : ℚ_[q.1])‖₊ ^
                  Module.finrank ℚ
                    (skewAdjointMatricesLieSubalgebra
                      L.rationalFormMatrix) : ℝ≥0∞) *
                ((balls.card : ℝ≥0∞) *
                  ((q.1 : ℝ≥0∞) ^
                    (level * Module.finrank ℚ
                      (skewAdjointMatricesLieSubalgebra
                        L.rationalFormMatrix)))⁻¹)) *
                (Nat.card
                  (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                    q.1) : ℝ≥0∞) =
              ((q.1 : ℝ≥0∞) ^
                  localDensityDenominatorExponent n
                    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                      q.1))⁻¹ *
                L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q *
                (associatedBilinearDualQuotientCount L q.1
                    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                      q.1) : ℝ≥0∞)) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  obtain
      ⟨level, balls, center, hcenter, hpairwise, hcover, hcoordinate⟩ :=
    L.exists_localPadicSpecialOrthogonalDifferentialDensityCongruenceSource_coordinateMeasure_commonBall
      q.1
  have hballs : balls.Nonempty := by
    by_contra hempty
    have heq : balls = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero :=
      L.zero_mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        q.1
    have hzeroUnion : (0 :
        (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map
            (algebraMap ℚ ℚ_[q.1]))).toSubmodule) ∈ ⋃ B ∈ balls, B := by
      rw [hcover]
      exact hzero
    simp [heq] at hzeroUnion
  refine
    ⟨level, balls, center, hcenter, hpairwise, hcover, hballs, ?_⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_intrinsicCoordinate_mul_ordinaryReductionRangeCard_eq_inv_primePow_mul_comparison_mul_quotientCount
      q]
  unfold
    localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
  rw [hcoordinate]

end PositiveDefiniteIntegralLattice
