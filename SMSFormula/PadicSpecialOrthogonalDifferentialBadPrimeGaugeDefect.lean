import SMSFormula.RationalSpecialOrthogonalBadPrimeUnitNormalization
import SMSFormula.PadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityFiberCorrection

/-!
# The pointwise bad-prime differential gauge defect

The global raw differential normalization is the product of pointwise
local corrections divided by the p-adic norm of the rational
basis-comparison determinant.  This module fixes the orientation of
the expected dyadic/Gram factor directly from the selected Schulze--Pillot
coordinate normalization: it is the reciprocal of the
`|2|_p^{-n}` and Gram-determinant coefficient.

At an arbitrary prime, the desired pointwise identity is proved equivalent to
one equality involving the density-adapted coordinate mass, the selected
congruence depth, the associated-bilinear quotient count, and the complete
ordinary-reduction fiber excess.  No bad-prime coordinate mass or fiber
cardinality is evaluated here.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The p-adic norm of the rational fixed/form-adapted basis-comparison
determinant at a prime. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) : ℝ≥0∞ :=
  Rat.padicNormENNRealAtPrime
    (skewAdjointFixedFormElementaryDetScalar
      L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero)
    q

/-- The explicitly oriented local dyadic/Gram gauge factor.  The inverse is
outside the complete positive selected coefficient, so the half-integer power
`Real.rpow` in `gramDetPadicNormFactor` remains literal. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) : ℝ≥0∞ :=
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  (ENNReal.ofReal
    ((((twoPadicNormInvPow q.1 n : ℚ) : ℝ) *
      gramDetPadicNormFactor L q.1)))⁻¹

/-- The pointwise comparison norm is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q ≠ 0 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
  simpa only [Rat.padicNormENNRealAtPrime] using
    ENNReal_coe_nnnorm_skewAdjointFixedFormElementaryDetScalar_ne_zero
      q.1 L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero

/-- The pointwise comparison norm is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_top
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q ≠ ⊤ := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
  simpa only [Rat.padicNormENNRealAtPrime] using
    ENNReal_coe_nnnorm_skewAdjointFixedFormElementaryDetScalar_ne_top
      q.1 L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero

/-- The explicitly oriented dyadic/Gram gauge factor is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
        q ≠ 0 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
  apply ENNReal.inv_ne_zero.mpr
  exact ENNReal.ofReal_ne_top

/-- The explicitly oriented dyadic/Gram gauge factor is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_ne_top
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
        q ≠ ⊤ := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
  apply ENNReal.inv_ne_top.mpr
  apply ENNReal.ofReal_ne_zero_iff.mpr
  have htwo :
      0 < (((twoPadicNormInvPow q.1 n : ℚ) : ℝ)) := by
    exact_mod_cast twoPadicNormInvPow_pos q.1 n
  exact mul_pos htwo (gramDetPadicNormFactor_pos L q.1)

private theorem ennreal_eq_iff_mul_right_finite
    {a b c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    a = b ↔ a * c = b * c := by
  constructor
  · exact fun h ↦ congrArg (fun z : ℝ≥0∞ ↦ z * c) h
  · intro h
    calc
      a = a * 1 := (mul_one a).symm
      _ = a * (c * c⁻¹) := by
        rw [ENNReal.mul_inv_cancel hc0 hctop]
      _ = (a * c) * c⁻¹ := by rw [mul_assoc]
      _ = (b * c) * c⁻¹ := by rw [h]
      _ = b * (c * c⁻¹) := by rw [mul_assoc]
      _ = b * 1 := by rw [ENNReal.mul_inv_cancel hc0 hctop]
      _ = b := mul_one b

private theorem ennreal_mul_inv_mul_mul_inv_eq_iff
    {a b c d x : ℝ≥0∞}
    (hb0 : b ≠ 0) (hbtop : b ≠ ⊤)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) :
    a * b⁻¹ * c * d⁻¹ = x ↔ a * c = x * (b * d) := by
  have hbd0 : b * d ≠ 0 := mul_ne_zero hb0 hd0
  have hbdtop : b * d ≠ ⊤ := ENNReal.mul_ne_top hbtop hdtop
  constructor
  · intro h
    calc
      a * c = (a * b⁻¹ * c * d⁻¹) * (b * d) := by
        rw [show (a * b⁻¹ * c * d⁻¹) * (b * d) =
            (a * c) * (b⁻¹ * b) * (d⁻¹ * d) by ac_rfl,
          ENNReal.inv_mul_cancel hb0 hbtop,
          ENNReal.inv_mul_cancel hd0 hdtop, mul_one, mul_one]
      _ = x * (b * d) := by rw [h]
  · intro h
    apply (ennreal_eq_iff_mul_right_finite hbd0 hbdtop).mpr
    calc
      (a * b⁻¹ * c * d⁻¹) * (b * d) =
          (a * c) * (b⁻¹ * b) * (d⁻¹ * d) := by ac_rfl
      _ = a * c := by
        rw [ENNReal.inv_mul_cancel hb0 hbtop,
          ENNReal.inv_mul_cancel hd0 hdtop, mul_one, mul_one]
      _ = x * (b * d) := h

/-- Dividing the local correction by the rational comparison norm gives the
explicit dyadic/Gram factor exactly when the intrinsic coordinate mass times
the complete fiber correction equals the selected coordinate normalization
times the comparison norm and that explicit factor. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_intrinsicCoordinate_mul_fiberCorrection
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q ↔
      L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
            q.1 *
          L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection q.1 =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
            q *
          (L.selectedCoordinateNormalizationENNReal q.1 *
            L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let D :=
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
      q.1
  let N := L.selectedCoordinateNormalizationENNReal q.1
  let r :=
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection q.1
  let c :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q
  let X :=
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
      q
  have hN0 : N ≠ 0 :=
    L.selectedCoordinateNormalizationENNReal_ne_zero q.1
  have hNtop : N ≠ ⊤ :=
    L.selectedCoordinateNormalizationENNReal_ne_top q.1
  have hc0 : c ≠ 0 :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_zero q
  have hctop : c ≠ ⊤ :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_top q
  change ((D * N⁻¹) * r) * c⁻¹ = X ↔ D * r = X * (N * c)
  simpa only [mul_assoc] using
    (ennreal_mul_inv_mul_mul_inv_eq_iff hN0 hNtop hc0 hctop :
      D * N⁻¹ * r * c⁻¹ = X ↔ D * r = X * (N * c))

/-- The pointwise gauge identity is equivalent to an explicit equation with every
selected-depth ingredient visible.
The left side contains the density-adapted coordinate mass and the complete
ordinary-range excess `Q + E`; the right side contains the dyadic
power, congruence depth, Gram `Real.rpow`, comparison norm, and associated-
bilinear quotient count `Q`. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_coordinateMeasure_mul_quotientCount_add_fiberExcess
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q ↔
      ((‖(2 : ℚ_[q.1])‖₊ ^
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix) : ℝ≥0∞) *
          skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              q.1)) *
          ((associatedBilinearDualQuotientCount L q.1
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                  q.1) +
              L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess q.1 :
            ℕ) : ℝ≥0∞) =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
            q *
            (ENNReal.ofReal
                (((twoPadicNormInvPow q.1 n *
                    ((q.1 : ℚ) ^
                      localDensityDenominatorExponent n
                        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                          q.1))⁻¹ : ℚ) : ℝ) *
                  gramDetPadicNormFactor L q.1) *
              L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q) *
          (associatedBilinearDualQuotientCount L q.1
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                q.1) : ℝ≥0∞) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let D :=
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
      q.1
  let N := L.selectedCoordinateNormalizationENNReal q.1
  let r :=
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection q.1
  let c :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q
  let X :=
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
      q
  let Q :=
    associatedBilinearDualQuotientCount L q.1
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
  let E := L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess q.1
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 :=
    L.ENNReal_coe_associatedBilinearDualQuotientCount_ne_zero_at_densityCongruenceDepth
      q.1
  have hQtop : (Q : ℝ≥0∞) ≠ ⊤ :=
    L.ENNReal_coe_associatedBilinearDualQuotientCount_ne_top_at_densityCongruenceDepth
      q.1
  have hsum : ((Q + E : ℕ) : ℝ≥0∞) = r * (Q : ℝ≥0∞) := by
    simpa only [Q, E, r] using
      L.ENNReal_coe_associatedBilinearDualQuotientCount_add_densityFiberExcess_eq_densityFiberCorrection_mul_quotientCount
        q.1
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_intrinsicCoordinate_mul_fiberCorrection
      q]
  change D * r = X * (N * c) ↔ D * ((Q + E : ℕ) : ℝ≥0∞) =
    X * (N * c) * (Q : ℝ≥0∞)
  rw [ennreal_eq_iff_mul_right_finite hQ0 hQtop]
  rw [hsum]
  constructor <;> intro h <;> simpa only [mul_assoc] using h

/-- Replacing `Q + E` by the equal cardinality of the selected ordinary
reduction range gives the same equivalent form of the pointwise identity. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_coordinateMeasure_mul_ordinaryReductionRangeCard
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
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
            q *
            (L.selectedCoordinateNormalizationENNReal q.1 *
              L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q) *
          (associatedBilinearDualQuotientCount L q.1
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                q.1) : ℝ≥0∞) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_coordinateMeasure_mul_quotientCount_add_fiberExcess
      q]
  rw [
    ← L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_add_fiberExcess
      q.1]
  rfl

/-- The chosen orientation agrees with the completed good-prime calculation:
outside the bad set both the gauge defect and the explicit dyadic/Gram factor
are one. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  have hc0 :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_zero q
  have hctop :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_top q
  have hq_two : q.1 ≠ 2 :=
    L.not_mem_massBadPrimeSet_ne_two hq
  have hgram : gramDetPadicNormFactor L q.1 = 1 :=
    L.gramDetPadicNormFactor_eq_one_of_not_mem_massBadPrimeSet
      q hq
  rw [show L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q =
      L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q by
    simpa only [
      localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime,
      localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime,
      Rat.padicNormENNRealAtPrime] using
      L.localPadicSpecialOrthogonalDifferentialLocalCorrection_eq_comparisonNorm_of_not_mem_massBadPrimeSet
        q hq]
  rw [ENNReal.mul_inv_cancel hc0 hctop]
  unfold
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
  rw [twoPadicNormInvPow_eq_one_of_ne_two hq_two, hgram]
  norm_num

end PositiveDefiniteIntegralLattice
