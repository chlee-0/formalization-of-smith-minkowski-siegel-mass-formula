import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceResidueCardinalityBoundary
import SMSFormula.PadicSpecialOrthogonalDifferentialGoodPrimeDensityCongruenceElementaryBallMeasure
import SMSFormula.PadicCayleyTangentModulus

/-!
# The odd-prime density condition as a natural cardinality identity

At an odd prime the norm of two is one.  The selected local-density
denominator exponent is the density depth times the skew-adjoint tangent rank,
whereas the prescribed form-coordinate residue level includes the additional
valuation of the Gram determinant.  Cancelling the common positive finite
prime power therefore turns the remaining ENNReal gauge identity into one
natural-number cardinality identity.

This module proves only equivalences with that identity.  It does not assert
the identity or construct a map between the finite carriers.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private theorem ennreal_mul_inv_mul_eq_inv_mul_iff
    {a b c p v : ℝ≥0∞}
    (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤) :
    (a * (p * v)⁻¹) * b = p⁻¹ * c ↔ a * b = v * c := by
  have hpv0 : p * v ≠ 0 := mul_ne_zero hp0 hv0
  have hpvtop : p * v ≠ ⊤ := ENNReal.mul_ne_top hptop hvtop
  constructor
  · intro h
    calc
      a * b = ((a * (p * v)⁻¹) * b) * (p * v) := by
        rw [show ((a * (p * v)⁻¹) * b) * (p * v) =
            (a * b) * ((p * v)⁻¹ * (p * v)) by ac_rfl,
          ENNReal.inv_mul_cancel hpv0 hpvtop, mul_one]
      _ = (p⁻¹ * c) * (p * v) := by rw [h]
      _ = v * c := by
        rw [show (p⁻¹ * c) * (p * v) =
            (p⁻¹ * p) * (v * c) by ac_rfl,
          ENNReal.inv_mul_cancel hp0 hptop, one_mul]
  · intro h
    have hmul :
        ((a * (p * v)⁻¹) * b) * (p * v) =
          (p⁻¹ * c) * (p * v) := by
      calc
        ((a * (p * v)⁻¹) * b) * (p * v) = a * b := by
          rw [show ((a * (p * v)⁻¹) * b) * (p * v) =
              (a * b) * ((p * v)⁻¹ * (p * v)) by ac_rfl,
            ENNReal.inv_mul_cancel hpv0 hpvtop, mul_one]
        _ = v * c := h
        _ = (p⁻¹ * c) * (p * v) := by
          rw [show (p⁻¹ * c) * (p * v) =
              (p⁻¹ * p) * (v * c) by ac_rfl,
            ENNReal.inv_mul_cancel hp0 hptop, one_mul]
    calc
      (a * (p * v)⁻¹) * b =
          ((a * (p * v)⁻¹) * b) * 1 := (mul_one _).symm
      _ = ((a * (p * v)⁻¹) * b) * ((p * v) * (p * v)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hpv0 hpvtop]
      _ = ((a * (p * v)⁻¹) * b) * (p * v) * (p * v)⁻¹ := by
        rw [← mul_assoc]
      _ = (p⁻¹ * c) * (p * v) * (p * v)⁻¹ := by rw [hmul]
      _ = p⁻¹ * c := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hpv0 hpvtop, mul_one]

/-- The selected local-density denominator exponent is the density
depth times the rational skew-adjoint tangent rank. -/
theorem
    localDensityDenominatorExponent_eq_mul_finrank_skewAdjoint_rationalFormMatrix
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ) :
    localDensityDenominatorExponent n k =
      k * Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) :=
  (L.mul_finrank_skewAdjoint_rationalFormMatrix_eq_localDensityDenominatorExponent
    k).symm

/-- Expanding the prescribed residue level splits its prime-power exponent
into the selected density denominator exponent and the exact Gram-determinant
valuation loss. -/
theorem
    densityCongruenceFormCoordinateResidueLevel_mul_finrank_eq_densityDenominatorExponent_add_pairingDeterminantVal_mul_finrank
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          p *
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) =
      localDensityDenominatorExponent n
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) +
        padicValInt p L.pairingDeterminant *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) := by
  unfold
    localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
  rw [Nat.add_mul,
    L.mul_finrank_skewAdjoint_rationalFormMatrix_eq_localDensityDenominatorExponent]

/-- At an odd prime, the residual ENNReal coordinate-mass equality is
equivalent exactly to the natural-number cardinality identity left after
cancelling the selected density prime power. -/
theorem
    densityResidueCoordinateMass_mul_ordinaryReductionRangeCard_eq_inv_densityPrimePow_mul_associatedBilinearQuotientCount_iff_ncard_mul_natCard_eq_pairingDeterminantPrimePow_mul_quotientCount
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq2 : q.1 ≠ 2) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    ((‖(2 : ℚ_[q.1])‖₊ ^
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix) : ℝ≥0∞) *
          ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
              q.1).ncard *
            ((q.1 : ℝ≥0∞) ^
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
                  q.1 *
                Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹)) *
          (Nat.card
              (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                q.1) : ℝ≥0∞) =
        ((q.1 : ℝ≥0∞) ^
            localDensityDenominatorExponent n
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                q.1))⁻¹ *
          (associatedBilinearDualQuotientCount L q.1
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                q.1) : ℝ≥0∞) ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          q.1).ncard *
          Nat.card
            (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
              q.1) =
        q.1 ^
            (padicValInt q.1 L.pairingDeterminant *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          associatedBilinearDualQuotientCount L q.1
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [Matrix.nnnorm_two_padic_eq_one_of_ne_two q.1 hq2, ENNReal.coe_one,
    one_pow, one_mul,
    L.densityCongruenceFormCoordinateResidueLevel_mul_finrank_eq_densityDenominatorExponent_add_pairingDeterminantVal_mul_finrank
      q.1,
    pow_add]
  let N :=
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
      q.1).ncard
  let O :=
    Nat.card
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
        q.1)
  let Q :=
    associatedBilinearDualQuotientCount L q.1
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
  let P : ℝ≥0∞ :=
    (q.1 : ℝ≥0∞) ^
      localDensityDenominatorExponent n
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
  let V : ℝ≥0∞ :=
    (q.1 : ℝ≥0∞) ^
      (padicValInt q.1 L.pairingDeterminant *
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix))
  have hq0 : (q.1 : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast q.2.ne_zero
  have hqtop : (q.1 : ℝ≥0∞) ≠ ⊤ := by simp
  have hP0 : P ≠ 0 := pow_ne_zero _ hq0
  have hPtop : P ≠ ⊤ := ENNReal.pow_ne_top hqtop
  have hV0 : V ≠ 0 := pow_ne_zero _ hq0
  have hVtop : V ≠ ⊤ := ENNReal.pow_ne_top hqtop
  have hV : V =
      ((q.1 ^
        (padicValInt q.1 L.pairingDeterminant *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) : ℕ) :
        ℝ≥0∞) := by
    dsimp only [V]
    norm_cast
  change
    (((N : ℝ≥0∞) * (P * V)⁻¹) * (O : ℝ≥0∞) =
        P⁻¹ * (Q : ℝ≥0∞)) ↔
      N * O =
        q.1 ^
            (padicValInt q.1 L.pairingDeterminant *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) * Q
  rw [ennreal_mul_inv_mul_eq_inv_mul_iff hP0 hPtop hV0 hVtop]
  rw [hV]
  norm_cast

/-- At an odd prime, the pointwise gauge-defect target itself is equivalent
to the exact remaining natural-number residue-cardinality identity. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_densityResidueCardinalityPrimePower
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq2 : q.1 ≠ 2) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          q.1).ncard *
          Nat.card
            (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
              q.1) =
        q.1 ^
            (padicValInt q.1 L.pairingDeterminant *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          associatedBilinearDualQuotientCount L q.1
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_densityResidueCardinality
      q hq2,
    L.densityResidueCoordinateMass_mul_ordinaryReductionRangeCard_eq_inv_densityPrimePow_mul_associatedBilinearQuotientCount_iff_ncard_mul_natCard_eq_pairingDeterminantPrimePow_mul_quotientCount
      q hq2]

/-- The same odd-prime cardinality equivalence, with the ordinary reduction
range split into the associated-bilinear quotient count and the fiber
excess. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_densityResidueCardinality_mul_quotientCount_add_fiberExcess
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq2 : q.1 ≠ 2) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          q.1).ncard *
          (associatedBilinearDualQuotientCount L q.1
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                  q.1) +
            L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess q.1) =
        q.1 ^
            (padicValInt q.1 L.pairingDeterminant *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          associatedBilinearDualQuotientCount L q.1
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_densityResidueCardinalityPrimePower
      q hq2,
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_add_fiberExcess
      q.1]

end PositiveDefiniteIntegralLattice
