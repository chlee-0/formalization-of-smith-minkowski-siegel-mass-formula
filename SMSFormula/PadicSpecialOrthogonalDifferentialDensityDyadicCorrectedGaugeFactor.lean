import SMSFormula.RationalSpecialOrthogonalBinaryResidualCancellation
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicResidueCardinalityBoundary
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientCardinality

/-!
# The corrected dyadic pointwise gauge factor

The dyadic finite correspondence forces one more tangent-rank binary layer
than the original pointwise factor, before correction.  The global binary
computation identifies that layer as the inverse dyadic Cayley tangent
modulus and proves that it cancels the reciprocal real/Gram residual.

This module defines the corrected factor as a separate quantity; the original
explicit factor and the measures are unchanged.  The corrected pointwise
equality is reduced to the finite cardinality identity and proved from that
identity.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_dyadic_corrected_gauge_factor :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The corrected dyadic factor is the original explicit two/Gram factor
multiplied by the inverse intrinsic Cayley tangent modulus. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialCorrectedDyadicGaugeFactor
    (L : PositiveDefiniteIntegralLattice n) : ℝ≥0∞ :=
  (↑(‖LinearMap.det
      (skewAdjointPadicCayleyTangentFactor
        L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹ *
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
      localPadicSpecialOrthogonalDifferentialDyadicPrime

/-- The corrected factor exposes exactly one positive tangent-rank power of
two in front of the original explicit factor. -/
theorem
    localPadicSpecialOrthogonalDifferentialCorrectedDyadicGaugeFactor_eq_two_pow_tangentRank_mul_explicit
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialCorrectedDyadicGaugeFactor =
      (2 : ℝ≥0∞) ^
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) *
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime := by
  unfold localPadicSpecialOrthogonalDifferentialCorrectedDyadicGaugeFactor
  rw [L.ENNReal_inv_dyadicCayleyTangentModulus_eq_two_pow_tangentRank]

private theorem ennreal_eq_iff_mul_left_finite_corrected_dyadic
    {a b c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    a = b ↔ c * a = c * b := by
  constructor
  · exact fun h ↦ congrArg (fun z : ℝ≥0∞ ↦ c * z) h
  · intro h
    calc
      a = 1 * a := (one_mul a).symm
      _ = (c⁻¹ * c) * a := by
        rw [ENNReal.inv_mul_cancel hc0 hctop]
      _ = c⁻¹ * (c * a) := by rw [mul_assoc]
      _ = c⁻¹ * (c * b) := by rw [h]
      _ = (c⁻¹ * c) * b := by rw [mul_assoc]
      _ = 1 * b := by
        rw [ENNReal.inv_mul_cancel hc0 hctop]
      _ = b := one_mul b

private theorem ennreal_mul_inv_mul_mul_inv_eq_iff_corrected_dyadic
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
    apply
      (ennreal_eq_iff_mul_left_finite_corrected_dyadic hbd0 hbdtop).mpr
    calc
      (b * d) * (a * b⁻¹ * c * d⁻¹) =
          (a * c) * (b⁻¹ * b) * (d⁻¹ * d) := by ac_rfl
      _ = a * c := by
        rw [ENNReal.inv_mul_cancel hb0 hbtop,
          ENNReal.inv_mul_cancel hd0 hdtop, mul_one, mul_one]
      _ = (b * d) * x := by rw [h]; ac_rfl

/-- The local-correction equality may be tested against an arbitrary finite
factor before specializing to the corrected dyadic one. -/
private theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_factor_iff_intrinsicCoordinate_mul_ordinaryReductionRangeCard
    (L : PositiveDefiniteIntegralLattice n) (X : ℝ≥0∞) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime)⁻¹ = X ↔
      L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
            2 *
          (Nat.card
              (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                2) : ℝ≥0∞) =
        X *
            (L.selectedCoordinateNormalizationENNReal 2 *
              L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
                localPadicSpecialOrthogonalDifferentialDyadicPrime) *
          (associatedBilinearDualQuotientCount L 2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                2) : ℝ≥0∞) := by
  let D :=
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
      2
  let N := L.selectedCoordinateNormalizationENNReal 2
  let r :=
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection 2
  let c :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
      localPadicSpecialOrthogonalDifferentialDyadicPrime
  let Q :=
    associatedBilinearDualQuotientCount L 2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)
  let O :=
    Nat.card
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
        2)
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess 2
  have hN0 : N ≠ 0 :=
    L.selectedCoordinateNormalizationENNReal_ne_zero 2
  have hNtop : N ≠ ⊤ :=
    L.selectedCoordinateNormalizationENNReal_ne_top 2
  have hc0 : c ≠ 0 :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_zero
      localPadicSpecialOrthogonalDifferentialDyadicPrime
  have hctop : c ≠ ⊤ :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_top
      localPadicSpecialOrthogonalDifferentialDyadicPrime
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 :=
    L.ENNReal_coe_associatedBilinearDualQuotientCount_ne_zero_at_densityCongruenceDepth
      2
  have hQtop : (Q : ℝ≥0∞) ≠ ⊤ :=
    L.ENNReal_coe_associatedBilinearDualQuotientCount_ne_top_at_densityCongruenceDepth
      2
  have hOnat : O = Q + E := by
    simpa only [O, Q, E] using
      L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_add_fiberExcess
        2
  have hsum : ((Q + E : ℕ) : ℝ≥0∞) = r * (Q : ℝ≥0∞) := by
    simpa only [Q, E, r] using
      L.ENNReal_coe_associatedBilinearDualQuotientCount_add_densityFiberExcess_eq_densityFiberCorrection_mul_quotientCount
        2
  have hO : (O : ℝ≥0∞) = r * (Q : ℝ≥0∞) := by
    rw [hOnat]
    exact hsum
  change ((D * N⁻¹) * r) * c⁻¹ = X ↔
    D * (O : ℝ≥0∞) = X * (N * c) * (Q : ℝ≥0∞)
  rw [ennreal_mul_inv_mul_mul_inv_eq_iff_corrected_dyadic
    hN0 hNtop hc0 hctop]
  rw [hO]
  constructor
  · intro h
    calc
      D * (r * (Q : ℝ≥0∞)) = (D * r) * (Q : ℝ≥0∞) := by rw [mul_assoc]
      _ = (X * (N * c)) * (Q : ℝ≥0∞) := by rw [h]
  · intro h
    apply
      (ennreal_eq_iff_mul_left_finite_corrected_dyadic hQ0 hQtop).mpr
    calc
      (Q : ℝ≥0∞) * (D * r) = D * (r * (Q : ℝ≥0∞)) := by ac_rfl
      _ = D * (r * (Q : ℝ≥0∞)) := rfl
      _ = X * (N * c) * (Q : ℝ≥0∞) := h
      _ = (Q : ℝ≥0∞) * (X * (N * c)) := by ac_rfl

/-- After the fixed/form comparison norm is cancelled, the corrected dyadic
pointwise equality is exactly the displayed residue-coordinate mass equality
with the positive tangent-rank power retained on the right. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_correctedDyadicGaugeFactor_iff_dyadicResidueCoordinateMass
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialCorrectedDyadicGaugeFactor ↔
      (((((2 : ℝ≥0)⁻¹) ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) :
            ℝ≥0) : ℝ≥0∞) *
          ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
              2).ncard *
            ((2 : ℝ≥0∞) ^
              ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
                  padicValInt 2 L.pairingDeterminant) *
                Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹)) *
          (Nat.card
              (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                2) : ℝ≥0∞) =
        (2 : ℝ≥0∞) ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) *
          ((2 : ℝ≥0∞) ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹ *
          (associatedBilinearDualQuotientCount L 2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                2) : ℝ≥0∞) := by
  rw [
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_factor_iff_intrinsicCoordinate_mul_ordinaryReductionRangeCard,
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_two,
    L.skewAdjointPadicCoordinateMeasure_dyadicDensityCongruenceSourceAmbientSet_eq_comparisonNorm_mul_residueImage_ncard_mul_inv_pow,
    L.localPadicSpecialOrthogonalDifferentialCorrectedDyadicGaugeFactor_eq_two_pow_tangentRank_mul_explicit]
  let c :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
      localPadicSpecialOrthogonalDifferentialDyadicPrime
  let A : ℝ≥0∞ :=
    ((((2 : ℝ≥0)⁻¹) ^
      Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) : ℝ≥0) :
          ℝ≥0∞)
  let M : ℝ≥0∞ :=
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
        2).ncard *
      ((2 : ℝ≥0∞) ^
        ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
            padicValInt 2 L.pairingDeterminant) *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹
  let O : ℝ≥0∞ :=
    Nat.card
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
        2)
  let T : ℝ≥0∞ :=
    (2 : ℝ≥0∞) ^
      Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)
  let P : ℝ≥0∞ :=
    ((2 : ℝ≥0∞) ^
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 *
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹
  let Q : ℝ≥0∞ :=
    associatedBilinearDualQuotientCount L 2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)
  have hc0 : c ≠ 0 :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_zero
      localPadicSpecialOrthogonalDifferentialDyadicPrime
  have hctop : c ≠ ⊤ :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_top
      localPadicSpecialOrthogonalDifferentialDyadicPrime
  change (A * (c * M)) * O =
      (T *
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime) *
          (L.selectedCoordinateNormalizationENNReal 2 * c) * Q ↔
    (A * M) * O = T * P * Q
  have hES :
      L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
            localPadicSpecialOrthogonalDifferentialDyadicPrime *
          L.selectedCoordinateNormalizationENNReal 2 = P := by
    simpa only [P] using
      L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_mul_selectedCoordinateNormalization_two
  constructor
  · intro h
    apply (ennreal_eq_iff_mul_left_finite_corrected_dyadic hc0 hctop).mpr
    calc
      c * ((A * M) * O) = (A * (c * M)) * O := by ac_rfl
      _ = (T *
            L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
              localPadicSpecialOrthogonalDifferentialDyadicPrime) *
          (L.selectedCoordinateNormalizationENNReal 2 * c) * Q := h
      _ = c * (T *
          (L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
              localPadicSpecialOrthogonalDifferentialDyadicPrime *
            L.selectedCoordinateNormalizationENNReal 2) * Q) := by
        ac_rfl
      _ = c * (T * P * Q) := by rw [hES]
  · intro h
    have hc : c * ((A * M) * O) = c * (T * P * Q) :=
      (ennreal_eq_iff_mul_left_finite_corrected_dyadic hc0 hctop).mp h
    calc
      (A * (c * M)) * O = c * ((A * M) * O) := by ac_rfl
      _ = c * (T * P * Q) := hc
      _ = c * (T *
          (L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
              localPadicSpecialOrthogonalDifferentialDyadicPrime *
            L.selectedCoordinateNormalizationENNReal 2) * Q) := by
        rw [hES]
      _ = (T *
            L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
              localPadicSpecialOrthogonalDifferentialDyadicPrime) *
          (L.selectedCoordinateNormalizationENNReal 2 * c) * Q := by
        ac_rfl

private theorem ennreal_mul_inv_mul_eq_inv_mul_iff_corrected_dyadic
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

/-- The corrected dyadic residue-coordinate mass equality is equivalent to
the natural cardinality identity with exponent `(v₂(pairingDeterminant)+2)*d`. -/
theorem
    correctedDyadicResidueCoordinateMass_eq_iff_ncard_mul_natCard_eq_two_pow_add_two_pairingDeterminantVal_mul_quotientCount
    (L : PositiveDefiniteIntegralLattice n) :
    (((((2 : ℝ≥0)⁻¹) ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) :
            ℝ≥0) : ℝ≥0∞) *
          ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
              2).ncard *
            ((2 : ℝ≥0∞) ^
              ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
                  padicValInt 2 L.pairingDeterminant) *
                Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹)) *
          (Nat.card
              (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                2) : ℝ≥0∞) =
        (2 : ℝ≥0∞) ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) *
          ((2 : ℝ≥0∞) ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹ *
          (associatedBilinearDualQuotientCount L 2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                2) : ℝ≥0∞) ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          2).ncard *
          Nat.card
            (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
              2) =
        2 ^
            ((padicValInt 2 L.pairingDeterminant + 2) *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          associatedBilinearDualQuotientCount L 2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              2) := by
  let d :=
    Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  let v := padicValInt 2 L.pairingDeterminant
  let N :=
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
      2).ncard
  let O :=
    Nat.card
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
        2)
  let Q :=
    associatedBilinearDualQuotientCount L 2 k
  let P : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (k * d)
  let V : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((v + 1) * d)
  let T : ℝ≥0∞ := (2 : ℝ≥0∞) ^ d
  have htwoA :
      (((((2 : ℝ≥0)⁻¹) ^ d : ℝ≥0) : ℝ≥0∞)) = T⁻¹ := by
    change
      (↑(((2 : ℝ≥0)⁻¹) ^ d) : ℝ≥0∞) =
        (↑((2 : ℝ≥0) ^ d) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by positivity : (2 : ℝ≥0) ^ d ≠ 0)]
    congr 1
    exact inv_pow (2 : ℝ≥0) d
  have hpow : T * ((2 : ℝ≥0∞) ^ (v * d)) = V := by
    dsimp only [T, V]
    rw [Nat.add_mul, one_mul, pow_add]
    ac_rfl
  have hP0 : P ≠ 0 := pow_ne_zero _ (by norm_num)
  have hPtop : P ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hV0 : V ≠ 0 := pow_ne_zero _ (by norm_num)
  have hVtop : V ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hT0 : T ≠ 0 := pow_ne_zero _ (by norm_num)
  have hTtop : T ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hVT : V * T = ((2 ^ ((v + 2) * d) : ℕ) : ℝ≥0∞) := by
    dsimp only [V, T]
    rw [← pow_add]
    norm_cast
    congr 2
    ring
  rw [htwoA]
  rw [Nat.add_mul, pow_add]
  change
    ((T⁻¹ *
          ((N : ℝ≥0∞) *
            (P * (2 : ℝ≥0∞) ^ (v * d))⁻¹)) *
        (O : ℝ≥0∞) =
      T * P⁻¹ * (Q : ℝ≥0∞)) ↔
      N * O = 2 ^ ((v + 2) * d) * Q
  have hnormalize :
      (T⁻¹ *
          ((N : ℝ≥0∞) *
            (P * (2 : ℝ≥0∞) ^ (v * d))⁻¹)) *
          (O : ℝ≥0∞) =
        ((N : ℝ≥0∞) * (P * V)⁻¹) * (O : ℝ≥0∞) := by
    have hpowInv :
        T⁻¹ * ((2 : ℝ≥0∞) ^ (v * d))⁻¹ = V⁻¹ := by
      calc
        T⁻¹ * ((2 : ℝ≥0∞) ^ (v * d))⁻¹ =
            (T * (2 : ℝ≥0∞) ^ (v * d))⁻¹ := by
              rw [ENNReal.mul_inv (Or.inl hT0) (Or.inl hTtop)]
        _ = V⁻¹ := congrArg Inv.inv hpow
    have hPVInv : (P * V)⁻¹ = P⁻¹ * V⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hP0) (Or.inl hPtop)]
    rw [ENNReal.mul_inv (Or.inl hP0) (Or.inl hPtop)]
    calc
      (T⁻¹ *
            ((N : ℝ≥0∞) *
              (P⁻¹ * ((2 : ℝ≥0∞) ^ (v * d))⁻¹))) *
          (O : ℝ≥0∞) =
        ((N : ℝ≥0∞) *
          (P⁻¹ *
            (T⁻¹ * ((2 : ℝ≥0∞) ^ (v * d))⁻¹))) *
            (O : ℝ≥0∞) := by ac_rfl
      _ = ((N : ℝ≥0∞) * (P⁻¹ * V⁻¹)) * (O : ℝ≥0∞) := by
        rw [hpowInv]
      _ = ((N : ℝ≥0∞) * (P * V)⁻¹) * (O : ℝ≥0∞) := by
        rw [hPVInv]
  rw [hnormalize]
  rw [show T * P⁻¹ * (Q : ℝ≥0∞) = P⁻¹ * (T * (Q : ℝ≥0∞)) by
    ac_rfl]
  change
    ((N : ℝ≥0∞) * (P * V)⁻¹) * (O : ℝ≥0∞) =
        P⁻¹ * (T * (Q : ℝ≥0∞)) ↔
      N * O = 2 ^ ((v + 2) * d) * Q
  rw [ennreal_mul_inv_mul_eq_inv_mul_iff_corrected_dyadic
    hP0 hPtop hV0 hVtop]
  rw [← mul_assoc, hVT]
  norm_cast

/-- The corrected dyadic pointwise equality is equivalent exactly to the
certified natural residue-cardinality identity. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_correctedDyadicGaugeFactor_iff_dyadicResidueCardinalityPrimePower
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialCorrectedDyadicGaugeFactor ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          2).ncard *
          Nat.card
            (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
              2) =
        2 ^
            ((padicValInt 2 L.pairingDeterminant + 2) *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          associatedBilinearDualQuotientCount L 2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              2) := by
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_correctedDyadicGaugeFactor_iff_dyadicResidueCoordinateMass,
    L.correctedDyadicResidueCoordinateMass_eq_iff_ncard_mul_natCard_eq_two_pow_add_two_pairingDeterminantVal_mul_quotientCount]

/-- The completed shifted dyadic finite correspondence proves the corrected
dyadic pointwise equality. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_correctedDyadicGaugeFactor
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialCorrectedDyadicGaugeFactor := by
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_correctedDyadicGaugeFactor_iff_dyadicResidueCardinalityPrimePower]
  exact
    L.dyadicResidueImage_ncard_mul_ordinaryReductionRangeCard_eq_two_pow_add_two_pairingDeterminantVal_mul_quotientCount

end PositiveDefiniteIntegralLattice
