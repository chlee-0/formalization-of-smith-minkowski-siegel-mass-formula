import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateMass
import SMSFormula.SkewAdjointPadicElementaryCoordinateMeasureScale
import SMSFormula.PadicSpecialOrthogonalDifferentialBadPrimeFiniteReductionBoundary

/-!
# The odd-prime density gauge defect as a residue-cardinality identity

The explicit form-coordinate residue decomposition evaluates the density
source using the form-adapted comparison measure.  This module transports that
evaluation back to the fixed-coordinate measure through the rational
basis-comparison norm.  It then cancels that same finite nonzero norm from the
pointwise gauge-defect criterion.

The resulting statement is only an equivalence with a finite-cardinality and
prime-power identity.  No equality between the residue image and either
stabilizer-reduction carrier is asserted.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance densityResidueBoundaryMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance densityResidueBoundaryBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

private theorem ennreal_eq_iff_mul_left_finite
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

/-- On the density source, the fixed-coordinate mass is the p-adic rational
basis-comparison norm times the form-coordinate mass. -/
theorem
    skewAdjointPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_comparisonNorm_mul_formCoordinateMeasure
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          q.1) =
      L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q *
        skewAdjointFormElementaryPadicCoordinateMeasure q.1
          L.rationalFormMatrix (L.form_symm.map (algebraMap ℤ ℚ))
            L.rationalFormMatrix_det_ne_zero
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
            q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let s :=
    skewAdjointFixedFormElementaryDetScalar
      L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero
  let cNN : ℝ≥0 := ‖algebraMap ℚ ℚ_[q.1] s‖₊
  let c : ℝ≥0∞ := cNN
  let C :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
      q.1
  have hc0 : c ≠ 0 := by
    exact
      ENNReal_coe_nnnorm_skewAdjointFixedFormElementaryDetScalar_ne_zero
        q.1 L.rationalFormMatrix
        (L.form_symm.map (algebraMap ℤ ℚ))
        L.rationalFormMatrix_det_ne_zero
  have hctop : c ≠ ⊤ := by
    exact
      ENNReal_coe_nnnorm_skewAdjointFixedFormElementaryDetScalar_ne_top
        q.1 L.rationalFormMatrix
        (L.form_symm.map (algebraMap ℤ ℚ))
        L.rationalFormMatrix_det_ne_zero
  have hcNN0 : cNN ≠ 0 := ENNReal.coe_ne_zero.mp hc0
  have hmeasure :=
    skewAdjointFormElementaryPadicCoordinateMeasure_eq_smul
      q.1 L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero
  have happly := congrArg (fun μ : Measure _ ↦ μ C) hmeasure
  change
    skewAdjointFormElementaryPadicCoordinateMeasure q.1
        L.rationalFormMatrix
        (L.form_symm.map (algebraMap ℤ ℚ))
        L.rationalFormMatrix_det_ne_zero C =
      (cNN⁻¹ •
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1) C
      at happly
  rw [Measure.smul_apply] at happly
  have hscale :
      skewAdjointFormElementaryPadicCoordinateMeasure q.1
          L.rationalFormMatrix
          (L.form_symm.map (algebraMap ℤ ℚ))
          L.rationalFormMatrix_det_ne_zero C =
        c⁻¹ *
          skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1 C := by
    rw [happly]
    rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv hcNN0]
  change
    skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1 C =
      c *
        skewAdjointFormElementaryPadicCoordinateMeasure q.1
          L.rationalFormMatrix
          (L.form_symm.map (algebraMap ℤ ℚ))
          L.rationalFormMatrix_det_ne_zero C
  calc
    skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1 C =
        1 * skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1 C := by
      rw [one_mul]
    _ = (c * c⁻¹) *
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1 C := by
      rw [ENNReal.mul_inv_cancel hc0 hctop]
    _ = c * (c⁻¹ *
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1 C) := by
      rw [mul_assoc]
    _ = c *
        skewAdjointFormElementaryPadicCoordinateMeasure q.1
          L.rationalFormMatrix
          (L.form_symm.map (algebraMap ℤ ℚ))
          L.rationalFormMatrix_det_ne_zero C := by
      rw [← hscale]

/-- At an odd prime, the intrinsic coordinate normalization is the norm of
two to the tangent rank, the literal rational comparison norm, the attained
residue count, and the inverse mass of one prescribed-level residue fiber. -/
theorem
    localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_eq_twoNorm_mul_comparisonNorm_mul_residueImage_ncard_mul_inv_primePow
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq2 : q.1 ≠ 2) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
        q.1 =
      (‖(2 : ℚ_[q.1])‖₊ ^
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) : ℝ≥0∞) *
        (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q *
          ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
              q.1).ncard *
            ((q.1 : ℝ≥0∞) ^
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
                  q.1 *
                Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹)) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold
    localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
  rw [
    L.skewAdjointPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_comparisonNorm_mul_formCoordinateMeasure
      q,
    L.skewAdjointFormElementaryPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_residueImage_ncard_mul
      q.1 hq2]

/-- At an odd prime, the pointwise differential gauge-defect target is
equivalent to the exact residual residue-cardinality and prime-power identity.
The rational basis-comparison norm has been cancelled using its proved
nonzeroness and finiteness. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_densityResidueCardinality
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq2 : q.1 ≠ 2) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q ↔
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
                q.1) : ℝ≥0∞) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_intrinsicCoordinate_mul_ordinaryReductionRangeCard_eq_inv_primePow_mul_comparison_mul_quotientCount
      q,
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_eq_twoNorm_mul_comparisonNorm_mul_residueImage_ncard_mul_inv_primePow
      q hq2]
  let c :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q
  let A : ℝ≥0∞ :=
    (‖(2 : ℚ_[q.1])‖₊ ^
      Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) : ℝ≥0∞)
  let M : ℝ≥0∞ :=
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
        q.1).ncard *
      ((q.1 : ℝ≥0∞) ^
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            q.1 *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹
  let O : ℝ≥0∞ :=
    Nat.card
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
        q.1)
  let E : ℝ≥0∞ :=
    ((q.1 : ℝ≥0∞) ^
      localDensityDenominatorExponent n
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
          q.1))⁻¹
  let Q : ℝ≥0∞ :=
    associatedBilinearDualQuotientCount L q.1
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
  have hc0 : c ≠ 0 :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_zero q
  have hctop : c ≠ ⊤ :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_top q
  change (A * (c * M)) * O = (E * c) * Q ↔
    (A * M) * O = E * Q
  constructor
  · intro h
    apply (ennreal_eq_iff_mul_left_finite hc0 hctop).mpr
    calc
      c * ((A * M) * O) = (A * (c * M)) * O := by ac_rfl
      _ = (E * c) * Q := h
      _ = c * (E * Q) := by ac_rfl
  · intro h
    have hc : c * ((A * M) * O) = c * (E * Q) :=
      (ennreal_eq_iff_mul_left_finite hc0 hctop).mp h
    calc
      (A * (c * M)) * O = c * ((A * M) * O) := by ac_rfl
      _ = c * (E * Q) := hc
      _ = (E * c) * Q := by ac_rfl

end PositiveDefiniteIntegralLattice
