import SMSFormula.PadicSpecialOrthogonalDifferentialGoodPrimeDensityCongruenceElementaryBallMeasure
import SMSFormula.PadicSpecialOrthogonalDifferentialGoodPrimeCoordinateTarget
import SMSFormula.SkewAdjointPadicElementaryCoordinateMeasureScale

/-!
# The exact rational-basis correction at Schulze--Pillot good primes

The form-adapted coordinate measure is the fixed-basis coordinate
measure scaled by the inverse p-adic norm of the single rational
fixed/form-adapted comparison determinant.  Since the form-adapted
density-kernel mass is known exactly, this gives the fixed-basis kernel
mass with the comparison norm in the numerator.

Combining that coordinate identity with the intrinsic corrected stabilizer
volume and the selected-depth alpha identity proves the exact good-prime
rational-basis correction.  The rational scalar remains symbolic.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped ENNReal Matrix NNReal

namespace Matrix

variable {n : ℕ}

/-- The `ENNReal` p-adic norm of the scalar-extended rational
fixed/form-adapted comparison determinant is nonzero. -/
theorem
    ENNReal_coe_nnnorm_skewAdjointFixedFormElementaryDetScalar_ne_zero
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (‖algebraMap ℚ ℚ_[p]
        (skewAdjointFixedFormElementaryDetScalar F hF hdet)‖₊ :
      ℝ≥0∞) ≠ 0 := by
  rw [ENNReal.coe_ne_zero]
  intro hnorm
  have hpadic :
      algebraMap ℚ ℚ_[p]
          (skewAdjointFixedFormElementaryDetScalar F hF hdet) =
        0 :=
    nnnorm_eq_zero.mp hnorm
  exact
    (algebraMap ℚ ℚ_[p]).injective.ne
      (skewAdjointFixedFormElementaryDetScalar_ne_zero F hF hdet)
      hpadic

/-- The `ENNReal` p-adic norm of the scalar-extended rational
fixed/form-adapted comparison determinant is finite. -/
theorem
    ENNReal_coe_nnnorm_skewAdjointFixedFormElementaryDetScalar_ne_top
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (‖algebraMap ℚ ℚ_[p]
        (skewAdjointFixedFormElementaryDetScalar F hF hdet)‖₊ :
      ℝ≥0∞) ≠ ⊤ :=
  ENNReal.coe_ne_top

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    goodPrimeRationalBasisCorrectionMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance
    goodPrimeRationalBasisCorrectionBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- At a Schulze--Pillot good prime, the fixed-basis coordinate mass
of the density kernel is the elementary inverse prime power multiplied by the
p-adic norm of the rational basis-comparison determinant. -/
theorem
    skewAdjointPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_comparisonNorm_mul_inv_primePow_denominatorExponent_of_not_mem_badPrimeSet
    (L : PositiveDefiniteIntegralLattice n)
    (q : {p : ℕ // Nat.Prime p})
    [Fact (Nat.Prime q.1)]
    (hq : q ∉ massBadPrimeSet L) :
    skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          q.1) =
      (‖algebraMap ℚ ℚ_[q.1]
          (skewAdjointFixedFormElementaryDetScalar
            L.rationalFormMatrix
            (L.form_symm.map (algebraMap ℤ ℚ))
            L.rationalFormMatrix_det_ne_zero)‖₊ : ℝ≥0∞) *
        ((q.1 : ℝ≥0∞) ^
          localDensityDenominatorExponent n
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              q.1))⁻¹ := by
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
  let B : ℝ≥0∞ :=
    ((q.1 : ℝ≥0∞) ^
      localDensityDenominatorExponent n
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
          q.1))⁻¹
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
  have hcNN0 : cNN ≠ 0 :=
    ENNReal.coe_ne_zero.mp hc0
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
  have hform :
      skewAdjointFormElementaryPadicCoordinateMeasure q.1
          L.rationalFormMatrix
          (L.form_symm.map (algebraMap ℤ ℚ))
          L.rationalFormMatrix_det_ne_zero C = B := by
    exact
      L.skewAdjointFormElementaryPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_inv_primePow_denominatorExponent_of_not_mem_badPrimeSet
        q hq
  have hscale :
      B = c⁻¹ *
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1 C := by
    rw [← hform, happly]
    rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv hcNN0]
  change
    skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1 C =
      c * B
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
    _ = c * B := by rw [← hscale]

/-- At every Schulze--Pillot good prime, with no restriction on the rational
basis-comparison support, the corrected stabilizer volume is
`normalizedLocalDensity` multiplied by the literal p-adic comparison-determinant
norm. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_comparisonNorm_mul_ENNReal_ofReal_normalizedLocalDensity_of_not_mem_badPrimeSet
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 =
      (‖algebraMap ℚ ℚ_[q.1]
          (skewAdjointFixedFormElementaryDetScalar
            L.rationalFormMatrix
            (L.form_symm.map (algebraMap ℤ ℚ))
            L.rationalFormMatrix_det_ne_zero)‖₊ : ℝ≥0∞) *
        ENNReal.ofReal (normalizedLocalDensity L q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let s :=
    skewAdjointFixedFormElementaryDetScalar
      L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero
  let c : ℝ≥0∞ := ‖algebraMap ℚ ℚ_[q.1] s‖₊
  let C :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
      q.1
  let B : ℝ≥0∞ :=
    ((q.1 : ℝ≥0∞) ^
      localDensityDenominatorExponent n
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
          q.1))⁻¹
  let Q :=
    associatedBilinearDualQuotientCount L q.1
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
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
  have hq2 : q.1 ≠ 2 :=
    L.not_mem_massBadPrimeSet_ne_two hq
  have htwo : ‖(2 : ℚ_[q.1])‖₊ = 1 :=
    Matrix.nnnorm_two_padic_eq_one_of_ne_two q.1 hq2
  have hcoord :
      skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1 C =
        c * B := by
    exact
      L.skewAdjointPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_comparisonNorm_mul_inv_primePow_denominatorExponent_of_not_mem_badPrimeSet
        q hq
  have hvol :
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
          (2 : ℝ≥0∞) =
        c * B * (Q : ℝ≥0∞) := by
    have h :=
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_zeroDensity_mul_coordinateMeasure_mul_quotientCount_of_not_mem_massBadPrimeSet
        q hq
    simp only [htwo] at h
    rw [hcoord] at h
    simpa [c, s, B, Q, C] using h
  have halpha :
      ENNReal.ofReal (normalizedLocalDensity L q.1) * (2 : ℝ≥0∞) =
        B * (Q : ℝ≥0∞) := by
    have h :=
      L.ENNReal_ofReal_normalizedLocalDensity_mul_two_eq_coordinateNormalization_mul_associatedBilinearDualQuotientCount_at_densityDepth
        q.1
    have hnormal :=
      L.ENNReal_ofReal_coordinateNormalization_eq_inv_primePow_of_not_mem_massBadPrimeSet
        q hq
    rw [hnormal] at h
    simpa [B, Q] using h
  have hmul :
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
          (2 : ℝ≥0∞) =
        (c * ENNReal.ofReal (normalizedLocalDensity L q.1)) *
          (2 : ℝ≥0∞) := by
    calc
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
          (2 : ℝ≥0∞) =
        c * B * (Q : ℝ≥0∞) := hvol
      _ = c * (B * (Q : ℝ≥0∞)) := by rw [mul_assoc]
      _ = c *
          (ENNReal.ofReal (normalizedLocalDensity L q.1) *
            (2 : ℝ≥0∞)) := by
        rw [← halpha]
      _ = (c * ENNReal.ofReal (normalizedLocalDensity L q.1)) *
          (2 : ℝ≥0∞) := by rw [mul_assoc]
  let two : ℝ≥0∞ := 2
  have htwo0 : two ≠ 0 := by norm_num [two]
  have htwotop : two ≠ ⊤ := by norm_num [two]
  calc
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 =
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
          1 := by rw [mul_one]
    _ =
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
          (two * two⁻¹) := by
      rw [ENNReal.mul_inv_cancel htwo0 htwotop]
    _ =
        (L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
          two) * two⁻¹ := by rw [mul_assoc]
    _ = ((c * ENNReal.ofReal (normalizedLocalDensity L q.1)) *
          two) * two⁻¹ := by
      rw [show
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
            two =
          (c * ENNReal.ofReal (normalizedLocalDensity L q.1)) * two by
        simpa [two] using hmul]
    _ = (c * ENNReal.ofReal (normalizedLocalDensity L q.1)) *
          (two * two⁻¹) := by rw [mul_assoc]
    _ = c * ENNReal.ofReal (normalizedLocalDensity L q.1) := by
      rw [ENNReal.mul_inv_cancel htwo0 htwotop, mul_one]

end PositiveDefiniteIntegralLattice
