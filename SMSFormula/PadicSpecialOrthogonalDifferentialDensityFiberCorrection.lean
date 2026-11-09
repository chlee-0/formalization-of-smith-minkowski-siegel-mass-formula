import SMSFormula.PadicSpecialOrthogonalDifferentialStabilizerVolumeIntrinsicCoordinateMass

/-!
# The multiplicative selected-density fiber correction

The selected ordinary finite reduction range has cardinality equal to the
associated-bilinear quotient count plus a literal natural-number fiber excess.
This module packages that additive excess as an exact multiplicative `ENNReal`
correction relative to the positive quotient count.

The correction is nonzero and finite.  It rewrites only the terminal finite
factor in the intrinsic balanced corrected stabilizer-volume identity, and it
is one outside the Schulze--Pillot bad-prime set.  No value at a bad prime,
coordinate normalization, finite prime product, or Tamagawa number is
evaluated here.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The exact multiplicative correction from the associated-bilinear quotient
count to the selected ordinary reduction-range cardinality. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityFiberCorrection
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℝ≥0∞ :=
  ((associatedBilinearDualQuotientCount L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) +
        L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess p :
      ℕ) : ℝ≥0∞) *
    (associatedBilinearDualQuotientCount L p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) :
      ℝ≥0∞)⁻¹

/-- The selected associated-bilinear quotient count is positive. -/
theorem
    associatedBilinearDualQuotientCount_pos_at_densityCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    0 <
      associatedBilinearDualQuotientCount L p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
  unfold associatedBilinearDualQuotientCount
  exact
    coordinateLocalDualQuotientCount_pos_of_admissible L p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p))
      (associatedBilinearDualPadicDenominatorIntegralPreimage_admissible
        (n := n) L p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
          p).associated_bilinear_quadratic_depth)

/-- The `ENNReal` cast of the selected associated-bilinear quotient count is
nonzero. -/
theorem
    ENNReal_coe_associatedBilinearDualQuotientCount_ne_zero_at_densityCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (associatedBilinearDualQuotientCount L p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) :
      ℝ≥0∞) ≠ 0 := by
  exact_mod_cast
    (L.associatedBilinearDualQuotientCount_pos_at_densityCongruenceDepth
      p).ne'

/-- The `ENNReal` cast of the selected associated-bilinear quotient count is
finite. -/
theorem
    ENNReal_coe_associatedBilinearDualQuotientCount_ne_top_at_densityCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (associatedBilinearDualQuotientCount L p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) :
      ℝ≥0∞) ≠ ⊤ :=
  ENNReal.natCast_ne_top _

/-- The quotient count plus the selected fiber excess is exactly the
multiplicative fiber correction times the quotient count. -/
theorem
    ENNReal_coe_associatedBilinearDualQuotientCount_add_densityFiberExcess_eq_densityFiberCorrection_mul_quotientCount
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ((associatedBilinearDualQuotientCount L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) +
        L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess p :
      ℕ) : ℝ≥0∞) =
      L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection p *
        (associatedBilinearDualQuotientCount L p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p) :
          ℝ≥0∞) := by
  let Q :=
    associatedBilinearDualQuotientCount L p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  let E := L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess p
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
    exact
      L.ENNReal_coe_associatedBilinearDualQuotientCount_ne_zero_at_densityCongruenceDepth
        p
  have hQtop : (Q : ℝ≥0∞) ≠ ⊤ := by
    exact
      L.ENNReal_coe_associatedBilinearDualQuotientCount_ne_top_at_densityCongruenceDepth
        p
  change
    ((Q + E : ℕ) : ℝ≥0∞) =
      (((Q + E : ℕ) : ℝ≥0∞) * (Q : ℝ≥0∞)⁻¹) * (Q : ℝ≥0∞)
  rw [mul_assoc, ENNReal.inv_mul_cancel hQ0 hQtop, mul_one]

/-- The selected multiplicative fiber correction is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityFiberCorrection_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection p ≠ 0 := by
  let Q :=
    associatedBilinearDualQuotientCount L p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  let E := L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess p
  have hQpos : 0 < Q := by
    exact
      L.associatedBilinearDualQuotientCount_pos_at_densityCongruenceDepth
        p
  have hQtop : (Q : ℝ≥0∞) ≠ ⊤ := by
    exact
      L.ENNReal_coe_associatedBilinearDualQuotientCount_ne_top_at_densityCongruenceDepth
        p
  have hsum0 : ((Q + E : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : Q + E ≠ 0)
  unfold localPadicSpecialOrthogonalDifferentialDensityFiberCorrection
  exact mul_ne_zero hsum0 (ENNReal.inv_ne_zero.mpr hQtop)

/-- The selected multiplicative fiber correction is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityFiberCorrection_ne_top
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection p ≠ ⊤ := by
  let Q :=
    associatedBilinearDualQuotientCount L p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
    exact
      L.ENNReal_coe_associatedBilinearDualQuotientCount_ne_zero_at_densityCongruenceDepth
        p
  unfold localPadicSpecialOrthogonalDifferentialDensityFiberCorrection
  exact
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr hQ0)

/-- The intrinsic balanced corrected stabilizer volume with its terminal
ordinary-reduction factor split into the multiplicative selected-fiber
correction and the associated-bilinear quotient count. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_zeroDensity_mul_coordinateMeasure_mul_densityFiberCorrection_mul_quotientCount
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
        (2 : ℝ≥0∞) =
      (‖(2 : ℚ_[p])‖₊ ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra
            L.rationalFormMatrix) : ℝ≥0∞) *
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
            p) *
        L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection p *
        (associatedBilinearDualQuotientCount L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) :
          ℝ≥0∞) := by
  let Q :=
    associatedBilinearDualQuotientCount L p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  let E := L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess p
  have hsplit :
      (Q : ℝ≥0∞) + (E : ℝ≥0∞) =
        L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection p *
          (Q : ℝ≥0∞) := by
    rw [← Nat.cast_add]
    exact
      L.ENNReal_coe_associatedBilinearDualQuotientCount_add_densityFiberExcess_eq_densityFiberCorrection_mul_quotientCount
        p
  rw [
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_zeroDensity_mul_coordinateMeasure_mul_quotientCount_add_fiberExcess
      p,
    hsplit,
    ← mul_assoc]

/-- Outside the Schulze--Pillot bad-prime set, the selected multiplicative
fiber correction is one. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityFiberCorrection_eq_one_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection q.1 =
      1 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let Q :=
    associatedBilinearDualQuotientCount L q.1
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
    exact
      L.ENNReal_coe_associatedBilinearDualQuotientCount_ne_zero_at_densityCongruenceDepth
        q.1
  have hQtop : (Q : ℝ≥0∞) ≠ ⊤ := by
    exact
      L.ENNReal_coe_associatedBilinearDualQuotientCount_ne_top_at_densityCongruenceDepth
        q.1
  unfold localPadicSpecialOrthogonalDifferentialDensityFiberCorrection
  rw [
    L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess_eq_zero_of_not_mem_massBadPrimeSet
      q hq,
    add_zero,
    ENNReal.mul_inv_cancel hQ0 hQtop]

end PositiveDefiniteIntegralLattice
