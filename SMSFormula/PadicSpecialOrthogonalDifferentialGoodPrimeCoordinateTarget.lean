import SMSFormula.PadicSpecialOrthogonalDifferentialGoodPrimeAlphaCancellation

/-!
# The good-prime coordinate target

Outside the finite Schulze--Pillot bad-prime set, the dyadic factor and the
Gram-determinant factor in the selected-depth alpha normalization are both
one.  This module performs that simplification, including the exact
`ENNReal.ofReal` conversion of the positive rational prime-power inverse.

Consequently, the alpha-normalization equivalence reduces to one
condition: the density-kernel coordinate mass must be the selected
prime-power ball mass.  That condition is not proved here.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped ENNReal Matrix Matrix.Norms.Operator NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Outside the Schulze--Pillot bad-prime set, the Gram-determinant norm
factor in the selected local-density normalization is one. -/
theorem
    gramDetPadicNormFactor_eq_one_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n)
    (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    gramDetPadicNormFactor L q.1 = 1 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold gramDetPadicNormFactor
  rw [polarDeterminant_padic_norm_eq_padicValInt,
    padicValInt_polarDeterminant_eq_zero_of_not_mem_massBadPrimeSet L hq]
  norm_num

/-- At a good prime, the selected-depth denominator-and-Gram factor becomes
the `ENNReal` mass of one uniform coordinate ball at the selected denominator
exponent. -/
theorem
    ENNReal_ofReal_coordinateNormalization_eq_inv_primePow_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n)
    (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    ENNReal.ofReal
        (((twoPadicNormInvPow q.1 n *
            ((q.1 : ℚ) ^
              localDensityDenominatorExponent n
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                  q.1))⁻¹ : ℚ) : ℝ) *
          gramDetPadicNormFactor L q.1) =
      ((q.1 : ℝ≥0∞) ^
        localDensityDenominatorExponent n
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            q.1))⁻¹ := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let e :=
    localDensityDenominatorExponent n
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
  have hq_two : q.1 ≠ 2 :=
    not_mem_massBadPrimeSet_ne_two L hq
  have hpowq : 0 < (q.1 : ℚ) ^ e := by
    exact pow_pos (by exact_mod_cast q.2.pos) _
  have hpowr : 0 < (((q.1 : ℚ) ^ e : ℚ) : ℝ) := by
    exact_mod_cast hpowq
  rw [twoPadicNormInvPow_eq_one_of_ne_two hq_two,
    L.gramDetPadicNormFactor_eq_one_of_not_mem_massBadPrimeSet
      q hq]
  simp only [one_mul, mul_one]
  change
    ENNReal.ofReal (((((q.1 : ℚ) ^ e)⁻¹ : ℚ) : ℝ)) =
      ((q.1 : ℝ≥0∞) ^ e)⁻¹
  rw [show (((((q.1 : ℚ) ^ e)⁻¹ : ℚ) : ℝ)) =
      (((q.1 : ℚ) ^ e : ℚ) : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos hpowr]
  simp

/-- At a good prime, the corrected special-stabilizer volume has the expected
Schulze--Pillot normalization exactly when the intrinsic coordinate mass of
the density-adapted kernel is the selected prime-power ball mass. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_ENNReal_ofReal_normalizedLocalDensity_iff_coordinateMeasure_eq_inv_primePow_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 =
          ENNReal.ofReal (normalizedLocalDensity L q.1) ↔
      skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
            q.1) =
        ((q.1 : ℝ≥0∞) ^
          localDensityDenominatorExponent n
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              q.1))⁻¹ := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  have hq_two : q.1 ≠ 2 :=
    not_mem_massBadPrimeSet_ne_two L hq
  rw [
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_ENNReal_ofReal_normalizedLocalDensity_iff_coordinateNormalization_of_not_mem_massBadPrimeSet
      q hq,
    Matrix.nnnorm_two_padic_eq_one_of_ne_two q.1 hq_two,
    ENNReal.coe_one, one_pow, one_mul,
    L.ENNReal_ofReal_coordinateNormalization_eq_inv_primePow_of_not_mem_massBadPrimeSet
      q hq]

end PositiveDefiniteIntegralLattice
