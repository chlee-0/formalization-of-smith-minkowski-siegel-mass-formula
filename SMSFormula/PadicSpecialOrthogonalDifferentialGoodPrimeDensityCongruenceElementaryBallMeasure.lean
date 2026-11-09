import SMSFormula.PadicSpecialOrthogonalDifferentialGoodPrimeDensityCongruenceElementaryBall
import SMSFormula.SkewAdjointPadicElementaryUniformCoordinateBallMeasure

/-!
# Elementary coordinate mass of the good-prime density kernel

The exact good-prime identification of the density-adapted inverse-Cayley
kernel with a form-adapted uniform coordinate ball can be measured
directly.  The form-adapted ball formula first gives the mass in terms of the
symbolic rational skew-adjoint rank.  A separate elementary dimension identity
then rewrites this exponent as the selected Schulze--Pillot denominator
exponent.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- At a Schulze--Pillot good prime, the normalized form-adapted coordinate
mass of the density kernel is the inverse prime power in the symbolic rational
skew-adjoint rank. -/
theorem
    skewAdjointFormElementaryPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_inv_primePow_finrank_of_not_mem_badPrimeSet
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    [Fact (Nat.Prime q.1)]
    (hq : q ∉ massBadPrimeSet L) :
    skewAdjointFormElementaryPadicCoordinateMeasure q.1
        L.rationalFormMatrix
        (L.form_symm.map (algebraMap ℤ ℚ))
        L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          q.1) =
      ((q.1 : ℝ≥0∞) ^
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1 *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra
              L.rationalFormMatrix)))⁻¹ := by
  rw [
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_eq_formElementaryUniformCoordinateBall_of_not_mem_badPrimeSet
      q hq]
  exact
    skewAdjointFormElementaryPadicCoordinateMeasure_uniformCoordinateBall
      q.1
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
      L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero

/-- The uniform-ball exponent `k` times the rational skew-adjoint rank is
literally the Schulze--Pillot local-density denominator exponent. -/
theorem
    mul_finrank_skewAdjoint_rationalFormMatrix_eq_localDensityDenominatorExponent
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ) :
    k * Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) =
      localDensityDenominatorExponent n k := by
  rw [
    finrank_skewAdjointMatricesLieSubalgebra_eq_choose_two n
      L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero]
  unfold localDensityDenominatorExponent
  rw [Nat.choose_two_right]

/-- At a Schulze--Pillot good prime, the normalized form-adapted coordinate
mass of the density kernel is exactly the inverse prime power appearing in
the selected local-density denominator. -/
theorem
    skewAdjointFormElementaryPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_inv_primePow_denominatorExponent_of_not_mem_badPrimeSet
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    [Fact (Nat.Prime q.1)]
    (hq : q ∉ massBadPrimeSet L) :
    skewAdjointFormElementaryPadicCoordinateMeasure q.1
        L.rationalFormMatrix
        (L.form_symm.map (algebraMap ℤ ℚ))
        L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          q.1) =
      ((q.1 : ℝ≥0∞) ^
        localDensityDenominatorExponent n
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            q.1))⁻¹ := by
  rw [
    L.skewAdjointFormElementaryPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_inv_primePow_finrank_of_not_mem_badPrimeSet
      q hq,
    L.mul_finrank_skewAdjoint_rationalFormMatrix_eq_localDensityDenominatorExponent]

end PositiveDefiniteIntegralLattice
