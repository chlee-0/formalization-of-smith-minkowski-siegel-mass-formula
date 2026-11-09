import SMSFormula.RationalSpecialOrthogonalNormalizedProperMass
import SMSFormula.ProperMass

/-!
# Symbolic ordinary mass for the normalized differential datum

The determinant-sign splitting identifies proper class genus mass with twice
ordinary genus mass.  This module transports that identity to
`ENNReal.ofReal` and combines it with the normalized symbolic proper-mass
formula.  The result contains the normalized Tamagawa accessor divided by two.

This module does not use the theorem that the normalized Tamagawa number is
two.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The internal proper-to-ordinary mass identity after applying
`ENNReal.ofReal`. -/
theorem properClassGenusMassENNReal_eq_two_mul_ordinaryGenusMassENNReal
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ)) =
      2 * ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) := by
  rw [L.properClassGenusMass_eq_two_ordinaryGenusMass]
  rw [ENNReal.ofReal_mul (by positivity)]
  norm_num

/-- Ordinary genus mass in terms of the normalized sound datum's still-
symbolic Tamagawa accessor divided by two. -/
theorem ordinaryGenusMassENNReal_eq_inv_realDifferentialMass_mul_inv_two_mul_normalizedTamagawaNumber
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) =
      (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
        ((2 : ℝ≥0∞)⁻¹ *
          (L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
            inst hP).tamagawaNumberENNReal) := by
  have hproper :=
    L.properClassGenusMassENNReal_eq_inv_realDifferentialMass_mul_normalizedTamagawaNumber
      inst hP
  have hsplit := L.properClassGenusMassENNReal_eq_two_mul_ordinaryGenusMassENNReal
  have htwo :
      (2 : ℝ≥0∞) * ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) =
        (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
          (L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
            inst hP).tamagawaNumberENNReal :=
    hsplit.symm.trans hproper
  calc
    ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) =
        ((2 : ℝ≥0∞)⁻¹ * 2) *
          ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) := by
            rw [ENNReal.inv_mul_cancel] <;> norm_num
    _ = (2 : ℝ≥0∞)⁻¹ *
          (2 * ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ))) := by
            rw [mul_assoc]
    _ = (2 : ℝ≥0∞)⁻¹ *
          ((L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
            (L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
              inst hP).tamagawaNumberENNReal) := by
                rw [htwo]
    _ = (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
          ((2 : ℝ≥0∞)⁻¹ *
            (L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
              inst hP).tamagawaNumberENNReal) := by
                ac_rfl

end PositiveDefiniteIntegralLattice
