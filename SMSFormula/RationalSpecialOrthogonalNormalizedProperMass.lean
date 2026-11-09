import SMSFormula.RationalSpecialOrthogonalNormalizedDifferentialMeasurableWeilMeasureData
import SMSFormula.SpecialOrthogonalAdelicDifferentialProperMassRearrangement

/-!
# Symbolic proper mass for the normalized differential datum

The proper-mass rearrangement uses the lattice measurable-Weil datum together
with its named finite inverse volume.  That inverse volume is exactly the
reciprocal scalar used to define the normalized sound datum.  This module
combines those two facts and rewrites proper class genus mass directly
through the normalized Tamagawa accessor.

The normalized accessor remains symbolic: this module does not use the
theorem that its value is two.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Proper class genus mass in terms of the normalized sound datum's still-
symbolic Tamagawa accessor. -/
theorem properClassGenusMassENNReal_eq_inv_realDifferentialMass_mul_normalizedTamagawaNumber
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ)) =
      (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
        (L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
          inst hP).tamagawaNumberENNReal := by
  rw [L.properClassGenusMassENNReal_eq_inv_realDifferentialMass_mul_finiteInverseVolume_mul_differentialTamagawaNumber
    inst hP]
  rw [L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal
    inst hP]
  rw [L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_eq_inv_volume]

end PositiveDefiniteIntegralLattice
