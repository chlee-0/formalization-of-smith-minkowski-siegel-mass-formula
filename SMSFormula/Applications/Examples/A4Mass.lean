import SMSFormula.Applications.Examples.A4Product
import SMSFormula.IntegralQuadraticFormGenusMass
import SMSFormula.RationalSpecialOrthogonalMassFormula

/-! Numerical A4 mass from the original local densities and independent intrinsic genus sum. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice

theorem a4_latticeOfPolarForm_ordinaryGenusMass : a4.latticeOfPolarForm.ordinaryGenusMass = (1/240:ℚ) := by
  have hpos : 0 < (Real.pi^4/240:ℝ) := by positivity
  have h := a4.latticeOfPolarForm.ordinaryGenusMass_eq_massFormulaProductSide
    (by decide) hpos a4_inverseProduct_limit
  have hprod : massFormulaProductSide a4.latticeOfPolarForm (Real.pi^4/240) = (1/240:ℝ) := by
    rw [massFormulaProductSide, archimedeanMassFactor_four]
    field_simp [Real.pi_ne_zero]
  rw [hprod] at h
  apply Rat.cast_injective (α := ℝ)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
  exact h

theorem a4_intrinsic_ordinaryGenusMass : a4.ordinaryGenusMass = (1/240:ℚ) := by
  rw [PositiveDefiniteIntegralQuadraticForm.ordinaryGenusMass_eq_latticeOfPolarForm, a4_latticeOfPolarForm_ordinaryGenusMass]

end MassFormulaReleaseExamples
