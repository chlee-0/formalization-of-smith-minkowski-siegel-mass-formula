import SMSFormula.Applications.Examples.TernaryProduct
import SMSFormula.RationalSpecialOrthogonalMassFormula

/-! Numerical ordinary full-O mass of the original determinant-22 lattice. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice

theorem ternary_ordinaryGenusMass : ternaryLattice.ordinaryGenusMass = (3 / 8 : ℚ) := by
  have hpos : 0 < (3 * Real.pi ^ 2 / 8 : ℝ) := by positivity
  have h := ternaryLattice.ordinaryGenusMass_eq_massFormulaProductSide (by decide)
    hpos ternary_inverseProduct_limit
  have hprod : massFormulaProductSide ternaryLattice (3 * Real.pi ^ 2 / 8) = (3 / 8 : ℝ) := by
    rw [massFormulaProductSide, archimedeanMassFactor_three]
    field_simp [Real.pi_ne_zero] <;> ring
  rw [hprod] at h
  apply Rat.cast_injective (α := ℝ)
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  exact h

end MassFormulaReleaseExamples
