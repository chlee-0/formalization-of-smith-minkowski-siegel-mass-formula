import SMSFormula.RationalSpecialOrthogonalCorrectedBadPrimeProduct
import SMSFormula.RationalSpecialOrthogonalMassProductSideNormalizationReduction

/-!
# Schulze--Pillot ordinary mass formula

The corrected bad-prime product supplies the global differential unit
normalization required by the normalized ordinary-mass reduction.  This
module assembles the final theorem, first in `ENNReal` and then in `Real`.

The named local-product limit appears together with its positivity.
-/

noncomputable section

open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The ordinary mass formula after applying the completed global unit
normalization, stated first as an equality of `ENNReal.ofReal` values. -/
theorem ordinaryGenusMass_eq_massFormulaProductSide_ENNReal
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) =
      ENNReal.ofReal (massFormulaProductSide L P) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  exact
    (L.ordinaryGenusMassENNReal_eq_ofReal_massFormulaProductSide_iff_globalDifferentialUnitNormalization
      hn inferInstance hP hconv).2 L.globalDifferentialUnitNormalization

/-- The positive-definite Schulze--Pillot ordinary genus mass
formula in its literal real product-side normalization. -/
theorem ordinaryGenusMass_eq_massFormulaProductSide
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massFormulaProductSide L P := by
  apply
    (ENNReal.ofReal_eq_ofReal_iff
      (by exact_mod_cast (le_of_lt L.ordinaryGenusMass_pos))
      (L.massFormulaProductSide_pos hP).le).1
  exact
    L.ordinaryGenusMass_eq_massFormulaProductSide_ENNReal
      hn hP hconv

end PositiveDefiniteIntegralLattice

end
