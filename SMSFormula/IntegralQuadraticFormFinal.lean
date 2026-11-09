import SMSFormula.IntegralQuadraticFormPreTamagawa
import SMSFormula.RationalSpecialOrthogonalRawTamagawaNumber

/-!
# Numerical direct mass formula for integral quadratic forms

This module is the first integral-quadratic-form layer to invoke the lattice value
`tau(SO)=2` (`RationalSpecialOrthogonalRawTamagawaNumber`).  That value is
proved through intrinsic
`tau(Spin)=1`, so every theorem here uses standard axioms only
(`IntegralQuadraticFormFinalAxiomAudit`).  The pre-Tamagawa theorem already contains the
direct `Q_H`/`A`-dual product, so only the full differential Tamagawa accessor
is evaluated here.
-/

noncomputable section

open scoped ENNReal

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-- The full differential Tamagawa accessor of the integral quadratic form has
value two.  Direct local-product convergence is transported to the scaled
integral model solely to certify the raw differential datum. -/
theorem fullAdelicDifferentialTamagawaNumberENNReal_eq_two
    (hn : 3 ≤ n)
    (inst : Fintype
      H.latticeOfPolarForm.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : H.massLocalInverseProductTendsTo P) :
    H.fullAdelicDifferentialTamagawaNumberENNReal
        (lt_of_lt_of_le (by norm_num) hn) inst hP = 2 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  have hconvIntegralModel :
      PositiveDefiniteIntegralLattice.massLocalInverseProductTendsTo
        H.latticeOfPolarForm P :=
    (H.massLocalInverseProductTendsTo_iff_latticeOfPolarForm
      P).mp hconv
  simpa [fullAdelicDifferentialTamagawaNumberENNReal] using
    H.latticeOfPolarForm
      |>.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_two
        hn inst hP hconvIntegralModel

/-- The direct product side of the integral quadratic form is strictly positive when its named
limit is positive. -/
theorem massFormulaProductSide_pos
    {P : ℝ} (hP : 0 < P) :
    0 < H.massFormulaProductSide P := by
  rw [H.massFormulaProductSide_eq_latticeOfPolarForm]
  exact H.latticeOfPolarForm.massFormulaProductSide_pos hP

/-- The ordinary mass of the integral quadratic form is strictly positive by transparent genus
transport to the scaled integral integral model. -/
theorem transportedOrdinaryGenusMass_pos : 0 < H.transportedOrdinaryGenusMass := by
  rw [H.transportedOrdinaryGenusMass_eq_latticeOfPolarForm]
  exact H.latticeOfPolarForm.ordinaryGenusMass_pos

/-- The direct positive-definite ordinary mass formula for integral quadratic forms in
`ENNReal`.  Standard axioms only: the value `tau(SO)=2` it uses is proved
(the former axiom is deleted). -/
theorem transportedOrdinaryGenusMass_eq_massFormulaProductSide_ENNReal
    (hn : 3 ≤ n) {P : ℝ} (hP : 0 < P)
    (hconv : H.massLocalInverseProductTendsTo P) :
    ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
      ENNReal.ofReal (H.massFormulaProductSide P) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  let inst : Fintype
      H.latticeOfPolarForm.ConcreteProperRationalDoubleCosetSet :=
    inferInstance
  have hpre :=
    H.transportedOrdinaryGenusMass_eq_massFormulaProductSide_mul_tamagawa_ENNReal
      hn inst hP hconv
  rw [H.fullAdelicDifferentialTamagawaNumberENNReal_eq_two
    hn inst hP hconv] at hpre
  have htwo : (2 : ℝ≥0∞)⁻¹ * 2 = 1 := by
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
        ENNReal.ofReal (H.massFormulaProductSide P) *
          ((2 : ℝ≥0∞)⁻¹ * 2) := hpre
    _ = ENNReal.ofReal (H.massFormulaProductSide P) := by
      rw [htwo, mul_one]

/-- The direct positive-definite ordinary mass formula for integral quadratic forms over
`Real`.  The descent from `ENNReal.ofReal` uses the independently proved
positivity of both sides. -/
theorem transportedOrdinaryGenusMass_eq_massFormulaProductSide
    (hn : 3 ≤ n) {P : ℝ} (hP : 0 < P)
    (hconv : H.massLocalInverseProductTendsTo P) :
    ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) =
      H.massFormulaProductSide P := by
  apply
    (ENNReal.ofReal_eq_ofReal_iff
      (by exact_mod_cast (le_of_lt H.transportedOrdinaryGenusMass_pos))
      (H.massFormulaProductSide_pos hP).le).1
  exact
    H.transportedOrdinaryGenusMass_eq_massFormulaProductSide_ENNReal
      hn hP hconv

end PositiveDefiniteIntegralQuadraticForm

end
