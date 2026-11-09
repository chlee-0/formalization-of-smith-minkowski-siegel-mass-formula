import SMSFormula.RationalSpecialOrthogonalRawInvariantDifferentialMeasurableWeilMeasureData
import SMSFormula.RationalSpecialOrthogonalTamagawaNumberFromSpin

/-!
# Raw lattice special-orthogonal Tamagawa number

This module states `τ(SO) = 2` for the raw lattice differential datum.  The
theorem below follows from
`..._eq_two_of_three_le` (`RationalSpecialOrthogonalTamagawaNumberFromSpin`: intrinsic `τ(Spin) = 1`
and the relative Spin/SO comparison).  It uses only the standard axioms.
-/

noncomputable section

open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The raw lattice differential datum has Tamagawa number two (by
`..._eq_two_of_three_le`). -/
theorem rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_two
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
      inst hP).tamagawaNumberENNReal = 2 :=
  L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_two_of_three_le
    hn inst hP hconv

end PositiveDefiniteIntegralLattice
