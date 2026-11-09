import SMSFormula.AdelicSpinDiagonalBlockLocalData
import SMSFormula.AdelicGaussianRankFourSpinFromRankThree
import SMSFormula.AdelicGaussianSpecialOrthogonalTamagawaFromRankFour

/-!
# `τ(SO) = 2` for every lattice of rank `≥ 3`, from intrinsic `τ(Spin) = 1`

The final results of the Spin route:

* `DiagonalSpinProductFormula` is proved (`PositiveDefiniteIntegralLattice.diagonalSpinProductFormula`), so the
  diagonal block bootstrap gives `τ(Spin) = 1` in rank three (`rankThreeSpinTamagawaOne`);
* the rank-four common-complement step gives `τ(Spin) = 1` in rank four (`rankFourSpinTamagawaOne`);
* the relative Spin/SO comparison and the rank induction give `τ(SO) = 2` for the raw lattice
  differential datum in every rank `≥ 3`
  (`rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_two_of_three_le`).

This module imports no mass formula and no Tamagawa-number statement.  The lattice form of the
last theorem is in `RationalSpecialOrthogonalRawTamagawaNumber`.  The results use only the
standard axioms.
-/

noncomputable section

open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

/-- `τ(Spin) = 1` for every ternary lattice. -/
theorem rankThreeSpinTamagawaOne : RankThreeSpinTamagawaOne :=
  rankThreeSpinTamagawaOne_of_diagonalProductFormula diagonalSpinProductFormula

/-- `τ(Spin) = 1` for every rank-four lattice. -/
theorem rankFourSpinTamagawaOne : RankFourSpinTamagawaOne :=
  rankFourSpinTamagawaOne_of_rankThree rankThreeSpinTamagawaOne

/-- `τ(SO) = 2` in every rank `≥ 3` for the raw lattice differential datum, without a
Tamagawa-number hypothesis. -/
theorem rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_two_of_three_le
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P) :
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData inst hP).tamagawaNumberENNReal =
      2 :=
  IntegralFiniteAdelePhase.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_two_of_lowRankSpin
    rankThreeSpinTamagawaOne rankFourSpinTamagawaOne L hn inst hP hconv

end PositiveDefiniteIntegralLattice
