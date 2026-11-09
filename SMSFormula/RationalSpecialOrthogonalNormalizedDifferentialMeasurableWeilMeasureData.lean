import SMSFormula.RationalSpecialOrthogonalLatticeGeneralDifferentialMeasureComparison

/-!
# Normalized lattice differential measurable-Weil data

The retained lattice differential measurable-Weil datum has ambient measure
equal to the carrier-independent invariant-differential measure multiplied by
the finite stabilizer volume.  This module simultaneously rescales its
ambient and quotient measures by the reciprocal volume.

The resulting ambient measure is exactly the probability-normalized general
measure.  This is useful as an exact comparison datum, but it is not the raw
rational invariant-differential normalization.  The quotient measure and
`ENNReal` Tamagawa accessor retain their exact scaling formulas.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The retained sound differential datum, simultaneously rescaled by the
reciprocal of its literal finite stabilizer volume. -/
def rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData
      L.rationalQuadraticSpaceMatrix :=
  (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
    inst hP).smul
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P)⁻¹

/-- The normalized datum's ambient measure is literally the canonical general
invariant-differential full-adelic measure. -/
@[simp]
theorem rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData_adelicMeasure
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    (L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
        inst hP).adelicMeasure =
      L.rationalQuadraticSpaceMatrix.fullAdelicInvariantDifferentialGroupMeasure := by
  let a := L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
  change a⁻¹ • L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P = _
  rw [L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_eq_stabilizerVolume_smul_general
    hP]
  rw [smul_smul, ENNReal.inv_mul_cancel
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero P)
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_top hP),
    one_smul]

/-- The normalized quotient measure retains the exact simultaneous reciprocal-
volume scaling. -/
@[simp]
theorem rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData_quotientMeasure
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    (L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
        inst hP).quotientMeasure =
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P)⁻¹ •
        (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
          inst hP).quotientMeasure :=
  rfl

/-- The normalized `ENNReal` Tamagawa accessor retains the exact reciprocal-
volume scaling. -/
@[simp]
theorem rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    (L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumberENNReal =
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P)⁻¹ *
        (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
          inst hP).tamagawaNumberENNReal := by
  exact
    RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData.tamagawaNumberENNReal_smul
      _ _

end PositiveDefiniteIntegralLattice
