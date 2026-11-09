import SMSFormula.SpecialOrthogonalFullAdelicProperDomainDifferentialVolume
import SMSFormula.SpecialOrthogonalAdelicDifferentialMeasurableWeilTotalMass

/-!
# Differential measurable-Weil quotient volume

The evaluation of the lifted proper-domain differential volume is attached to
the concrete differential quotient measure and to the sound measurable-Weil
datum on the general rational quadratic-space carrier.

The resulting quotient volume is expressed through the real differential
total mass, the named finite differential stabilizer volume, and the real
cast of proper class genus mass.  The real-valued accessor is obtained by
applying `ENNReal.toReal` to the complete product; no finiteness-dependent
distribution of `toReal` over its factors is used.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The concrete differential quotient total mass is the exact internal
real-times-finite-times-proper-mass product. -/
theorem
    concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_univ_eq_real_mul_finiteVolume_mul_properClassGenusMass
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P
        Set.univ =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
          ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ))) := by
  rw [
    L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_univ P,
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_properTransversal_eq_real_mul_finiteVolume_mul_properClassGenusMass
      inst hP
  ]

/-- The `ENNReal` mass of the internally normalized sound measurable-Weil
datum is the exact internal real-times-finite-times-proper-mass product. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_real_mul_finiteVolume_mul_properClassGenusMass
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumberENNReal =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
          ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ))) := by
  rw [
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_concrete
      inst hP,
    L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_univ_eq_real_mul_finiteVolume_mul_properClassGenusMass
      inst hP
  ]

/-- Real-valued accessor form of the exact differential measurable-Weil
quotient-volume identity.  `ENNReal.toReal` remains outside the complete
product, so this theorem requires no implicit finiteness argument. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumber_eq_real_mul_finiteVolume_mul_properClassGenusMass
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumber =
      (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
          ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ)))).toReal := by
  change
    ((L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumberENNReal).toReal =
      (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
          ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ)))).toReal
  rw [
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_real_mul_finiteVolume_mul_properClassGenusMass
      inst hP
  ]

end PositiveDefiniteIntegralLattice
