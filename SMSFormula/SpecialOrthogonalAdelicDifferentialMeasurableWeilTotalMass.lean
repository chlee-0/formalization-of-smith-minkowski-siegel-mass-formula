import SMSFormula.SpecialOrthogonalAdelicMeasurableWeilMeasureData

/-!
# Total mass of the differential measurable-Weil datum

Transport through the concrete/general quotient measurable equivalence
preserves total mass.  Consequently the quotient mass of the general-carrier
differential measurable-Weil datum is exactly the concrete quotient mass, and
hence exactly the ambient differential mass of the lifted proper fundamental
domain.

The proper-domain mass is not evaluated in this module.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Transporting a concrete quotient measure through the rational-carrier
measurable equivalence preserves its total mass. -/
theorem rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure_univ
    (L : PositiveDefiniteIntegralLattice n)
    (μX : Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient) :
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μX Set.univ =
      μX Set.univ := by
  rw [rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure]
  rw [Measure.map_apply
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv.symm.measurable
    MeasurableSet.univ]
  simp

/-- The differential measurable-Weil datum has exactly the concrete
differential quotient total mass. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_concrete
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumberENNReal =
      L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P
        Set.univ := by
  change
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure
        (L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P)
        Set.univ =
      L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P
        Set.univ
  exact
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure_univ
      (L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P)

/-- The `ENNReal` quotient mass of the differential measurable-Weil datum is
the ambient differential mass of the lifted proper fundamental domain. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_properDomain
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumberENNReal =
      L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        L.concreteFullAdelicProperTransversal := by
  calc
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumberENNReal =
        L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P
          Set.univ :=
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_concrete
        inst hP
    _ =
        L.fullAdelicSpecialOrthogonalDifferentialMeasure P
          L.concreteFullAdelicProperTransversal :=
      L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_univ P

/-- Real-valued form of the exact differential datum/proper-domain total-mass
identity. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumber_eq_properDomain
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumber =
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        L.concreteFullAdelicProperTransversal).toReal := by
  change
    ((L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumberENNReal).toReal =
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        L.concreteFullAdelicProperTransversal).toReal
  rw [
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_properDomain
      inst hP
  ]

end PositiveDefiniteIntegralLattice
