import SMSFormula.SpecialOrthogonalRationalAdelicDifferentialMeasurableWeilCarrierTransport
import SMSFormula.RationalSpecialOrthogonalTamagawa

/-!
# Sound measurable Weil measure data

This module packages ambient and quotient measures satisfying the standard
measurable-integrand Weil formula.  The stronger arbitrary-integrand
Weil datum maps into this structure, while no converse is asserted.

The internally constructed differential ambient and quotient measures define
such a datum on the rational quadratic-space presentation associated with an
integral lattice.  No quotient mass is evaluated here.
-/

noncomputable section

variable {n : ℕ}

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

/-- Ambient and quotient measures satisfying the sound measurable-integrand
left Weil formula. -/
structure SpecialOrthogonalAdelicMeasurableWeilMeasureData
    (V : RationalQuadraticSpaceMatrix n) where
  adelicMeasure : Measure V.FullAdelicSpecialOrthogonalGroup
  quotientMeasure : Measure V.FullAdelicSpecialOrthogonalLeftQuotient
  isMeasurableWeilQuotientMeasure :
    IsLeftMeasurableWeilQuotientMeasure
      V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      adelicMeasure quotientMeasure

namespace SpecialOrthogonalAdelicMeasurableWeilMeasureData

/-- Every arbitrary-integrand Weil datum gives sound
measurable-integrand Weil data. -/
def ofLegacy
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicWeilMeasureData V) :
    SpecialOrthogonalAdelicMeasurableWeilMeasureData V where
  adelicMeasure := D.adelicMeasure
  quotientMeasure := D.quotientMeasure
  isMeasurableWeilQuotientMeasure :=
    D.isWeilQuotientMeasure.toIsLeftMeasurableWeilQuotientMeasure

/-- Common scalar rescaling preserves the measurable left Weil formula. -/
theorem isMeasurableWeilQuotientMeasure_smul
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V)
    (c : ℝ≥0∞) :
    IsLeftMeasurableWeilQuotientMeasure
      V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      (c • D.adelicMeasure) (c • D.quotientMeasure) where
  lintegral_leftPeriodize_eq f hf := by
    rw [lintegral_smul_measure, lintegral_smul_measure,
      D.isMeasurableWeilQuotientMeasure.lintegral_leftPeriodize_eq f hf]

/-- Simultaneously rescale the ambient and quotient measures in sound Weil
data. -/
def smul
    {V : RationalQuadraticSpaceMatrix n}
    (c : ℝ≥0∞)
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V) :
    SpecialOrthogonalAdelicMeasurableWeilMeasureData V where
  adelicMeasure := c • D.adelicMeasure
  quotientMeasure := c • D.quotientMeasure
  isMeasurableWeilQuotientMeasure :=
    D.isMeasurableWeilQuotientMeasure_smul c

/-- The `ENNReal` total mass of the measurable-Weil-normalized quotient. -/
def tamagawaNumberENNReal
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V) : ℝ≥0∞ :=
  D.quotientMeasure Set.univ

/-- The real-valued total mass of the measurable-Weil-normalized quotient. -/
def tamagawaNumber
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V) : ℝ :=
  D.tamagawaNumberENNReal.toReal

@[simp]
theorem tamagawaNumberENNReal_eq
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V) :
    D.tamagawaNumberENNReal = D.quotientMeasure Set.univ :=
  rfl

@[simp]
theorem tamagawaNumberENNReal_smul
    {V : RationalQuadraticSpaceMatrix n}
    (c : ℝ≥0∞)
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V) :
    (D.smul c).tamagawaNumberENNReal = c * D.tamagawaNumberENNReal := by
  change (c • D.quotientMeasure) Set.univ =
    c * D.quotientMeasure Set.univ
  rw [Measure.smul_apply, smul_eq_mul]

@[simp]
theorem tamagawaNumber_eq
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V) :
    D.tamagawaNumber = (D.quotientMeasure Set.univ).toReal :=
  rfl

@[simp]
theorem tamagawaNumberENNReal_ofLegacy
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicWeilMeasureData V) :
    (ofLegacy D).tamagawaNumberENNReal = D.tamagawaNumberENNReal :=
  rfl

end SpecialOrthogonalAdelicMeasurableWeilMeasureData

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

/-- The internally constructed differential ambient and quotient measures,
packaged as sound measurable Weil data on the associated rational
quadratic-space presentation. -/
def rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData
      L.rationalQuadraticSpaceMatrix where
  adelicMeasure :=
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P
  quotientMeasure :=
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure
      (L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P)
  isMeasurableWeilQuotientMeasure :=
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialQuotientMeasure_isLeftMeasurableWeilQuotientMeasure
      inst hP

end PositiveDefiniteIntegralLattice
