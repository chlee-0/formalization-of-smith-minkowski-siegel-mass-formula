import SMSFormula.SpecialOrthogonalFullAdelicProperFundamentalDomain
import SMSFormula.AdelicWeilQuotient

/-!
# Differential measure on the concrete rational full-adelic quotient

The internally constructed full-adelic differential Haar measure restricts
to the lifted proper fundamental domain.  Pushing that restriction through
the concrete rational left-quotient map defines the corresponding quotient
measure.

This module records only that literal definition and its total mass.  It does
not assert a Weil periodization identity or evaluate the fundamental-domain
mass.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The concrete rational quotient measure obtained by pushing the
full-adelic differential Haar restricted to the lifted proper fundamental
domain through the canonical left-quotient map. -/
def concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient :=
  Measure.map
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap
    ((L.fullAdelicSpecialOrthogonalDifferentialMeasure P).restrict
      L.concreteFullAdelicProperTransversal)

/-- The concrete differential quotient measure is exactly the generic
fundamental-domain quotient measure for the rational diagonal
subgroup. -/
theorem concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_eq_leftQuotientFundamentalDomainMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P =
      leftQuotientFundamentalDomainMeasure
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
        (L.fullAdelicSpecialOrthogonalDifferentialMeasure P)
        L.concreteFullAdelicProperTransversal :=
  rfl

/-- The total mass of the concrete differential quotient measure is exactly
the ambient differential mass of the lifted proper fundamental domain. -/
theorem concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P Set.univ =
      L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        L.concreteFullAdelicProperTransversal := by
  rw [
    L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_eq_leftQuotientFundamentalDomainMeasure
  ]
  exact leftQuotientFundamentalDomainMeasure_univ_map_mspace rfl

end PositiveDefiniteIntegralLattice
