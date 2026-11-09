import SMSFormula.SpecialOrthogonalAdelicDifferentialMeasurableWeilTotalMass
import SMSFormula.AdelicLeftCosets

/-!
# Differential mass of one proper finite-adelic selector

The arbitrary-scale finite-subgroup transversal identity is specialized to
one proper local-stabilizer selector inside the concrete
finite-adelic special-orthogonal lattice stabilizer.  Its mass is the
internally constructed finite differential stabilizer volume divided by the
finite stabilizer cardinality.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Balanced differential mass identity for one proper local-stabilizer
selector. -/
theorem
    concreteProperLocalRightStabilizerEmbeddingRealSlice_differential_natCard_mul_measure
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (P : ℝ) :
    (Nat.card
        (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
          g) :
        ℝ≥0∞) *
        L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P
          (L.concreteProperLocalRightStabilizerEmbeddingRealSlice g) =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  letI : Finite
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
        g) :=
    L.finite_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
      g
  letI : Fintype
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
        g) :=
    Fintype.ofFinite _
  rw [
    (L.concreteProperLocalRightStabilizerEmbeddingRealSlice_isLeftCosetTransversal
      g).natCard_mul_measure_eq_univ
        (L.concreteProperLocalRightStabilizerEmbeddingRealSlice_measurableSet g),
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ P
  ]

/-- Exact arbitrary-scale differential mass of one proper local-stabilizer
selector. -/
theorem
    concreteProperLocalRightStabilizerEmbeddingRealSlice_differential_measure
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (P : ℝ) :
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P
        (L.concreteProperLocalRightStabilizerEmbeddingRealSlice g) =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
        ENNReal.ofReal
          (1 / (Nat.card
            (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
              g) :
            ℝ)) := by
  letI : Finite
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
        g) :=
    L.finite_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
      g
  letI : Fintype
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
        g) :=
    Fintype.ofFinite _
  rw [
    (L.concreteProperLocalRightStabilizerEmbeddingRealSlice_isLeftCosetTransversal
      g).measure_eq_univ_mul_inv_natCard
        (L.concreteProperLocalRightStabilizerEmbeddingRealSlice_measurableSet g),
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ P
  ]

end PositiveDefiniteIntegralLattice
