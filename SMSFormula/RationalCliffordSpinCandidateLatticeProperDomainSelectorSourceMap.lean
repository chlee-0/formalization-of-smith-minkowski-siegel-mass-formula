import SMSFormula.SpecialOrthogonalFullAdelicProperQuotientMeasurableEquiv
import Mathlib.Probability.ProductMeasure
import SMSFormula.RationalCliffordSpinCandidateLatticeGoodIntegralPointMapPushforward
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockSplit
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FieldSimp
import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteAdelicStabilizerCarrier
import SMSFormula.SpecialOrthogonalFiniteAdelicDifferentialSelectorMass
import SMSFormula.AdelicLeftCosets

/-!
# Map the proper `SO` domain to the finite selector source

Every point of the exact proper fundamental domain lies in a unique
proper piece and therefore has a compact-open selector factor.  At a
finite comparison set, that factor determines the marked Spin-image class
and hence the refined orbit label.  This file defines the resulting map to
the measured selector-source carrier.  The statements are at the level of
carriers; the pushforward measure is not treated here.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- The unique proper-piece label containing a point of the exact proper
fundamental domain. -/
noncomputable def concreteFullAdelicProperDomainPieceLabel
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (z : {g : L.ConcreteFullAdelicSpecialOrthogonalGroup //
      g ∈ L.concreteFullAdelicProperTransversal}) :
    L.ConcreteProperRationalDoubleCosetSet := by
  have hz : z.1 ∈ ⋃ C : L.ConcreteProperRationalDoubleCosetSet,
      L.concreteFullAdelicProperTransversalPiece C := by
    rw [L.iUnion_concreteFullAdelicProperTransversalPiece]
    exact z.2
  exact Classical.choose (Set.mem_iUnion.mp hz)

/-- The chosen proper-piece label contains the supplied domain point. -/
theorem concreteFullAdelicProperDomainPieceLabel_spec
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (z : {g : L.ConcreteFullAdelicSpecialOrthogonalGroup //
      g ∈ L.concreteFullAdelicProperTransversal}) :
    z.1 ∈ L.concreteFullAdelicProperTransversalPiece
      (L.concreteFullAdelicProperDomainPieceLabel z) :=
  Classical.choose_spec (Set.mem_iUnion.mp (by
    rw [L.iUnion_concreteFullAdelicProperTransversalPiece]
    exact z.2))

/-- The proper-piece label is uniquely determined. -/
theorem concreteFullAdelicProperDomainPieceLabel_eq_of_mem
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (z : {g : L.ConcreteFullAdelicSpecialOrthogonalGroup //
      g ∈ L.concreteFullAdelicProperTransversal})
    (C : L.ConcreteProperRationalDoubleCosetSet)
    (hzC : z.1 ∈ L.concreteFullAdelicProperTransversalPiece C) :
    L.concreteFullAdelicProperDomainPieceLabel z = C := by
  by_contra hne
  exact Set.disjoint_left.mp
    (L.pairwiseDisjoint_concreteFullAdelicProperTransversalPiece hne)
    (L.concreteFullAdelicProperDomainPieceLabel_spec z) hzC

/-- The selected compact-open factor of a proper-domain point in its unique
proper piece. -/
noncomputable def concreteFullAdelicProperDomainSelectorElement
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (z : {g : L.ConcreteFullAdelicSpecialOrthogonalGroup //
      g ∈ L.concreteFullAdelicProperTransversal}) :
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
  Classical.choose
    ((L.mem_concreteFullAdelicProperTransversalPiece_iff_exists_factor
      (L.concreteFullAdelicProperDomainPieceLabel z) z.1).mp
        (L.concreteFullAdelicProperDomainPieceLabel_spec z))

/-- The selected compact-open factor belongs to the literal arithmetic
selector slice. -/
theorem concreteFullAdelicProperDomainSelectorElement_mem
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (z : {g : L.ConcreteFullAdelicSpecialOrthogonalGroup //
      g ∈ L.concreteFullAdelicProperTransversal}) :
    L.concreteFullAdelicProperDomainSelectorElement z ∈
      L.concreteProperLocalRightStabilizerEmbeddingRealSlice
        (Quot.out (L.concreteFullAdelicProperDomainPieceLabel z)) :=
  (Classical.choose_spec
    ((L.mem_concreteFullAdelicProperTransversalPiece_iff_exists_factor
      (L.concreteFullAdelicProperDomainPieceLabel z) z.1).mp
        (L.concreteFullAdelicProperDomainPieceLabel_spec z))).1

/-- Reassembling the real component and selected compact-open factor recovers
the proper-domain point. -/
theorem concreteFullAdelicProperDomainSelectorElement_factor
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (z : {g : L.ConcreteFullAdelicSpecialOrthogonalGroup //
      g ∈ L.concreteFullAdelicProperTransversal}) :
    z.1 =
      L.concreteFullAdelicProperTransversalRepresentative
          (L.concreteFullAdelicProperDomainPieceLabel z) *
        (L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
          ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv z.1).1,
            L.concreteFullAdelicProperDomainSelectorElement z)).1 :=
  (Classical.choose_spec
    ((L.mem_concreteFullAdelicProperTransversalPiece_iff_exists_factor
      (L.concreteFullAdelicProperDomainPieceLabel z) z.1).mp
        (L.concreteFullAdelicProperDomainPieceLabel_spec z))).2

end PositiveDefiniteIntegralLattice
