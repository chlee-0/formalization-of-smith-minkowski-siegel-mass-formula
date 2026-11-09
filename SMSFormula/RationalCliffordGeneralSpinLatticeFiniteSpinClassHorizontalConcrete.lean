import SMSFormula.RationalCliffordSpinCandidateLatticeProperQuotientFiniteDoubleCoset
import Mathlib.Probability.ProductMeasure
import SMSFormula.RationalCliffordSpinCandidateLatticeGoodIntegralPointMapPushforward
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockSplit
import SMSFormula.RationalCliffordGeneralSpinLatticeIntegralSpinorRange
import SMSFormula.RationalCliffordSpinCandidateAlmostEverywhereIntegralLifting
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
import SMSFormula.RationalSquareClassFiniteLocalizationSurjectivity
import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteAdelicSOSurjectivity
import SMSFormula.RationalCliffordGeneralSpinAdelicProduct
import SMSFormula.RationalCliffordGeneralSpinVerticalEquivalence
import SMSFormula.RationalCliffordGeneralSpinAdelicSpecialOrthogonalQuotient

/-!
# Concrete horizontal representatives of finite Spin classes

The general rational-quadratic-space `SO` carrier and the concrete lattice
carrier commute with right multiplication on their rational left quotients.
For the explicitly chosen finite-class general-Spin lift, its horizontal
`SO` projection becomes exactly the concrete full-adelic embedding of the
chosen compact-open representative, with identity real component.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- The full-adelic carrier identification preserves the literal real and
finite components. -/
theorem rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_components
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv g) =
      L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change
      (((L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv g).1.1.1.map
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)).map
          rationalInfiniteAdeleRingEquivReal) =
        ((g.1.1.1.map
          (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)).map
            rationalInfiniteAdeleRingEquivReal)
    rw [L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_apply_matrix]
  · apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change
      (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv g).1.1.1.map
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) =
      (g.1.1.1.map
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele))
    rw [L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_apply_matrix]

/-- The general-to-concrete quotient equivalence commutes with adelic right
multiplication. -/
theorem rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_rightMul
    (L : PositiveDefiniteIntegralLattice n)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv
        (L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientRightMul x q) =
      L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv x)
        (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv q) := by
  induction q using Quot.inductionOn with
  | _ g =>
    change L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv (g * x)) =
      L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv g *
          L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv x)
    rw [map_mul]

end PositiveDefiniteIntegralLattice
