import SMSFormula.GenericPrincipalIsoOfEpi
import SMSFormula.RationalCliffordSpinCandidateInvariantGroupScheme
import SMSFormula.RationalSpecialOrthogonalReduced
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# A generic isomorphism patch for the Spin invariant quotient

The implemented comparison

```text
O(SO_V) -> O(SpinCandidate_V)^sigma
```

is injective, finite type, and a commutative ring epimorphism, while its source
is reduced.  The generic commutative-algebra theorem therefore supplies a
principal neighborhood meeting every minimal component on which the
comparison is an isomorphism.

This is only the generic patch needed by the subsequent algebraic-group
translation argument.  It does not identify the two global coordinate
rings or prove the original Spin-candidate cover flat.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- At every minimal prime of `O(SO_V)`, one principal open meeting that
component identifies the implemented `SO` coordinate ring with the literal
fixed ring. -/
theorem exists_negOneInvariant_awayMap_bijective_of_mem_minimalPrimes
    (p : Ideal V.specialOrthogonalCoordinateRing)
    (hp : p ∈ minimalPrimes V.specialOrthogonalCoordinateRing) :
    ∃ d : V.specialOrthogonalCoordinateRing, d ∉ p ∧
      Function.Bijective
        (Localization.awayMap
          (algebraMap V.specialOrthogonalCoordinateRing
            V.negOneInvariantSubalgebra) d) := by
  letI : IsReduced V.specialOrthogonalCoordinateRing :=
    V.specialOrthogonalCoordinateRing_isReduced
  letI : Algebra.IsEpi V.specialOrthogonalCoordinateRing
      V.negOneInvariantSubalgebra :=
    V.specialOrthogonalToNegOneInvariant_isEpi
  letI : Algebra.FiniteType V.specialOrthogonalCoordinateRing
      V.negOneInvariantSubalgebra :=
    V.negOneInvariantSubalgebra_finiteType
  apply Algebra.exists_awayMap_bijective_of_mem_minimalPrimes
    (R := V.specialOrthogonalCoordinateRing)
    (S := V.negOneInvariantSubalgebra) _ p hp
  change Function.Injective V.specialOrthogonalToNegOneInvariantAlgHom
  exact V.specialOrthogonalToNegOneInvariantAlgHom_injective

end RationalQuadraticSpaceMatrix
