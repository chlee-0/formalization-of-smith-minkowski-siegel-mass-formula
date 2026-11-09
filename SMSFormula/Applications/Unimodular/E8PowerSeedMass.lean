import SMSFormula.Applications.Unimodular.StableIdentityComparison.StableRecursive
import SMSFormula.StandardAxiomsGuard

/-!
# E8-power seed mass

This module states the stable-identity-comparison result for `typeIISeed k`
(the finite second-orbit argument of Voskresenskii) in the application layer.
The target is the ordinary genus mass of the concrete seed lattice, with the
finite genus sum over full integral isometry groups stated separately.  No
geometric mass is defined, and no genus-uniqueness assertion is used.
-/

noncomputable section
open scoped BigOperators
open PositiveDefiniteIntegralLattice UnimodularMass

namespace PositiveDefiniteIntegralLattice

/-- The all-positive E8-power seed ordinary genus mass endpoint, routed through
checked finite-coordinate Voskresenskii second-orbit certificates. -/
theorem typeIISeed_ordinaryGenusMass_eq_typeIIConstant_of_pos
    (k : ℕ) (hk : 0 < k) :
    (typeIISeed k).ordinaryGenusMass = typeIIConstant (8 * k) :=
  StableIdentityComparisonStableRecursive.all_positive_typeIISeed_ordinaryGenusMass_eq_typeIIConstant
    k hk

/-- Literal genus-sum form of
`typeIISeed_ordinaryGenusMass_eq_typeIIConstant_of_pos`. -/
theorem typeIISeed_literal_sum_eq_typeIIConstant_of_pos
    (k : ℕ) (hk : 0 < k) :
    (∑ A : (typeIISeed k).genus,
      ((Fintype.card (genusClassRepresentative (typeIISeed k) A).IsometryGroup : ℚ)⁻¹)) =
        typeIIConstant (8 * k) :=
  StableIdentityComparisonStableRecursive.all_positive_typeIISeed_literal_sum_eq_typeIIConstant
    k hk

end PositiveDefiniteIntegralLattice


#assert_not_declared RationalQuadraticSpaceMatrix.specialOrthogonalTamagawaNumberENNReal_eq_two
