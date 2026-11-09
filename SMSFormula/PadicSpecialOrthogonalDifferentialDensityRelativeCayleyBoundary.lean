import SMSFormula.PadicSpecialOrthogonalDifferentialDensityFiniteDoubleCountCarrier
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceElementaryCoordinates

/-!
# Relative Cayley comparison for liftable quotient fibers

This module compares the stabilizer reconstructed from an infinitely
liftable raw Gram solution with the selected Hensel stabilizer attached to an
associated-bilinear quotient value.  Their relative element lies in the
selected-depth principal congruence kernel exactly when their *complete*
ordinary reductions agree.  On a fixed quotient fiber this happens exactly at
the selected Hensel basepoint.

Thus equality only after associated-bilinear coarsening is not enough to put
the relative element in the identity-centered inverse-Cayley chart.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The integral stabilizer reconstructed from the selected coherent branch
of an infinitely liftable raw Gram solution. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramStabilizer
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p) :
    L.localPadicLatticeStabilizerSubgroup p :=
  (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolutionChain
    p X).padicLimitStabilizer

/-- The selected integral Hensel stabilizer attached to one
associated-bilinear quotient-family value. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyHenselStabilizer
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    L.localPadicLatticeStabilizerSubgroup p :=
  associatedBilinearDualQuotientSolutionFamilyTowerPadicStabilizer
    L p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p).associated_bilinear_quadratic_depth
    Y

/-- The original relative stabilizer between a coherent-branch lift and the
selected Hensel lift of a quotient-family value. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityRelativeHenselStabilizer
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    L.localPadicLatticeStabilizerSubgroup p :=
  L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramStabilizer
      p X *
    (L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyHenselStabilizer
      p Y)⁻¹

/-- The selected-depth reduction of the relative stabilizer is literally the
quotient of the two complete ordinary reductions. -/
theorem
    localPadicLatticeStabilizerReduction_relativeHenselStabilizer
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    L.localPadicLatticeStabilizerReduction p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        (L.localPadicSpecialOrthogonalDifferentialDensityRelativeHenselStabilizer
          p X Y) =
      (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToOrdinaryReduction
          p X).1 *
        (L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
          p Y).1⁻¹ := by
  simp only [
    localPadicSpecialOrthogonalDifferentialDensityRelativeHenselStabilizer,
    map_mul, map_inv]
  rfl

/-- The relative stabilizer is in the selected-depth principal kernel exactly
when the complete ordinary reduction of the liftable point is the selected
Hensel reduction. -/
theorem
    relativeHenselStabilizer_mem_principalCongruenceSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    L.localPadicSpecialOrthogonalDifferentialDensityRelativeHenselStabilizer
        p X Y ∈
        L.localPadicPrincipalCongruenceSubgroup p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) ↔
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToOrdinaryReduction
          p X =
        L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
          p Y := by
  change
    L.localPadicLatticeStabilizerReduction p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        (L.localPadicSpecialOrthogonalDifferentialDensityRelativeHenselStabilizer
          p X Y) = 1 ↔ _
  rw [L.localPadicLatticeStabilizerReduction_relativeHenselStabilizer]
  constructor
  · intro h
    apply Subtype.ext
    exact (mul_inv_eq_one.mp h)
  · intro h
    have hv := congrArg Subtype.val h
    exact mul_inv_eq_one.mpr hv

end PositiveDefiniteIntegralLattice
