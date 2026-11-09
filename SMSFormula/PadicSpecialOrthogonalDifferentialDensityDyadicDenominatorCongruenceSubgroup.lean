import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDeterminantLossResidue
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup

/-!
# The shifted dyadic denominator-congruence subgroup

At the selected dyadic density depth `k`, the associated-bilinear denominator
is the local-dual denominator at depth `k - 1`.  This module packages the
correspondingly shifted stabilizer subgroup and proves that relative membership
is exactly equality of the complete selected-depth quotient-family values.

No principal-kernel quotient, torsor, coordinate quotient, cardinality, or
dyadic gauge value is constructed here.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- At the selected dyadic density depth, the associated-bilinear denominator
is exactly the local-dual denominator one level lower. -/
theorem
    associatedBilinearDualPadicDenominator_densityDepth_eq_localDualPadicDenominator_pred_dyadic
    (L : PositiveDefiniteIntegralLattice n) :
    associatedBilinearDualPadicDenominator L 2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2) =
      localDualPadicDenominator L 2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk :=
    L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  have hdepth :
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1) + 1 =
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 := by
    omega
  rw [← hdepth]
  exact
    L.associatedBilinearDualPadicDenominator_succ_eq_localDualPadicDenominator_dyadic
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)

/-- The dyadic intermediate subgroup: local-dual denominator congruence at
one level below the selected ordinary reduction depth. -/
def localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    Subgroup (L.localPadicLatticeStabilizerSubgroup 2) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact
    L.localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup 2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)

/-- Relative membership in the shifted dyadic subgroup is its literal
columnwise local-dual denominator condition. -/
theorem
    mul_inv_mem_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g h : L.localPadicLatticeStabilizerSubgroup 2) :
    g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup ↔
      ∀ j : Fin n,
        (fun i ↦
          L.localPadicLatticeStabilizerIntegralGL 2 g i j -
            L.localPadicLatticeStabilizerIntegralGL 2 h i j) ∈
          localDualPadicDenominator L 2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact
    L.mul_inv_mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff
      2 (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1) g h

/-- For two actual dyadic integral stabilizers, relative membership in the
shifted subgroup is exactly equality of their complete selected-depth
associated-bilinear quotient-family values. -/
theorem
    mul_inv_mem_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup_iff_quotient_eq
    (L : PositiveDefiniteIntegralLattice n)
    (g h : L.localPadicLatticeStabilizerSubgroup 2) :
    g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup ↔
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer
            2 g) =
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer
            2 h) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup,
    L.mul_inv_mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff,
    ← L.associatedBilinearDualPadicDenominator_densityDepth_eq_localDualPadicDenominator_pred_dyadic]
  exact
    (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer_quotient_eq_iff_padicColumnDifference_mem
      2 g h).symm

end PositiveDefiniteIntegralLattice
