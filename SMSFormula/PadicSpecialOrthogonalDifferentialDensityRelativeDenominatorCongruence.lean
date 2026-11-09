import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRelativeCayleyBoundary

/-!
# Relative denominator congruence on quotient fibers

Equality after coarsening an ordinary stabilizer reduction to the selected
associated-bilinear quotient family is equivalent to a literal columnwise
congruence modulo the selected integral denominator integral model.  Specializing this
statement to an infinitely liftable fiber point and the selected Hensel
basepoint gives the first exact input for the intermediate denominator-
congruence subgroup suggested by the local double-count argument.

The column difference uses the standard natural representatives of entries in
`ZMod (p^k)`, exactly as the existing quotient-family map does.  No principal
congruence, relative Cayley coordinate, subgroup action, or cardinality value
is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The literal integral column difference used by the selected quotient
coarsening map, with every finite-ring entry represented by its standard
natural representative. -/
def localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionColumnDifference
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (u v :
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p)
    (j : Fin n) : Fin n → ℤ :=
  fun i ↦ ((u.1.1 i j).val : ℤ) - ((v.1.1 i j).val : ℤ)

/-- Two complete ordinary reductions have the same selected
associated-bilinear quotient family exactly when all of their literal lifted
column differences lie in the selected denominator integral model. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_eq_iff_columnDifference_mem
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (u v :
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p) :
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p u =
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
          p v ↔
      ∀ j : Fin n,
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionColumnDifference
            p u v j ∈
          associatedBilinearDualPadicDenominatorIntegralPreimage L p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
  let k := L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  let E := associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  let hPE : primePowCoordinateSubmodule (n := n) p k ≤ E :=
    L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
      p k
  constructor
  · intro huv j
    have hval := congrArg Subtype.val huv
    have hj := congrFun hval j
    change
      E.mkQ (fun i ↦ ((u.1.1 i j).val : ℤ)) =
        E.mkQ (fun i ↦ ((v.1.1 i j).val : ℤ)) at hj
    change
      (Submodule.Quotient.mk (fun i ↦ ((u.1.1 i j).val : ℤ)) :
          (Fin n → ℤ) ⧸ E) =
        Submodule.Quotient.mk (fun i ↦ ((v.1.1 i j).val : ℤ)) at hj
    rw [Submodule.Quotient.eq] at hj
    exact hj
  · intro huv
    apply Subtype.ext
    funext j
    change
      E.mkQ (fun i ↦ ((u.1.1 i j).val : ℤ)) =
        E.mkQ (fun i ↦ ((v.1.1 i j).val : ℤ))
    change
      (Submodule.Quotient.mk (fun i ↦ ((u.1.1 i j).val : ℤ)) :
          (Fin n → ℤ) ⧸ E) =
        Submodule.Quotient.mk (fun i ↦ ((v.1.1 i j).val : ℤ))
    rw [Submodule.Quotient.eq]
    exact huv j

/-- A liftable point and the selected Hensel point in the same quotient fiber
have column differences in the associated-bilinear denominator integral model. -/
theorem
    infinitelyLiftableRawGramFiber_ordinaryReductionColumnDifference_mem_denominator
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p)
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber
        p hp2 Y) :
    ∀ j : Fin n,
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionColumnDifference
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToOrdinaryReduction
            p X.1)
          (L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
            p Y)
          j ∈
        associatedBilinearDualPadicDenominatorIntegralPreimage L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
  apply
    (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_eq_iff_columnDifference_mem
      p _ _).mp
  calc
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToOrdinaryReduction
          p X.1) =
        L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
          p hp2 X.1 :=
      L.localPadicSpecialOrthogonalDifferentialDensity_ordinaryReduction_infinitelyLiftableRawGram_commutes
        p hp2 X.1
    _ = Y := X.2
    _ =
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
            p Y) :=
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_apply_lift
        p Y).symm

/-- The preceding congruence is the column difference of the two
selected-depth stabilizer reductions given by the coherent branch
and the Hensel tower. -/
theorem
    infinitelyLiftableRawGramFiber_stabilizerReductionColumnDifference_mem_denominator
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p)
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber
        p hp2 Y) :
    ∀ j : Fin n,
      (fun i ↦
          ((L.localPadicLatticeStabilizerReduction p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
              (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramStabilizer
                p X.1) i j).val : ℤ) -
            ((L.localPadicLatticeStabilizerReduction p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
              (L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyHenselStabilizer
                p Y) i j).val : ℤ)) ∈
        associatedBilinearDualPadicDenominatorIntegralPreimage L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
  simpa only [
    localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionColumnDifference,
    localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramStabilizer,
    localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyHenselStabilizer] using
    L.infinitelyLiftableRawGramFiber_ordinaryReductionColumnDifference_mem_denominator
      p hp2 Y X

end PositiveDefiniteIntegralLattice
