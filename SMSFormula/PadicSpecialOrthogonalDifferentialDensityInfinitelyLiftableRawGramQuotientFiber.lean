import SMSFormula.PadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramCarrier
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramQuotientBoundary
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceResidueCardinalityPrimePower

/-!
# Quotient fibers of infinitely liftable raw Gram solutions

At an odd prime, this module restricts the selected raw-Gram-to-associated-
bilinear quotient map to the infinitely liftable raw Gram carrier.  The
restricted map is transported across the existing equivalence with the
ordinary stabilizer reduction range.  Its fibers are therefore equivalent to
the ordinary-reduction fibers, not to the larger complete raw Gram fibers.

The pointwise gauge criterion is restated as a sum of these exact liftable
fiber cardinalities.  No fiber uniformity or cardinality value is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The selected raw Gram coarsening restricted to solutions admitting one
coherent infinite lift branch. -/
def localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution p →
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p :=
  fun X ↦
    L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily
      p hp2 X.1

/-- The equivalence from ordinary reductions to infinitely liftable raw Gram
solutions commutes literally with the selected quotient maps. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensity_infinitelyLiftableRawGram_ordinaryReduction_commutes
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (u : L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p) :
    L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
        p hp2
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionEquivInfinitelyLiftableRawGram
          p u) =
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p u := by
  exact
    L.localPadicSpecialOrthogonalDifferentialDensity_rawGram_ordinaryReduction_commutes
      p hp2 u

/-- The inverse equivalence from an infinitely liftable raw Gram solution to
the ordinary range also commutes with the quotient maps. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensity_ordinaryReduction_infinitelyLiftableRawGram_commutes
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p) :
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p
        ((L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionEquivInfinitelyLiftableRawGram
          p).symm X) =
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
        p hp2 X := by
  let e :=
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionEquivInfinitelyLiftableRawGram
      p
  calc
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
        p (e.symm X) =
        L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
          p hp2 (e (e.symm X)) :=
      (L.localPadicSpecialOrthogonalDifferentialDensity_infinitelyLiftableRawGram_ordinaryReduction_commutes
        p hp2 (e.symm X)).symm
    _ =
        L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
          p hp2 X := by rw [e.apply_symm_apply]

/-- The quotient map on infinitely liftable raw Gram solutions is surjective.
The preimage is the selected ordinary Hensel lift transported through the
literal carrier equivalence. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily_surjective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Function.Surjective
      (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
        p hp2) := by
  intro Y
  obtain ⟨u, hu⟩ :=
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_surjective
      p Y
  refine
    ⟨L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionEquivInfinitelyLiftableRawGram
      p u, ?_⟩
  rw [L.localPadicSpecialOrthogonalDifferentialDensity_infinitelyLiftableRawGram_ordinaryReduction_commutes]
  exact hu

/-- Over each quotient-family value, the infinitely liftable raw Gram fiber
is equivalent exactly to the ordinary stabilizer reduction fiber. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiberEquivOrdinaryReductionFiber
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    {X :
        L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
          p //
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
          p hp2 X = Y} ≃
      {u :
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p //
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            p u = Y} :=
  let e :=
    L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionEquivInfinitelyLiftableRawGram
      p
  { toFun := fun X ↦
      ⟨e.symm X.1,
        (L.localPadicSpecialOrthogonalDifferentialDensity_ordinaryReduction_infinitelyLiftableRawGram_commutes
          p hp2 X.1).trans X.2⟩
    invFun := fun u ↦
      ⟨e u.1,
        (L.localPadicSpecialOrthogonalDifferentialDensity_infinitelyLiftableRawGram_ordinaryReduction_commutes
          p hp2 u.1).trans u.2⟩
    left_inv := by
      intro X
      apply Subtype.ext
      exact e.apply_symm_apply X.1
    right_inv := by
      intro u
      apply Subtype.ext
      exact e.symm_apply_apply u.1 }

/-- The exact liftable raw Gram fiber and ordinary stabilizer fiber have the
same cardinality. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber_eq_ordinaryReductionFiber
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    Nat.card
        {X :
            L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
              p //
          L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
              p hp2 X = Y} =
      Nat.card
        {u :
            L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p //
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
              p u = Y} :=
  Nat.card_congr
    (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiberEquivOrdinaryReductionFiber
      p hp2 Y)

/-- The infinitely liftable selected-depth raw Gram carrier is the exact sum
of its quotient-family fibers. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGram_eq_sum_fibers
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
          p) =
      ∑ Y :
          L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
            p,
        Nat.card
          {X :
              L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
                p //
            L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
                p hp2 X = Y} := by
  rw [←
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_infinitelyLiftableRawGram
      p]
  rw [L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_sum_fibers]
  apply Finset.sum_congr rfl
  intro Y _hY
  exact
    (L.natCard_localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber_eq_ordinaryReductionFiber
      p hp2 Y).symm

/-- The odd-prime gauge-defect criterion with the ordinary factor replaced by
the sum of the infinitely liftable raw Gram fibers. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_densityResidueCardinality_mul_sum_infinitelyLiftableRawGramFibers
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq2 : q.1 ≠ 2) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          q.1).ncard *
          (∑ Y :
              L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
                q.1,
            Nat.card
              {X :
                  L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
                    q.1 //
                L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
                    q.1 hq2 X = Y}) =
        q.1 ^
            (padicValInt q.1 L.pairingDeterminant *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          associatedBilinearDualQuotientCount L q.1
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_densityResidueCardinalityPrimePower
      q hq2,
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_infinitelyLiftableRawGram
      q.1,
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGram_eq_sum_fibers
      q.1 hq2]

end PositiveDefiniteIntegralLattice
