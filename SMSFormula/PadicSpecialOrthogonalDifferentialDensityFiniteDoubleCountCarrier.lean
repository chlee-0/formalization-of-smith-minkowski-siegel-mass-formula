import SMSFormula.PadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramQuotientFiber
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue

/-!
# Finite double-count carriers for the odd-prime gauge identity

This module writes the two sides of the odd-prime cardinality identity as
finite types.  The left carrier is the sigma type, over
the selected associated-bilinear quotient family, of attained density residues
times the corresponding infinitely liftable raw Gram fiber.  The right carrier
is the quotient family times the determinant-loss residue carrier.

The pointwise gauge target is proved equivalent exactly to equality of their
cardinalities.  No map or equivalence between these carriers is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

noncomputable local instance infinitelyLiftableRawGramSolution_finite
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Finite
      (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p) := by
  unfold
    localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
  infer_instance

/-- The infinitely liftable raw Gram fiber over one selected quotient-family
value. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :=
  {X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p //
    L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramToQuotientFamily
        p hp2 X = Y}

/-- The left double-count carrier above one quotient-family value: an attained
density residue paired with an infinitely liftable raw Gram point in that
fiber. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityFiberwiseDoubleCountCarrier
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :=
  L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      p ×
    L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber
      p hp2 Y

/-- The aggregate left double-count carrier, retaining the quotient value and
the corresponding fiber literally. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityLeftDoubleCountCarrier
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :=
  Σ Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p,
    L.localPadicSpecialOrthogonalDifferentialDensityFiberwiseDoubleCountCarrier
      p hp2 Y

/-- The aggregate right double-count carrier: one selected quotient-family
value paired with one determinant-loss residue. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityRightDoubleCountCarrier
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :=
  L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
      p ×
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
      p

/-- Cardinality of the left carrier over one quotient-family value. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityFiberwiseDoubleCountCarrier
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityFiberwiseDoubleCountCarrier
          p hp2 Y) =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          p).ncard *
        Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber
            p hp2 Y) := by
  rw [Nat.card_prod, Nat.card_coe_set_eq]

/-- Cardinality of the determinant-loss carrier on the right above each
quotient-family value. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue_eq_pairingDeterminantPrimePow
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
          p) =
      p ^
        (padicValInt p L.pairingDeterminant *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) :=
  L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
    p

/-- The aggregate left carrier has cardinality `N` times the exact sum of the
infinitely liftable quotient-fiber cardinalities. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityLeftDoubleCountCarrier
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityLeftDoubleCountCarrier
          p hp2) =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          p).ncard *
        (∑ Y :
            L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
              p,
          Nat.card
            (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber
              p hp2 Y)) := by
  rw [Nat.card_sigma]
  simp_rw [L.natCard_localPadicSpecialOrthogonalDifferentialDensityFiberwiseDoubleCountCarrier
    p hp2]
  rw [Finset.mul_sum]

/-- The aggregate right carrier has cardinality `p^(v*d) * Q`. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityRightDoubleCountCarrier
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityRightDoubleCountCarrier
          p) =
      p ^
          (padicValInt p L.pairingDeterminant *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
        associatedBilinearDualQuotientCount L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
  rw [Nat.card_prod,
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue_eq_pairingDeterminantPrimePow,
    associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  exact Nat.mul_comm _ _

/-- The odd-prime pointwise gauge target is exactly equality of the two named
finite double-count carrier cardinalities. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_natCard_leftDoubleCountCarrier_eq_rightDoubleCountCarrier
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq2 : q.1 ≠ 2) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q ↔
      Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityLeftDoubleCountCarrier
            q.1 hq2) =
        Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityRightDoubleCountCarrier
            q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_densityResidueCardinality_mul_sum_infinitelyLiftableRawGramFibers
      q hq2,
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityLeftDoubleCountCarrier
      q.1 hq2,
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityRightDoubleCountCarrier
      q.1]

end PositiveDefiniteIntegralLattice
