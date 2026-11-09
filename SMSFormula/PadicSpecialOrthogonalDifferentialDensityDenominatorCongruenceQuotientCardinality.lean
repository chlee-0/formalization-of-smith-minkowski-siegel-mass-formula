import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientDescent
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityFiniteDoubleCountCarrier
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceResidueCardinalityPrimePower

/-!
# Cardinality of the odd-prime denominator Cayley quotient

This module takes cardinalities of the explicit quotient equivalence
`H_k/K_k ≃ T/N`.  Lagrange's theorem for the attained-residue additive
subgroup computes every exact liftable quotient fiber, and the existing sigma
decomposition closes the odd-prime finite double count and pointwise gauge
defect.

No dyadic statement or finite prime product is formed.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

noncomputable local instance infinitelyLiftableRawGramSolution_finite_quotientCardinality
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Finite
      (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
        p) := by
  unfold
    localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramSolution
  infer_instance

/-- The attained-residue subgroup has exactly the cardinality of the existing
residue-image subtype. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup_eq_residueImage_ncard
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
          p hp2) =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
        p).ncard := by
  rw [← Nat.card_coe_set_eq]
  exact
    Nat.card_congr
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexEquivAttainedResidueAddSubgroup
        p hp2).symm

/-- Lagrange's theorem computes the determinant-loss carrier as the attained
subgroup cardinality times the quotient cardinality. -/
theorem
    natCard_attainedResidueAddSubgroup_mul_determinantLossQuotient_eq_determinantLossResidue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
            p hp2) *
        Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossQuotient
            p hp2) =
      Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
          p) := by
  rw [Nat.mul_comm]
  exact
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
      p hp2).card_eq_card_quotient_mul_card_addSubgroup.symm

/-- Every exact liftable quotient fiber has the cardinality of `T/N`. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber_eq_determinantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber
          p hp2 Y) =
      Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossQuotient
          p hp2) :=
  Nat.card_congr
    (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiberEquivDeterminantLossQuotient
      p hp2 Y)

/-- Above every quotient-family value, the attained-residue/liftable-fiber
product has exactly the cardinality of the determinant-loss carrier. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityFiberwiseDoubleCountCarrier_eq_determinantLossResidue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityFiberwiseDoubleCountCarrier
          p hp2 Y) =
      Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
          p) := by
  rw [L.natCard_localPadicSpecialOrthogonalDifferentialDensityFiberwiseDoubleCountCarrier
    p hp2 Y]
  rw [←
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup_eq_residueImage_ncard
      p hp2]
  rw [L.natCard_localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber_eq_determinantLossQuotient
    p hp2 Y]
  exact
    L.natCard_attainedResidueAddSubgroup_mul_determinantLossQuotient_eq_determinantLossResidue
      p hp2

/-- The two literal aggregate double-count carriers have the same
cardinality. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityLeftDoubleCountCarrier_eq_rightDoubleCountCarrier
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityLeftDoubleCountCarrier
          p hp2) =
      Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityRightDoubleCountCarrier
          p) := by
  rw [Nat.card_sigma, Nat.card_prod]
  simp_rw [
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityFiberwiseDoubleCountCarrier_eq_determinantLossResidue
      p hp2]
  simp [Finset.sum_const, Nat.card_eq_fintype_card]

/-- The exact natural-number residue-cardinality identity at every odd prime. -/
theorem
    densityResidueCardinality_mul_ordinaryReductionRangeCard_eq_pairingDeterminantPrimePow_mul_quotientCount
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq2 : q.1 ≠ 2) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
        q.1).ncard *
        Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
            q.1) =
      q.1 ^
          (padicValInt q.1 L.pairingDeterminant *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
        associatedBilinearDualQuotientCount L q.1
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  have hcarriers :=
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityLeftDoubleCountCarrier_eq_rightDoubleCountCarrier
      q.1 hq2
  have hgauge :=
    (L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_natCard_leftDoubleCountCarrier_eq_rightDoubleCountCarrier
      q hq2).2 hcarriers
  exact
    (L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_densityResidueCardinalityPrimePower
      q hq2).1 hgauge

/-- The odd-prime pointwise gauge defect. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq2 : q.1 ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
          (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
        q := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  exact
    (L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_densityResidueCardinalityPrimePower
      q hq2).2
      (L.densityResidueCardinality_mul_ordinaryReductionRangeCard_eq_pairingDeterminantPrimePow_mul_quotientCount
        q hq2)

end PositiveDefiniteIntegralLattice
