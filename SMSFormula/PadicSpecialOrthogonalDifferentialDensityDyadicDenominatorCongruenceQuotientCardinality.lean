import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientDescent
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDoubledAttainedResidueCardinality
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDeterminantLossResidue
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityQuotientFiber

/-!
# Cardinalities of the shifted dyadic denominator quotient

This module takes cardinalities only after the explicit equivalences have been
constructed.  It records independently the doubled-attained subgroup size,
finite additive Lagrange identity, uniform ordinary-fiber cardinality, and
exact sum over associated-bilinear quotient values.

Combining these natural-number identities gives the precise power
of two forced by the shifted dyadic quotient.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_dyadic_quotient_cardinality_audit :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The newly packaged additive subgroup has exactly the cardinality of the
literal doubled attained residue subtype. -/
theorem
    natCard_dyadicDoubledAttainedResidueAddSubgroup_eq_index
    (L : PositiveDefiniteIntegralLattice n) :
    Nat.card
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup =
      Nat.card
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex :=
  (Nat.card_congr
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndexEquivAddSubgroup).symm

/-- Lagrange's theorem computes the enlarged determinant-loss carrier as the
doubled attained subgroup cardinality times its additive quotient. -/
theorem
    natCard_dyadicDoubledAttainedResidueAddSubgroup_mul_determinantLossQuotient_eq_determinantLossResidue
    (L : PositiveDefiniteIntegralLattice n) :
    Nat.card
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup *
        Nat.card
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossQuotient =
      Nat.card
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue := by
  rw [Nat.mul_comm]
  exact
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup.symm

/-- Every complete ordinary dyadic quotient fiber has the cardinality of the
finite additive quotient `T₂/N₂'`. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionFiber_eq_dyadicDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        2) :
    Nat.card
        {u :
            L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange 2 //
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
              2 u = Y} =
      Nat.card
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossQuotient :=
  Nat.card_congr
    (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionFiberEquivDyadicDeterminantLossQuotient
      Y)

/-- The complete ordinary dyadic reduction range is the quotient-family count
times the common additive-quotient fiber cardinality. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_quotientCount_mul_dyadicDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
          2) =
      associatedBilinearDualQuotientCount L 2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2) *
        Nat.card
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossQuotient := by
  rw [
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_sum_fibers
      2]
  simp_rw [
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionFiber_eq_dyadicDeterminantLossQuotient]
  simp [Finset.sum_const,
    localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily,
    associatedBilinearDualQuotientCount,
    coordinateLocalDualQuotientCount]

/-- The original attained dyadic residue count is the doubled attained
subgroup cardinality times the one forgotten binary layer. -/
theorem
    natCard_dyadicDoubledAttainedResidueAddSubgroup_mul_two_pow_tangentRank_eq_residueImage_ncard
    (L : PositiveDefiniteIntegralLattice n) :
    Nat.card
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup *
        2 ^ Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
        2).ncard := by
  rw [L.natCard_dyadicDoubledAttainedResidueAddSubgroup_eq_index]
  exact
    L.natCard_dyadicDoubledAttainedResidueIndex_mul_two_pow_tangentRank_eq_residueImage_ncard

/-- The shifted dyadic quotient correspondence forces one additional binary
layer beyond the enlarged determinant-loss exponent: the literal finite
identity has exponent `(v₂(pairingDeterminant)+2)*d`. -/
theorem
    dyadicResidueImage_ncard_mul_ordinaryReductionRangeCard_eq_two_pow_add_two_pairingDeterminantVal_mul_quotientCount
    (L : PositiveDefiniteIntegralLattice n) :
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          2).ncard *
        Nat.card
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
            2) =
      2 ^
          ((padicValInt 2 L.pairingDeterminant + 2) *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
        associatedBilinearDualQuotientCount L 2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            2) := by
  let A :=
    Nat.card
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup
  let B :=
    Nat.card
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossQuotient
  let C :=
    2 ^ Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)
  let N :=
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
      2).ncard
  let O :=
    Nat.card
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
        2)
  let Q :=
    associatedBilinearDualQuotientCount L 2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)
  let T :=
    Nat.card
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue
  let d :=
    Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)
  let v := padicValInt 2 L.pairingDeterminant
  have hN : A * C = N := by
    simpa only [A, C, N] using
      L.natCard_dyadicDoubledAttainedResidueAddSubgroup_mul_two_pow_tangentRank_eq_residueImage_ncard
  have hT : A * B = T := by
    simpa only [A, B, T] using
      L.natCard_dyadicDoubledAttainedResidueAddSubgroup_mul_determinantLossQuotient_eq_determinantLossResidue
  have hTpow : T = 2 ^ ((v + 1) * d) := by
    simpa only [T, v, d] using
      L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue
  have hO : O = Q * B := by
    simpa only [O, Q, B] using
      L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_quotientCount_mul_dyadicDeterminantLossQuotient
  have hpow : 2 ^ ((v + 1) * d) * C = 2 ^ ((v + 2) * d) := by
    dsimp only [C]
    calc
      2 ^ ((v + 1) * d) * 2 ^ d =
          2 ^ (((v + 1) * d) + d) := (pow_add 2 _ _).symm
      _ = 2 ^ ((v + 2) * d) := by
        congr 1
        ring
  change N * O = 2 ^ ((v + 2) * d) * Q
  calc
    N * O = (A * C) * (Q * B) := by rw [hN, hO]
    _ = (A * B) * C * Q := by ring
    _ = T * C * Q := by rw [hT]
    _ = (2 ^ ((v + 1) * d) * C) * Q := by rw [hTpow]
    _ = 2 ^ ((v + 2) * d) * Q := by rw [hpow]

end PositiveDefiniteIntegralLattice
