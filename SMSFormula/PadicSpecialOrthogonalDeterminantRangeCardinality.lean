import SMSFormula.PadicSpecialOrthogonalDifferentialSignSeparatedDensityDepth

/-!
# Finite determinant kernel/image cardinality

The determinant-one part of the ordinary integral-stabilizer reduction image
is the kernel of its finite determinant character.  The finite first
isomorphism theorem therefore factors the ordinary reduction-range
cardinality as the determinant-one kernel cardinal times the cardinality of
the actual determinant-character image.

The determinant-image cardinal remains literal.  In particular, no
index-two assertion is made.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix Matrix.Norms.Operator NNReal Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The ordinary finite stabilizer reduction range factors into the
determinant-one kernel and the actual determinant-character image. -/
theorem
    natCard_localPadicLatticeStabilizerReduction_range_eq_special_mul_determinantRange
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (L.localPadicLatticeStabilizerReduction p k).range =
      Nat.card
          (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
            p k) *
        Nat.card
          (L.localPadicLatticeStabilizerReductionRangeDeterminant p k).range := by
  let G := (L.localPadicLatticeStabilizerReduction p k).range
  let detHom := L.localPadicLatticeStabilizerReductionRangeDeterminant p k
  have hquotient :
      Nat.card (G ⧸ detHom.ker) = Nat.card detHom.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange detHom).toEquiv
  calc
    Nat.card G =
        Nat.card (G ⧸ detHom.ker) * Nat.card detHom.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup detHom.ker
    _ = Nat.card detHom.range * Nat.card detHom.ker := by
      rw [hquotient]
    _ = Nat.card detHom.ker * Nat.card detHom.range := Nat.mul_comm _ _
    _ =
        Nat.card
            (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
              p k) *
          Nat.card
            (L.localPadicLatticeStabilizerReductionRangeDeterminant p k).range := by
      rfl

/-- The same kernel/image cardinal factorization at the selected corrected
density-adapted depth. -/
theorem
    natCard_localPadicLatticeStabilizerReduction_densityCongruenceRange_eq_special_mul_determinantRange
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card
        (L.localPadicLatticeStabilizerReduction
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            p)).range =
      Nat.card
          (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p)) *
        Nat.card
          (L.localPadicLatticeStabilizerReductionRangeDeterminant
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p)).range :=
  L.natCard_localPadicLatticeStabilizerReduction_range_eq_special_mul_determinantRange
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)

/-- Multiplying the corrected special-stabilizer volume by the
determinant-image cardinal replaces the determinant-one reduction factor by
the ordinary stabilizer reduction-range cardinal. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_determinantRangeCard_eq_densityBallCard_mul_ordinaryReductionRangeCard
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ level : ℕ,
      ∃ balls : Finset (Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule),
        ∃ center :
            Set (skewAdjointMatricesLieSubalgebra
                (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
                p,
          (∀ B ∈ balls,
            B = skewAdjointPadicTranslatedUniformCoordinateBall
              L.rationalFormMatrix p level (center B)) ∧
          (↑balls : Set (Set (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map
              (algebraMap ℚ ℚ_[p]))).toSubmodule)).PairwiseDisjoint id ∧
          (⋃ B ∈ balls, B) =
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              p ∧
          L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
              (Nat.card
                (L.localPadicLatticeStabilizerReductionRangeDeterminant
                  p
                  (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                    p)).range : ℝ≥0∞) =
            (‖(2 : ℚ_[p])‖₊ ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra
                  L.rationalFormMatrix) : ℝ≥0∞) *
              (balls.card : ℝ≥0∞) *
              ((p : ℝ≥0∞) ^
                (level * Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹ *
              (Nat.card
                (L.localPadicLatticeStabilizerReduction
                  p
                  (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                    p)).range : ℝ≥0∞) := by
  obtain
      ⟨level, balls, center, hcenter, hpairwise, hcover, hvolume⟩ :=
    L.exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_densityBallCard_mul_specialReductionRangeCard
      p
  refine
    ⟨level, balls, center, hcenter, hpairwise, hcover, ?_⟩
  have hcard :=
    L.natCard_localPadicLatticeStabilizerReduction_densityCongruenceRange_eq_special_mul_determinantRange
      p
  have hcardENN :
      (Nat.card
          (L.localPadicLatticeStabilizerReduction
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p)).range : ℝ≥0∞) =
        (Nat.card
            (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p)) : ℝ≥0∞) *
          (Nat.card
            (L.localPadicLatticeStabilizerReductionRangeDeterminant
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p)).range : ℝ≥0∞) := by
    exact_mod_cast hcard
  calc
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
          (Nat.card
            (L.localPadicLatticeStabilizerReductionRangeDeterminant
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p)).range : ℝ≥0∞) =
        ((‖(2 : ℚ_[p])‖₊ ^
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix) : ℝ≥0∞) *
          (balls.card : ℝ≥0∞) *
          ((p : ℝ≥0∞) ^
            (level * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ *
          (Nat.card
            (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p)) : ℝ≥0∞)) *
          (Nat.card
            (L.localPadicLatticeStabilizerReductionRangeDeterminant
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p)).range : ℝ≥0∞) := by
      rw [hvolume]
    _ =
        (‖(2 : ℚ_[p])‖₊ ^
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix) : ℝ≥0∞) *
          (balls.card : ℝ≥0∞) *
          ((p : ℝ≥0∞) ^
            (level * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ *
          ((Nat.card
              (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
                p
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                  p)) : ℝ≥0∞) *
            (Nat.card
              (L.localPadicLatticeStabilizerReductionRangeDeterminant
                p
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                  p)).range : ℝ≥0∞)) := by
      rw [mul_assoc]
    _ =
        (‖(2 : ℚ_[p])‖₊ ^
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix) : ℝ≥0∞) *
          (balls.card : ℝ≥0∞) *
          ((p : ℝ≥0∞) ^
            (level * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ *
          (Nat.card
            (L.localPadicLatticeStabilizerReduction
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p)).range : ℝ≥0∞) := by
      rw [← hcardENN]

end PositiveDefiniteIntegralLattice
