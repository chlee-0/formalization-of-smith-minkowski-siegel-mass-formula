import SMSFormula.PadicSpecialOrthogonalDeterminantImageDichotomy

/-!
# Realizing the p-adic orientation character in positive rank

The existing integral reflection certificate gives an element of the
integral p-adic lattice stabilizer whose determinant is `-1` in every positive
rank, including at the dyadic prime.  The intrinsic determinant-image
dichotomy therefore has its two-element branch, and the balanced corrected
special-stabilizer volume carries the literal orientation factor `2`.

No finite local-density comparison is made here.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix Matrix.Norms.Operator NNReal Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- In positive rank, an integral p-adic lattice stabilizer element realizes
determinant `-1`. -/
theorem exists_localPadicLatticeStabilizerDeterminant_eq_neg_one
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ g : L.localPadicLatticeStabilizerSubgroup p,
      L.localPadicLatticeStabilizerDeterminant p g = -1 := by
  obtain ⟨d⟩ := localPadicIntegralReflectionData_nonempty L p
  exact ⟨d.stabilizer, d.stabilizer_determinant⟩

/-- In positive rank, the intrinsic integral p-adic determinant image has
exactly the two signs. -/
theorem natCard_localPadicLatticeStabilizerDeterminant_range_eq_two
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (L.localPadicLatticeStabilizerDeterminant p).range = 2 :=
  (L.natCard_localPadicLatticeStabilizerDeterminant_range_eq_two_iff_exists_det_neg_one
    p).2
    (L.exists_localPadicLatticeStabilizerDeterminant_eq_neg_one p)

/-- In positive rank, the balanced corrected special-stabilizer volume has
the literal orientation factor `2`. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_densityBallCard_mul_ordinaryReductionRangeCard
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] :
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
              (2 : ℝ≥0∞) =
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
    L.exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_integralDeterminantRangeCard_eq_densityBallCard_mul_ordinaryReductionRangeCard
      p
  refine
    ⟨level, balls, center, hcenter, hpairwise, hcover, ?_⟩
  rw [L.natCard_localPadicLatticeStabilizerDeterminant_range_eq_two p] at hvolume
  exact hvolume

end PositiveDefiniteIntegralLattice
