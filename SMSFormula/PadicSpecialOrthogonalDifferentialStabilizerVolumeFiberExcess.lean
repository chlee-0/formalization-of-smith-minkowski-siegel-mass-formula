import SMSFormula.PadicSpecialOrthogonalDifferentialDensityFiberExcess
import SMSFormula.PadicSpecialOrthogonalDeterminantImagePositiveRank

/-!
# The corrected stabilizer volume with its finite fiber excess

This module rewrites only the terminal finite reduction-range cardinal in the
internally constructed corrected special-stabilizer volume.  The coordinate
level, finite ball family, centers, disjointness, and cover are unchanged.

At every prime the terminal factor is the associated-bilinear quotient count
plus the selected fiber excess.  Outside the finite Schulze--Pillot bad-prime
set the excess vanishes, leaving the quotient count alone.  No coordinate
normalization or bad-prime excess is evaluated here.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix Matrix.Norms.Operator NNReal Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The balanced corrected special-stabilizer volume with the ordinary
reduction cardinal split into quotient count plus selected fiber excess. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_densityBallCard_mul_quotientCount_add_fiberExcess
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
              ((associatedBilinearDualQuotientCount L p
                  (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                    p) : ℝ≥0∞) +
                (L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess
                  p : ℝ≥0∞)) := by
  obtain
      ⟨level, balls, center, hcenter, hpairwise, hcover, hvolume⟩ :=
    L.exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_densityBallCard_mul_ordinaryReductionRangeCard
      p
  refine
    ⟨level, balls, center, hcenter, hpairwise, hcover, ?_⟩
  rw [
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange_eq_associatedBilinearDualQuotientCount_add_fiberExcess
      p] at hvolume
  simpa only [Nat.cast_add] using hvolume

/-- Outside the Schulze--Pillot bad-prime set, the balanced corrected
special-stabilizer volume has the selected associated-bilinear quotient count
as its terminal finite factor. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_densityBallCard_mul_quotientCount_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    ∃ level : ℕ,
      ∃ balls : Finset (Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))).toSubmodule),
        ∃ center :
            Set (skewAdjointMatricesLieSubalgebra
                (L.rationalFormMatrix.map
                  (algebraMap ℚ ℚ_[q.1]))).toSubmodule →
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
                q.1,
          (∀ B ∈ balls,
            B = skewAdjointPadicTranslatedUniformCoordinateBall
              L.rationalFormMatrix q.1 level (center B)) ∧
          (↑balls : Set (Set (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map
              (algebraMap ℚ ℚ_[q.1]))).toSubmodule)).PairwiseDisjoint id ∧
          (⋃ B ∈ balls, B) =
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              q.1 ∧
          L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
              (2 : ℝ≥0∞) =
            (‖(2 : ℚ_[q.1])‖₊ ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra
                  L.rationalFormMatrix) : ℝ≥0∞) *
              (balls.card : ℝ≥0∞) *
              ((q.1 : ℝ≥0∞) ^
                (level * Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹ *
              (associatedBilinearDualQuotientCount L q.1
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                  q.1) : ℝ≥0∞) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  obtain
      ⟨level, balls, center, hcenter, hpairwise, hcover, hvolume⟩ :=
    L.exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_densityBallCard_mul_quotientCount_add_fiberExcess
      q.1
  refine
    ⟨level, balls, center, hcenter, hpairwise, hcover, ?_⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess_eq_zero_of_not_mem_massBadPrimeSet
      q hq] at hvolume
  simpa using hvolume

end PositiveDefiniteIntegralLattice
