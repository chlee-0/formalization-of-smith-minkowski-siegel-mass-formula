import SMSFormula.PadicSpecialOrthogonalDifferentialStabilizerVolumeExtraction
import SMSFormula.PadicSpecialOrthogonalReductionSurjectivity

/-!
# Sign separation at the corrected density-adapted depth

The density-adapted principal-congruence depth is selected at least two.
Every prime power at such a depth distinguishes `1` from `-1`.  The
sign-separated special-reduction theorem therefore identifies the literal
direct reduction range used in the corrected stabilizer-volume formula with
the full determinant-one subgroup of the ordinary stabilizer reduction image.

No index comparison with the ordinary reduction range is made.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix Matrix.Norms.Operator NNReal Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A prime-power residue ring at depth at least two distinguishes `1` and
`-1`. -/
theorem neg_one_ne_one_zmod_prime_pow_of_two_le
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 2 ≤ k) :
    (-1 : ZMod (p ^ k)) ≠ 1 := by
  intro hsign
  have htwo : (2 : ZMod (p ^ k)) = 0 := by
    calc
      (2 : ZMod (p ^ k)) = 1 - (-1) := by ring
      _ = 0 := by rw [hsign]; simp
  have hdvd : p ^ k ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 (p ^ k)).mp htwo
  have hupper : p ^ k ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hdvd
  have hlower : 4 ≤ p ^ k := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 :=
        Nat.pow_le_pow_left ((Fact.out : Nat.Prime p).two_le) 2
      _ ≤ p ^ k :=
        Nat.pow_le_pow_right ((Fact.out : Nat.Prime p).pos) hk
  omega

/-- The selected corrected density-adapted depth distinguishes the two
residue signs. -/
theorem
    neg_one_ne_one_zmod_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (-1 :
      ZMod
        (p ^
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)) ≠
      1 :=
  neg_one_ne_one_zmod_prime_pow_of_two_le p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)

/-- At the selected density-adapted depth, the literal direct reduction range
has the cardinality of the full determinant-one subgroup of the ordinary
stabilizer reduction image. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceReduction_range_eq
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            p)).range =
      Nat.card
        (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            p)) :=
  L.natCard_localPadicSpecialOrthogonalDifferentialStabilizerReduction_range_eq
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.neg_one_ne_one_zmod_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p)

/-- The corrected differential stabilizer volume with the finite factor
expressed as the full determinant-one subgroup of the ordinary stabilizer
reduction image at the selected sign-separated depth. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_densityBallCard_mul_specialReductionRangeCard
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
          L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p =
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
                (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
                  p
                  (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                    p)) : ℝ≥0∞) := by
  obtain
      ⟨level, balls, center, hcenter, hpairwise, hcover, hvolume⟩ :=
    L.exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_densityBallCard_mul_reductionRangeCard
      p
  refine
    ⟨level, balls, center, hcenter, hpairwise, hcover, ?_⟩
  calc
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p =
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
            (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p)).range : ℝ≥0∞) :=
      hvolume
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
            (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p)) : ℝ≥0∞) := by
      rw [
        L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceReduction_range_eq
          p]

end PositiveDefiniteIntegralLattice
