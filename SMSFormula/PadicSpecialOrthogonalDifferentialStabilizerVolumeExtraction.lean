import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceCoordinateMass

/-!
# Extracting the corrected p-adic special stabilizer volume

The density-adapted inverse-Cayley source has two independently established
mass descriptions.  Finite-index Haar algebra expresses it as the corrected
special-stabilizer volume times the inverse cardinality of the actual finite
reduction image.  Fixed transported coordinates express it as the
zero-coordinate Cayley density times the number and common mass of a finite
common-level coordinate-ball partition.

The actual reduction range is a nonempty finite type.  Cancelling only its
finite nonzero `ENNReal` cardinal gives an explicit stabilizer-volume formula
while retaining both literal finite cardinalities.  No raw congruence-solution
set or normalized reference Haar measure is used.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped ENNReal Matrix Matrix.Norms.Operator NNReal Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The corrected differential volume of the integral special stabilizer is
the density-adapted coordinate-kernel mass multiplied by the cardinality of
the finite reduction image.

The selected common level, finite coordinate-ball family, and its centers appear
explicitly.  Neither finite cardinality is identified with a raw
solution set. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_densityBallCard_mul_reductionRangeCard
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
                (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction
                  p
                  (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                    p)).range : ℝ≥0∞) := by
  obtain
      ⟨level, balls, center, hcenter, hpairwise, hcover, hcoordinate⟩ :=
    L.exists_localPadicSpecialOrthogonalDifferentialDensityCongruenceSource_finite_mass_commonBall
      p
  refine
    ⟨level, balls, center, hcenter, hpairwise, hcover, ?_⟩
  let reduction :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerReduction
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  let c : ENNReal := (Nat.card reduction.range : ℝ≥0∞)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (Nat.card_pos : 0 < Nat.card reduction.range).ne'
  have hctop : c ≠ ⊤ := by
    dsimp only [c]
    exact ENNReal.natCast_ne_top _
  have hfiniteIndex :=
    L.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet_eq_volume_mul_inv_natCard_range
      p
  have hvolumeInv_eq_coordinate :
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p * c⁻¹ =
        (‖(2 : ℚ_[p])‖₊ ^
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra
              L.rationalFormMatrix) : ℝ≥0∞) *
          (balls.card : ℝ≥0∞) *
          ((p : ℝ≥0∞) ^
            (level * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
    calc
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p * c⁻¹ =
          skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
            p n L.rationalFormMatrix
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
              p) := by
        simpa only [c, reduction] using hfiniteIndex.symm
      _ =
          (‖(2 : ℚ_[p])‖₊ ^
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix) : ℝ≥0∞) *
            (balls.card : ℝ≥0∞) *
            ((p : ℝ≥0∞) ^
              (level * Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra
                  L.rationalFormMatrix)))⁻¹ :=
        hcoordinate
  calc
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p =
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p * 1 := by
      rw [mul_one]
    _ =
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
          (c⁻¹ * c) := by
      rw [ENNReal.inv_mul_cancel hc hctop]
    _ =
        (L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p * c⁻¹) *
          c := by
      rw [mul_assoc]
    _ =
        ((‖(2 : ℚ_[p])‖₊ ^
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix) : ℝ≥0∞) *
          (balls.card : ℝ≥0∞) *
          ((p : ℝ≥0∞) ^
            (level * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹) *
          c := by
      rw [hvolumeInv_eq_coordinate]
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
            (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p)).range : ℝ≥0∞) := by
      rfl

end PositiveDefiniteIntegralLattice
