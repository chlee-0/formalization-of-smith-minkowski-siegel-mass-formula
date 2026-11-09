import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceIntrinsicCoordinateMass

/-!
# Intrinsic coordinate form of the corrected special-stabilizer volume

An earlier theorem expresses the corrected special-stabilizer volume through
the cardinality and common level of a finite coordinate-ball partition.  This
module uses the cover and disjointness from that theorem to replace the
partition-dependent factor by the coordinate-Haar mass of the
density-adapted inverse-Cayley kernel.

The resulting identity is nonexistential.  Outside the finite
Schulze--Pillot bad-prime set, the vanishing of the fiber excess leaves only
the associated-bilinear quotient count.  No local-density normalization or
bad-prime excess is evaluated here.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped BigOperators ENNReal Matrix Matrix.Norms.Operator NNReal Pointwise
  Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialStabilizerVolumeIntrinsicCoordinateMassSourceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialStabilizerVolumeIntrinsicCoordinateMassSourceBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The balanced corrected special-stabilizer volume, with the finite
coordinate partition replaced by the intrinsic coordinate-Haar mass of the
literal density-adapted inverse-Cayley kernel. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_zeroDensity_mul_coordinateMeasure_mul_quotientCount_add_fiberExcess
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
        (2 : ℝ≥0∞) =
      (‖(2 : ℚ_[p])‖₊ ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra
            L.rationalFormMatrix) : ℝ≥0∞) *
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
            p) *
        ((associatedBilinearDualQuotientCount L p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p) : ℝ≥0∞) +
          (L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess
            p : ℝ≥0∞)) := by
  obtain
      ⟨level, balls, center, hcenter, hpairwise, hcover, hvolume⟩ :=
    L.exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_densityBallCard_mul_quotientCount_add_fiberExcess
      p
  have hmeasurable : ∀ B ∈ balls, MeasurableSet B := by
    intro B hB
    rw [hcenter B hB]
    exact
      (isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
        L.rationalFormMatrix p level (center B)).1.measurableSet
  have hcoordinate :
      skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
            p) =
        (balls.card : ℝ≥0∞) *
          ((p : ℝ≥0∞) ^
            (level * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
    rw [← hcover]
    calc
      skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p
          (⋃ B ∈ balls, B) =
          ∑ B ∈ balls,
            skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p B :=
        measure_biUnion_finset hpairwise hmeasurable
      _ = ∑ _B ∈ balls,
          ((p : ℝ≥0∞) ^
            (level * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
        apply Finset.sum_congr rfl
        intro B hB
        rw [hcenter B hB,
          skewAdjointPadicCoordinateMeasure_translatedUniformCoordinateBall_explicit]
      _ = (balls.card : ℝ≥0∞) *
          ((p : ℝ≥0∞) ^
            (level * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  calc
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
            p : ℝ≥0∞)) :=
      hvolume
    _ =
      (‖(2 : ℚ_[p])‖₊ ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra
            L.rationalFormMatrix) : ℝ≥0∞) *
        ((balls.card : ℝ≥0∞) *
          ((p : ℝ≥0∞) ^
            (level * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹) *
        ((associatedBilinearDualQuotientCount L p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p) : ℝ≥0∞) +
          (L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess
            p : ℝ≥0∞)) := by
      ac_rfl
    _ =
      (‖(2 : ℚ_[p])‖₊ ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra
            L.rationalFormMatrix) : ℝ≥0∞) *
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
            p) *
        ((associatedBilinearDualQuotientCount L p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p) : ℝ≥0∞) +
          (L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess
            p : ℝ≥0∞)) := by
      rw [hcoordinate]

/-- Outside the Schulze--Pillot bad-prime set, the intrinsic balanced
corrected special-stabilizer volume has the selected associated-bilinear
quotient count as its terminal finite factor. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_zeroDensity_mul_coordinateMeasure_mul_quotientCount_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
        (2 : ℝ≥0∞) =
      (‖(2 : ℚ_[q.1])‖₊ ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra
            L.rationalFormMatrix) : ℝ≥0∞) *
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
            q.1) *
        (associatedBilinearDualQuotientCount L q.1
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            q.1) : ℝ≥0∞) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_zeroDensity_mul_coordinateMeasure_mul_quotientCount_add_fiberExcess
      q.1,
    L.localPadicSpecialOrthogonalDifferentialDensityFiberExcess_eq_zero_of_not_mem_massBadPrimeSet
      q hq]
  simp

end PositiveDefiniteIntegralLattice
