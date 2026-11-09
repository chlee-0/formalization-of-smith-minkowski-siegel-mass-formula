import SMSFormula.PadicSpecialOrthogonalDifferentialStabilizerVolumeFiberExcess

/-!
# Intrinsic coordinate mass of the density-adapted Cayley kernel

The corrected Cayley density is constant on the density-adapted inverse source.
This module therefore computes its differential mass directly as that constant
times the ambient coordinate-Haar mass of the kernel.  The proof uses
the exact source subtype and its coordinate-measure comap, without choosing a
coordinate-ball partition.

A separate theorem uses the common-level partition and identifies
its numerical ball factor with this intrinsic ambient coordinate mass.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped BigOperators ENNReal Matrix Matrix.Norms.Operator NNReal Pointwise
  Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialDensityCongruenceIntrinsicCoordinateMassSourceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialDensityCongruenceIntrinsicCoordinateMassSourceBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The corrected differential mass of the density-adapted inverse-Cayley
kernel is intrinsically its constant zero-coordinate density times the
ambient coordinate-Haar mass of that kernel. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet_eq_zeroDensity_mul_coordinateMeasure
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
        p n L.rationalFormMatrix
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
          p) =
      (‖(2 : ℚ_[p])‖₊ ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra
            L.rationalFormMatrix) : ℝ≥0∞) *
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
            p) := by
  let C :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
      p
  let S := skewAdjointPadicCayleySource L.rationalFormMatrix p
  let density : S → ENNReal :=
    skewAdjointPadicCayleySourceDifferentialDensityENNReal
      p n L.rationalFormMatrix
  let zeroDensity : ENNReal :=
    (‖(2 : ℚ_[p])‖₊ ^
      Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) : ℝ≥0∞)
  have hsourceMeasurable :
      MeasurableSet
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
          p) :=
    L.measurableSet_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
      p
  have himage :
      Subtype.val ''
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
            p =
        C := by
    rfl
  rw [skewAdjointPadicCayleySourceDifferentialSubtypeMeasure,
    withDensity_apply _ hsourceMeasurable]
  calc
    (∫⁻ X in
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
            p,
        density X
        ∂skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
          p n L.rationalFormMatrix) =
        ∫⁻ _ in
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
              p,
          zeroDensity
          ∂skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
            p n L.rationalFormMatrix := by
      apply setLIntegral_congr_fun hsourceMeasurable
      intro X hX
      exact
        L.skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_zero_value_on_densityCongruenceSourceSet
          p X hX
    _ = zeroDensity *
        skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
          p n L.rationalFormMatrix
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
            p) :=
      setLIntegral_const _ _
    _ = zeroDensity *
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p C := by
      rw [skewAdjointPadicCayleySourceCoordinateSubtypeMeasure,
        comap_subtype_coe_apply
          (isOpen_skewAdjointPadicCayleySource
            L.rationalFormMatrix p).measurableSet,
        himage]

/-- The common-level ball factor in the existing finite partition is exactly
the intrinsic ambient coordinate-Haar mass of the density-adapted kernel. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialDensityCongruenceSource_coordinateMeasure_commonBall
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
          skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
                p) =
            (balls.card : ℝ≥0∞) *
              ((p : ℝ≥0∞) ^
                (level * Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹ := by
  obtain
      ⟨level, balls, center, hcenter, hpairwise, hcover, _hsourceMass⟩ :=
    L.exists_localPadicSpecialOrthogonalDifferentialDensityCongruenceSource_finite_mass_commonBall
      p
  refine
    ⟨level, balls, center, hcenter, hpairwise, hcover, ?_⟩
  have hmeasurable : ∀ B ∈ balls, MeasurableSet B := by
    intro B hB
    rw [hcenter B hB]
    exact
      (isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
        L.rationalFormMatrix p level (center B)).1.measurableSet
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

end PositiveDefiniteIntegralLattice
