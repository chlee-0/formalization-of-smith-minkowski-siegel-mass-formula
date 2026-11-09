import SMSFormula.SpecialOrthogonalRealIdentityRawDifferentialMass
import SMSFormula.SpecialOrthogonalRealFormCongruenceHaarScalarCancellation

/-!
# Positive-diagonal real differential mass

The raw identity-model Gamma formula is transported through the completed
inverse-square-root congruence from a positive rational diagonal form to the
identity form.  The identity carrier change preserves total mass by direct
`Measure.map_apply`, and the congruence contributes its already computed
reciprocal tangent determinant.

Both the positive-diagonal-to-identity determinant and the arbitrary
fixed-to-elementary identity tangent determinant remain literal.  No
lattice-specific diagonalization, reference-Haar comparison, or Tamagawa
specialization occurs here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

local instance identitySpecialOrthogonalGroupMeasurableSpaceRawMass (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identitySpecialOrthogonalGroupBorelSpaceRawMass (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

local instance identitySpecialOrthogonalMappedGroupMeasurableSpaceRawMass
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ))) :=
  borel _

local instance identitySpecialOrthogonalMappedGroupBorelSpaceRawMass
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The continuous equivalence from the rationally mapped identity group to
the literal real identity group preserves total mass directly. -/
theorem identitySpecialOrthogonalDifferentialMeasure_univ_eq_smooth
    (n : ℕ) :
    identitySpecialOrthogonalDifferentialMeasure n Set.univ =
      specialFormPreservingSmoothRealDifferentialMeasure
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        (by simp) (by simp) Set.univ := by
  have hf : Measurable
      (identitySpecialOrthogonalMappedGroupContinuousEquiv n :
        specialFormPreservingMatrixSubgroup
            ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
              (algebraMap ℚ ℝ)) →
          identitySpecialOrthogonalGroup n) :=
    (identitySpecialOrthogonalMappedGroupContinuousEquiv n).continuous.measurable
  rw [
    identitySpecialOrthogonalDifferentialMeasure,
    Measure.map_apply hf MeasurableSet.univ
  ]
  simp

/-- The positive-diagonal differential mass is the reciprocal diagonal
congruence determinant times the raw identity determinant and Gamma mass. -/
theorem positiveDiagonalSmoothRealDifferentialMeasure_univ_eq_det_mul_gamma
    (n : ℕ) (d : Fin (n + 1) → ℚ) (hd : ∀ i, 0 < d i) :
    specialFormPreservingSmoothRealDifferentialMeasure
        (Matrix.diagonal d)
        (positiveDiagonalForm_isSymm d)
        (positiveDiagonalForm_det_ne_zero d hd) Set.univ =
      (↑((Real.toNNReal
        |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹) : ℝ≥0∞) *
        ((Real.toNNReal
          |(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 1) : ℝ)| : ℝ≥0∞) *
          ENNReal.ofReal
            ((2 : ℝ) ^ n *
                Real.pi ^ ((n : ℝ) * ((n : ℝ) + 3) / 4) /
              (∏ k ∈ Finset.range n,
                Real.Gamma (((k + 2 : ℕ) : ℝ) / 2)))) := by
  rw [
    positiveDiagonalSmoothRealDifferentialMeasure_univ_eq_det,
    ← identitySpecialOrthogonalDifferentialMeasure_univ_eq_smooth n,
    identitySpecialOrthogonalDifferentialMeasure_univ_eq_det_mul_gamma
  ]

/-- Reciprocal positive-diagonal differential mass, written as the inverse
of the complete two-determinant Gamma product. -/
theorem positiveDiagonalSmoothRealDifferentialMeasure_univ_inv_eq
    (n : ℕ) (d : Fin (n + 1) → ℚ) (hd : ∀ i, 0 < d i) :
    (specialFormPreservingSmoothRealDifferentialMeasure
        (Matrix.diagonal d)
        (positiveDiagonalForm_isSymm d)
        (positiveDiagonalForm_det_ne_zero d hd) Set.univ)⁻¹ =
      ((↑((Real.toNNReal
          |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹) : ℝ≥0∞) *
        ((Real.toNNReal
          |(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 1) : ℝ)| : ℝ≥0∞) *
          ENNReal.ofReal
            ((2 : ℝ) ^ n *
                Real.pi ^ ((n : ℝ) * ((n : ℝ) + 3) / 4) /
              (∏ k ∈ Finset.range n,
                Real.Gamma (((k + 2 : ℕ) : ℝ) / 2)))))⁻¹ := by
  rw [positiveDiagonalSmoothRealDifferentialMeasure_univ_eq_det_mul_gamma]

end PositiveDefiniteIntegralLattice
