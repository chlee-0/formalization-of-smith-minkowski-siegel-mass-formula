import SMSFormula.SpecialOrthogonalRealCongruenceHaarScalarCancellation
import SMSFormula.SpecialOrthogonalRealFormCongruenceHaarScalarSelectedMass

/-!
# Finite-positive cancellation for explicit real form congruence
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Opaque explicit-real cancellation data assembled from the selected mass
identities. -/
def specialFormPreservingRealFormCongruenceHaarScalarCancellationCertificate
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    ENNRealFinitePositiveCancellationCertificate
      (specialFormPreservingRealFormCongruenceHaarScalar
        F F' hF hdet hF' hdet' c)
      (↑((Real.toNNReal |c.detScalar|)⁻¹) : ℝ≥0∞) where
  mass :=
    specialFormPreservingRealFormCongruenceFiniteCommonMass
      F F' hF hdet hF' hdet' c
  mass_ne_zero :=
    specialFormPreservingRealFormCongruenceFiniteCommonMass_ne_zero
      F F' hF hdet hF' hdet' c
  mass_ne_top :=
    specialFormPreservingRealFormCongruenceFiniteCommonMass_ne_top
      F F' hF hdet hF' hdet' c
  mul_mass_eq := by
    calc
      specialFormPreservingRealFormCongruenceHaarScalar
            F F' hF hdet hF' hdet' c *
          specialFormPreservingRealFormCongruenceFiniteCommonMass
            F F' hF hdet hF' hdet' c =
        specialFormPreservingRealFormCongruenceFiniteTransportedGlobalMass
          F F' hF hdet hF' hdet' c :=
        (specialFormPreservingRealFormCongruenceFiniteTransportedGlobalMass_eq_smul
          F F' hF hdet hF' hdet' c).symm
      _ =
        specialFormPreservingRealFormCongruenceFiniteTransportedOverlapMass
          F F' hF hdet hF' hdet' c :=
        (specialFormPreservingRealFormCongruenceFiniteTransportedOverlapMass_eq
          F F' hF hdet hF' hdet' c).symm
      _ =
        (↑((Real.toNNReal |c.detScalar|)⁻¹) : ℝ≥0∞) *
          specialFormPreservingRealFormCongruenceFiniteStandardOverlapMass
            F F' hF hdet hF' hdet' c :=
        specialFormPreservingRealFormCongruenceFiniteTransportedOverlapMass_eq_smul
          F F' hF hdet hF' hdet' c
      _ =
        (↑((Real.toNNReal |c.detScalar|)⁻¹) : ℝ≥0∞) *
          specialFormPreservingRealFormCongruenceFiniteCommonMass
            F F' hF hdet hF' hdet' c := by
        rw [specialFormPreservingRealFormCongruenceFiniteStandardOverlapMass_eq]

/-- The global explicit-real congruence Haar scalar is the reciprocal absolute
tangent basis-comparison determinant. -/
theorem specialFormPreservingRealFormCongruenceHaarScalar_eq
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingRealFormCongruenceHaarScalar
        F F' hF hdet hF' hdet' c =
      (↑((Real.toNNReal |c.detScalar|)⁻¹) : ℝ≥0∞) :=
  (specialFormPreservingRealFormCongruenceHaarScalarCancellationCertificate
    F F' hF hdet hF' hdet' c).eq

/-- The positive-diagonal-to-identity Haar scalar is the reciprocal tangent
basis-comparison determinant. -/
theorem positiveDiagonalRealFormCongruenceHaarScalar_eq
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    positiveDiagonalRealFormCongruenceHaarScalar d hd =
      (↑((Real.toNNReal
        |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹) : ℝ≥0∞) := by
  simpa only [positiveDiagonalRealFormCongruenceHaarScalar,
    positiveDiagonalRealFormCongruenceData_detScalar] using
    specialFormPreservingRealFormCongruenceHaarScalar_eq
      (Matrix.diagonal d) 1
      (positiveDiagonalForm_isSymm d)
      (positiveDiagonalForm_det_ne_zero d hd)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero
      (positiveDiagonalRealFormCongruenceData d hd)

/-- The positive-diagonal differential total mass is the reciprocal tangent
determinant times the identity-model differential total mass. -/
theorem positiveDiagonalSmoothRealDifferentialMeasure_univ_eq_det
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    specialFormPreservingSmoothRealDifferentialMeasure
        (Matrix.diagonal d)
        (positiveDiagonalForm_isSymm d)
        (positiveDiagonalForm_det_ne_zero d hd) Set.univ =
      (↑((Real.toNNReal
        |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹) : ℝ≥0∞) *
        specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero Set.univ := by
  rw [positiveDiagonalSmoothRealDifferentialMeasure_univ,
    positiveDiagonalRealFormCongruenceHaarScalar_eq]

end PositiveDefiniteIntegralLattice
