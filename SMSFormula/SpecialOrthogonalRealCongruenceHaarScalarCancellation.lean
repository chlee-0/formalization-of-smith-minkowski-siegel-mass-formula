import SMSFormula.SpecialOrthogonalRealCongruenceHaarScalarSelectedMass

/-!
# Finite-positive cancellation of the real congruence Haar scalar
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The fixed-type data needed to cancel one finite positive `ENNReal` mass. -/
structure ENNRealFinitePositiveCancellationCertificate
    (left right : ℝ≥0∞) where
  mass : ℝ≥0∞
  mass_ne_zero : mass ≠ 0
  mass_ne_top : mass ≠ ⊤
  mul_mass_eq : left * mass = right * mass

/-- A finite positive common factor cancels in `ENNReal`. -/
theorem ENNRealFinitePositiveCancellationCertificate.eq
    {left right : ℝ≥0∞}
    (c : ENNRealFinitePositiveCancellationCertificate left right) :
    left = right := by
  calc
    left = left * 1 := (mul_one left).symm
    _ = left * (c.mass * c.mass⁻¹) := by
      rw [ENNReal.mul_inv_cancel c.mass_ne_zero c.mass_ne_top]
    _ = (left * c.mass) * c.mass⁻¹ := by rw [mul_assoc]
    _ = (right * c.mass) * c.mass⁻¹ := by rw [c.mul_mass_eq]
    _ = right * (c.mass * c.mass⁻¹) := by rw [mul_assoc]
    _ = right * 1 := by
      rw [ENNReal.mul_inv_cancel c.mass_ne_zero c.mass_ne_top]
    _ = right := mul_one right

/-- Opaque form-specific cancellation data assembled from the selected mass
identities. -/
def specialFormPreservingRealCongruenceHaarScalarCancellationCertificate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    ENNRealFinitePositiveCancellationCertificate
      (specialFormPreservingRealCongruenceHaarScalar F hF hdet W)
      ((↑((Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹) : ℝ≥0∞)) where
  mass := specialFormPreservingRealCongruenceFiniteCommonMass F hF hdet W
  mass_ne_zero :=
    specialFormPreservingRealCongruenceFiniteCommonMass_ne_zero F hF hdet W
  mass_ne_top :=
    specialFormPreservingRealCongruenceFiniteCommonMass_ne_top F hF hdet W
  mul_mass_eq := by
    calc
      specialFormPreservingRealCongruenceHaarScalar F hF hdet W *
          specialFormPreservingRealCongruenceFiniteCommonMass F hF hdet W =
        specialFormPreservingRealCongruenceFiniteTransportedGlobalMass
          F hF hdet W :=
        (specialFormPreservingRealCongruenceFiniteTransportedGlobalMass_eq_smul
          F hF hdet W).symm
      _ = specialFormPreservingRealCongruenceFiniteTransportedOverlapMass
          F hF hdet W :=
        (specialFormPreservingRealCongruenceFiniteTransportedOverlapMass_eq
          F hF hdet W).symm
      _ = (↑((Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹) : ℝ≥0∞) *
          specialFormPreservingRealCongruenceFiniteStandardOverlapMass
            F hF hdet W :=
        specialFormPreservingRealCongruenceFiniteTransportedOverlapMass_eq_smul
          F hF hdet W
      _ = (↑((Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹) : ℝ≥0∞) *
          specialFormPreservingRealCongruenceFiniteCommonMass F hF hdet W := by
        rw [specialFormPreservingRealCongruenceFiniteStandardOverlapMass_eq]

/-- The global real congruence Haar scalar is exactly the reciprocal absolute
tangent basis-comparison determinant. -/
theorem specialFormPreservingRealCongruenceHaarScalar_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingRealCongruenceHaarScalar F hF hdet W =
      (↑((Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹) : ℝ≥0∞) :=
  (specialFormPreservingRealCongruenceHaarScalarCancellationCertificate
    F hF hdet W).eq

end PositiveDefiniteIntegralLattice
