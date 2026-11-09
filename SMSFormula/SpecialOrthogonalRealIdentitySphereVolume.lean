import SMSFormula.SpecialOrthogonalRealFormCongruenceHaarScalarCancellation
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The Euclidean sphere factor in the identity-model real volume

This module evaluates the standard additive-Haar-induced measure on the unit
sphere. The factor occurring in the target special-orthogonal volume
recurrence is exactly half of this sphere measure. No group quotient or
disintegration statement is asserted here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

/-- The Gamma factor expected in one identity-model special-orthogonal rank
step. Its relation to the differential group measure requires a separate
internally normalized quotient/disintegration theorem. -/
def identitySpecialOrthogonalSphereStep (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2))

/-- The additive-Haar-induced Euclidean unit-sphere measure has the classical
Gamma value. -/
theorem euclideanVolumeToSphere_univ
    (n : ℕ) (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ =
      ENNReal.ofReal
        (2 * Real.pi ^ ((n : ℝ) / 2) /
          Real.Gamma ((n : ℝ) / 2)) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [Measure.toSphere_apply_univ, EuclideanSpace.volume_ball]
  simp only [finrank_euclideanSpace, Fintype.card_fin,
    ENNReal.ofReal_one, one_pow, one_mul]
  rw [Real.Gamma_add_one (by positivity)]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul]
  · congr 1
    have hsqrt :
        √Real.pi ^ n = Real.pi ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_natCast]
      exact
        (Real.rpow_div_two_eq_sqrt
          (n : ℝ) Real.pi_nonneg).symm
    rw [hsqrt]
    field_simp
  · positivity

/-- The full Euclidean sphere measure is twice the factor required by the
target identity-model special-orthogonal product. -/
theorem euclideanVolumeToSphere_univ_eq_two_mul_identitySpecialOrthogonalSphereStep
    (n : ℕ) (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ =
      2 * identitySpecialOrthogonalSphereStep n := by
  rw [euclideanVolumeToSphere_univ n hn,
    identitySpecialOrthogonalSphereStep, ← ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The identity-model sphere step is positive in every positive rank. -/
theorem identitySpecialOrthogonalSphereStep_pos
    (n : ℕ) (hn : 0 < n) :
    0 < identitySpecialOrthogonalSphereStep n := by
  rw [identitySpecialOrthogonalSphereStep, ENNReal.ofReal_pos]
  exact div_pos
    (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by positivity))

/-- The identity-model sphere step is nonzero in every positive rank. -/
theorem identitySpecialOrthogonalSphereStep_ne_zero
    (n : ℕ) (hn : 0 < n) :
    identitySpecialOrthogonalSphereStep n ≠ 0 :=
  ne_of_gt (identitySpecialOrthogonalSphereStep_pos n hn)

/-- The identity-model sphere step is always finite. -/
theorem identitySpecialOrthogonalSphereStep_ne_top (n : ℕ) :
    identitySpecialOrthogonalSphereStep n ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The target rank step is exactly half of the additive-Haar-induced unit
sphere measure. -/
theorem identitySpecialOrthogonalSphereStep_eq_inv_two_mul_toSphere
    (n : ℕ) (hn : 0 < n) :
    identitySpecialOrthogonalSphereStep n =
      (2 : ℝ≥0∞)⁻¹ *
        (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ := by
  rw [
    euclideanVolumeToSphere_univ_eq_two_mul_identitySpecialOrthogonalSphereStep
      n hn]
  rw [← mul_assoc, ENNReal.inv_mul_cancel]
  · simp
  · norm_num
  · norm_num

end PositiveDefiniteIntegralLattice
