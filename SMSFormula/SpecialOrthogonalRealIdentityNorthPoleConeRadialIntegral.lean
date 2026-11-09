import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleConeProductVolume
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Radial integral for the identity north-pole cone

This module evaluates the one-dimensional radial factor isolated by the
north-pole cone change of variables.  It does not transport the resulting
identity to the sphere-coordinate measure.
-/

open scoped ENNReal
noncomputable section

open MeasureTheory Set

namespace PositiveDefiniteIntegralLattice

def identitySpecialOrthogonalNorthPoleConeRadialMeasure (n : ℕ) :
    Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioo 0 1)).withDensity
    fun r => ENNReal.ofReal (r ^ n)

theorem identitySpecialOrthogonalNorthPoleConeRadialMeasure_univ
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ =
      ENNReal.ofReal ((n + 1 : ℝ)⁻¹) := by
  rw [identitySpecialOrthogonalNorthPoleConeRadialMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal
      (intervalIntegral.intervalIntegrable_pow n).1,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  · simp [div_eq_mul_inv]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact pow_nonneg hr.1.le n

theorem identitySpecialOrthogonalNorthPoleConeRadialMeasure_univ_pos
    (n : ℕ) :
    0 < identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ := by
  rw [identitySpecialOrthogonalNorthPoleConeRadialMeasure_univ,
    ENNReal.ofReal_pos]
  positivity

theorem identitySpecialOrthogonalNorthPoleConeRadialMeasure_univ_lt_top
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ < ⊤ := by
  rw [identitySpecialOrthogonalNorthPoleConeRadialMeasure_univ]
  exact ENNReal.ofReal_lt_top

theorem identitySpecialOrthogonalNorthPoleConeRadialMeasure_ne_zero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleConeRadialMeasure n ≠ 0 := by
  intro h
  have hpos :=
    identitySpecialOrthogonalNorthPoleConeRadialMeasure_univ_pos n
  rw [h] at hpos
  simp at hpos

theorem
    identitySpecialOrthogonalNorthPoleConeRadialMeasure_finrankFactor
    (n : ℕ) :
    (n + 1 : ℝ≥0∞) *
      identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ = 1 := by
  rw [identitySpecialOrthogonalNorthPoleConeRadialMeasure_univ]
  rw [show ((n + 1 : ℝ)⁻¹) = ((n + 1 : ℝ) : ℝ)⁻¹ by rfl,
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < n + 1)]
  have hcast :
      ENNReal.ofReal ((n : ℝ) + 1) = (n + 1 : ℝ≥0∞) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ENNReal.ofReal_natCast (n + 1)
  rw [hcast]
  exact ENNReal.mul_inv_cancel (by positivity) (by simp)

instance identitySpecialOrthogonalNorthPoleConeRadialMeasure_isFinite
    (n : ℕ) :
    IsFiniteMeasure
      (identitySpecialOrthogonalNorthPoleConeRadialMeasure n) where
  measure_univ_lt_top :=
    identitySpecialOrthogonalNorthPoleConeRadialMeasure_univ_lt_top n

theorem
    identitySpecialOrthogonalNorthPoleConeWeightedDomainMeasure_univ
    (n : ℕ) :
    (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict
      (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
      fun p => ENNReal.ofReal
        (p.2 ^ n /
          identitySpecialOrthogonalNorthPoleFinalCoordinate p.1)) univ =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).withDensity
        (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n))) univ *
      ENNReal.ofReal ((n + 1 : ℝ)⁻¹) := by
  rw [withDensity_identitySpecialOrthogonalNorthPoleConeDomain_eq_prod,
    Measure.prod_apply MeasurableSet.univ]
  change
    (∫⁻ _x,
      identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (Metric.ball 0 1)).withDensity
            (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n))) =
      _
  rw [identitySpecialOrthogonalNorthPoleConeRadialMeasure_univ,
    lintegral_const]
  exact mul_comm _ _

end PositiveDefiniteIntegralLattice
