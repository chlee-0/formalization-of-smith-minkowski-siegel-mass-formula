import SMSFormula.PadicSpecialOrthogonalDifferentialLocalInverseVolumeConvergence

/-!
# The finite differential special-stabilizer volume scalar

The differential local inverse-volume cutoff products converge to the inverse
canonical finite correction times the existing real Schulze--Pillot product
limit.  This module names that limit as the finite differential stabilizer
inverse-volume scalar and names its reciprocal as the corresponding volume
scalar.

These are scalar interfaces only.  No restricted-product measure, real-place
factor, reference Haar comparison, or Tamagawa theorem is introduced.
-/

noncomputable section

open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The finite differential special-stabilizer inverse-volume scalar attached
to a real Schulze--Pillot cutoff-product limit. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) : ℝ≥0∞ :=
  L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct⁻¹ *
    ENNReal.ofReal P

/-- The finite differential special-stabilizer volume scalar is the
reciprocal of its named inverse-volume scalar. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) : ℝ≥0∞ :=
  (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P)⁻¹

/-- A positive real cutoff-product limit gives a nonzero differential
finite-stabilizer inverse volume. -/
theorem
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P ≠
      0 := by
  unfold
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
  exact mul_ne_zero
    (ENNReal.inv_ne_zero.mpr
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_ne_top)
    (ENNReal.ofReal_ne_zero_iff.mpr hP)

/-- The differential finite-stabilizer inverse volume is always finite:
`ENNReal.ofReal` and the inverse finite correction cannot be infinite. -/
theorem
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_top
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P ≠
      ⊤ := by
  unfold
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_ne_zero)
    ENNReal.ofReal_ne_top

/-- The differential finite-stabilizer volume is always nonzero because its
named inverse volume is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P ≠ 0 := by
  unfold localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume
  exact ENNReal.inv_ne_zero.mpr
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_top
      P)

/-- A positive real cutoff-product limit gives a finite differential
finite-stabilizer volume. -/
theorem
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_top
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P ≠ ⊤ := by
  unfold localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume
  exact ENNReal.inv_ne_top.mpr
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_zero
      hP)

/-- The named finite-stabilizer volume is literally the reciprocal of the
named inverse volume. -/
theorem
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_eq_inv_inverseVolume
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P =
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
        P)⁻¹ :=
  rfl

/-- Conversely, the named inverse volume is the reciprocal of the named
finite-stabilizer volume. -/
theorem
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_eq_inv_volume
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P =
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P)⁻¹ := by
  simp only [
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume, inv_inv]

/-- The positive finite inverse-volume and volume scalars multiply to one. -/
theorem
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_mul_volume_eq_one
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P =
      1 := by
  rw [
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_eq_inv_inverseVolume]
  exact ENNReal.mul_inv_cancel
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_zero
      hP)
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_top
      P)

/-- The positive finite volume and inverse-volume scalars multiply to one in
the opposite order as well. -/
theorem
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_mul_inverseVolume_eq_one
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
          P =
      1 := by
  rw [mul_comm]
  exact
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_mul_volume_eq_one
      hP

/-- The differential inverse-volume partial products converge to the named
finite-stabilizer inverse-volume scalar. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo_finiteStabilizerInverseVolume_of_massLocalInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] {P : ℝ}
    (hP : massLocalInverseProductTendsTo L P) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
        P) := by
  simpa only [
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume] using
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo_inv_localCorrectionFiniteProduct_mul_ENNReal_ofReal_of_massLocalInverseProductTendsTo
      hP

end PositiveDefiniteIntegralLattice
