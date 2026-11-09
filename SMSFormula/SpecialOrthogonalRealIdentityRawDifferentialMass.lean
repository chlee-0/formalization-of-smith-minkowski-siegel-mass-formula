import SMSFormula.SpecialOrthogonalAdelicDifferentialProperMassRearrangement
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereGammaVolume

/-!
# Raw identity-model real differential mass

The Gamma formula is stated for the identity-model differential mass after
converting the fixed arbitrary rational tangent basis to the elementary
skew-symmetric basis.  This module cancels that conversion explicitly and
recovers the total mass of the raw differential Haar.

The fixed-to-elementary determinant factor remains visible.  Its `ENNReal`
coercion is proved nonzero and finite before cancellation.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

/-- The absolute fixed-to-elementary tangent determinant gives a nonzero
`ENNReal` scalar. -/
theorem identitySpecialOrthogonalFixedElementaryDetFactor_ne_zero
    (n : ℕ) :
    (Real.toNNReal
      |(identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ)| :
        ℝ≥0∞) ≠ 0 := by
  have hdetR :
      (identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast
      identitySpecialOrthogonalFixedElementaryDetScalar_ne_zero (n + 1)
  exact ENNReal.coe_ne_zero.mpr
    (ne_of_gt (Real.toNNReal_pos.mpr (abs_pos.mpr hdetR)))

/-- The absolute fixed-to-elementary tangent determinant gives a finite
`ENNReal` scalar. -/
theorem identitySpecialOrthogonalFixedElementaryDetFactor_ne_top
    (n : ℕ) :
    (Real.toNNReal
      |(identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ)| :
        ℝ≥0∞) ≠ ⊤ :=
  ENNReal.coe_ne_top

/-- The raw identity-model differential total mass is the fixed-to-elementary
tangent determinant times the elementary Gamma product. -/
theorem identitySpecialOrthogonalDifferentialMeasure_univ_eq_det_mul_gamma
    (n : ℕ) :
    identitySpecialOrthogonalDifferentialMeasure n Set.univ =
      (Real.toNNReal
        |(identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ)| :
          ℝ≥0∞) *
        ENNReal.ofReal
          ((2 : ℝ) ^ n *
              Real.pi ^ ((n : ℝ) * ((n : ℝ) + 3) / 4) /
            (∏ k ∈ Finset.range n,
              Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))) := by
  let a : ℝ≥0∞ :=
    (Real.toNNReal
      |(identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ)| :
        ℝ≥0∞)
  let rawMass : ℝ≥0∞ :=
    identitySpecialOrthogonalDifferentialMeasure n Set.univ
  let gammaMass : ℝ≥0∞ :=
    ENNReal.ofReal
      ((2 : ℝ) ^ n *
          Real.pi ^ ((n : ℝ) * ((n : ℝ) + 3) / 4) /
        (∏ k ∈ Finset.range n,
          Real.Gamma (((k + 2 : ℕ) : ℝ) / 2)))
  change rawMass = a * gammaMass
  have ha0 : a ≠ 0 :=
    identitySpecialOrthogonalFixedElementaryDetFactor_ne_zero n
  have hatop : a ≠ ⊤ :=
    identitySpecialOrthogonalFixedElementaryDetFactor_ne_top n
  have hnormalized : a⁻¹ * rawMass = gammaMass := by
    change
      identitySpecialOrthogonalElementaryNormalizedDifferentialMass n =
        ENNReal.ofReal
          ((2 : ℝ) ^ n *
              Real.pi ^ ((n : ℝ) * ((n : ℝ) + 3) / 4) /
            (∏ k ∈ Finset.range n,
              Real.Gamma (((k + 2 : ℕ) : ℝ) / 2)))
    exact identitySpecialOrthogonalElementaryNormalizedDifferentialMass_eq_gamma
      n
  calc
    rawMass = (a * a⁻¹) * rawMass := by
      rw [ENNReal.mul_inv_cancel ha0 hatop, one_mul]
    _ = a * (a⁻¹ * rawMass) := by
      rw [mul_assoc]
    _ = a * gammaMass := by
      rw [hnormalized]

/-- Reciprocal form of the raw identity-model differential mass.  The inverse
is deliberately left around the complete determinant-times-Gamma product. -/
theorem identitySpecialOrthogonalDifferentialMeasure_univ_inv_eq
    (n : ℕ) :
    (identitySpecialOrthogonalDifferentialMeasure n Set.univ)⁻¹ =
      ((Real.toNNReal
          |(identitySpecialOrthogonalFixedElementaryDetScalar (n + 1) : ℝ)| :
            ℝ≥0∞) *
        ENNReal.ofReal
          ((2 : ℝ) ^ n *
              Real.pi ^ ((n : ℝ) * ((n : ℝ) + 3) / 4) /
            (∏ k ∈ Finset.range n,
              Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))))⁻¹ := by
  rw [identitySpecialOrthogonalDifferentialMeasure_univ_eq_det_mul_gamma]

end PositiveDefiniteIntegralLattice
