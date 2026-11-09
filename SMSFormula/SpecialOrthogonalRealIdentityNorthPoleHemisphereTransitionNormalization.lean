import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereSelectedTargetMass

/-!
# Normalizing the identity north-pole transition determinant

The reciprocal absolute transition determinant is converted to the ratio of
the consecutive-rank fixed-to-elementary tangent determinants.  This ratio is
then combined with the selected-target mass identity to give the
elementary-normalized consecutive-rank mass relation.

The fixed rational tangent bases are arbitrary.  Their determinant factors
therefore remain explicit; no numerical value is assigned to either one.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

/-- In `ENNReal`, the reciprocal absolute transition determinant is the ratio
of the consecutive fixed-to-elementary tangent determinant factors. -/
theorem
    inv_toNNReal_abs_identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
    (n : ℕ) :
    (Real.toNNReal
      |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
        (n + 1)| : ℝ≥0∞)⁻¹ =
      (Real.toNNReal
        |(identitySpecialOrthogonalFixedElementaryDetScalar
          (n + 1) : ℝ)| : ℝ≥0∞) /
        (Real.toNNReal
          |(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 2) : ℝ)| : ℝ≥0∞) := by
  have htransition :
      identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1) ≠ 0 :=
    identitySpecialOrthogonalNorthPoleProductTransitionDetScalar_ne_zero
      (n + 1)
  have hhigher :
      (identitySpecialOrthogonalFixedElementaryDetScalar
          (n + 2) : ℝ) ≠ 0 := by
    exact_mod_cast
      identitySpecialOrthogonalFixedElementaryDetScalar_ne_zero (n + 2)
  have hreal :
      |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|⁻¹ =
        |(identitySpecialOrthogonalFixedElementaryDetScalar
          (n + 1) : ℝ)| /
          |(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 2) : ℝ)| := by
    rw [
      abs_identitySpecialOrthogonalNorthPoleProductTransitionDetScalar,
      inv_inv,
      abs_identitySpecialOrthogonalTangentSplitDetScalar]
  calc
    (Real.toNNReal
      |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
        (n + 1)| : ℝ≥0∞)⁻¹ =
        (ENNReal.ofReal
          |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
            (n + 1)|)⁻¹ := rfl
    _ = ENNReal.ofReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (abs_pos.mpr htransition)]
    _ = ENNReal.ofReal
        (|(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 1) : ℝ)| /
          |(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 2) : ℝ)|) :=
      congrArg ENNReal.ofReal hreal
    _ = ENNReal.ofReal
          |(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 1) : ℝ)| /
        ENNReal.ofReal
          |(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 2) : ℝ)| := by
      rw [ENNReal.ofReal_div_of_pos (abs_pos.mpr hhigher)]
    _ = (Real.toNNReal
        |(identitySpecialOrthogonalFixedElementaryDetScalar
          (n + 1) : ℝ)| : ℝ≥0∞) /
        (Real.toNNReal
          |(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 2) : ℝ)| : ℝ≥0∞) := rfl

/-- After inserting the transition ratio, inverse consecutive-rank
fixed-to-elementary factors telescope across the differential mass relation.
No iteration over ranks or Gamma evaluation is used. -/
theorem
    identitySpecialOrthogonalElementaryNormalizedHigherMass_eq_two_sphereStep_mul_elementaryNormalizedLowerMass
    (n : ℕ) :
    (Real.toNNReal
      |(identitySpecialOrthogonalFixedElementaryDetScalar
        (n + 2) : ℝ)| : ℝ≥0∞)⁻¹ *
        identitySpecialOrthogonalDifferentialMeasure (n + 1) Set.univ =
      (2 * identitySpecialOrthogonalSphereStep (n + 2)) *
        ((Real.toNNReal
          |(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 1) : ℝ)| : ℝ≥0∞)⁻¹ *
          identitySpecialOrthogonalDifferentialMeasure n Set.univ) := by
  let a : ℝ≥0∞ :=
    Real.toNNReal
      |(identitySpecialOrthogonalFixedElementaryDetScalar
        (n + 1) : ℝ)|
  let b : ℝ≥0∞ :=
    Real.toNNReal
      |(identitySpecialOrthogonalFixedElementaryDetScalar
        (n + 2) : ℝ)|
  let lowerMass : ℝ≥0∞ :=
    identitySpecialOrthogonalDifferentialMeasure n Set.univ
  let higherMass : ℝ≥0∞ :=
    identitySpecialOrthogonalDifferentialMeasure (n + 1) Set.univ
  let sphereStep : ℝ≥0∞ :=
    identitySpecialOrthogonalSphereStep (n + 2)
  have haR :
      (identitySpecialOrthogonalFixedElementaryDetScalar
          (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast
      identitySpecialOrthogonalFixedElementaryDetScalar_ne_zero (n + 1)
  have haNN :
      Real.toNNReal
          |(identitySpecialOrthogonalFixedElementaryDetScalar
            (n + 1) : ℝ)| ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (abs_pos.mpr haR))
  have ha0 : a ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr haNN
  have haTop : a ≠ ⊤ := ENNReal.coe_ne_top
  have htransition :
      identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1) ≠ 0 :=
    identitySpecialOrthogonalNorthPoleProductTransitionDetScalar_ne_zero
      (n + 1)
  have htransitionNN :
      Real.toNNReal
          |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
            (n + 1)| ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (abs_pos.mpr htransition))
  have hmassRaw :=
    identitySpecialOrthogonalSphereStep_mul_two_mul_lowerMass_eq_transition_mul_higherMass
      n
  rw [
    ENNReal.coe_inv htransitionNN,
    inv_toNNReal_abs_identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
      n] at hmassRaw
  have hmass :
      sphereStep * (2 * lowerMass) = (a / b) * higherMass := by
    simpa [a, b, lowerMass, higherMass, sphereStep] using hmassRaw
  change b⁻¹ * higherMass =
    (2 * sphereStep) * (a⁻¹ * lowerMass)
  calc
    b⁻¹ * higherMass =
        (a⁻¹ * a) * (b⁻¹ * higherMass) := by
      rw [ENNReal.inv_mul_cancel ha0 haTop, one_mul]
    _ = a⁻¹ * ((a / b) * higherMass) := by
      rw [div_eq_mul_inv]
      ac_rfl
    _ = a⁻¹ * (sphereStep * (2 * lowerMass)) := by
      rw [← hmass]
    _ = (2 * sphereStep) * (a⁻¹ * lowerMass) := by
      ac_rfl

end PositiveDefiniteIntegralLattice
