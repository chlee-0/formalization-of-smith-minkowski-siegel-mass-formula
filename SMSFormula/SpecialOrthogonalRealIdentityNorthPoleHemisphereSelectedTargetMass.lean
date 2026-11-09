import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereFullSphereRestriction

/-!
# Cancelling the finite positive higher-chart probability mass

The literal higher product-chart target is an open identity neighborhood.
Its higher-rank probability-Haar mass is therefore positive and finite.  The
restricted full-sphere comparison is evaluated on this target, rewritten
through the common probability Haar measure, and only that selected mass is
cancelled.

The transition determinant remains explicit.  No tangent-basis scalar
simplification, rank recurrence, or Gamma evaluation is used.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleHemisphereSelectedTargetMassGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleHemisphereSelectedTargetMassGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- The identity belongs to the literal higher product-chart target. -/
theorem
    one_mem_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
    (n : ℕ) :
    (1 : identitySpecialOrthogonalGroup (n + 1)) ∈
      identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
        n := by
  change
    identitySpecialOrthogonalLiteralIdentityGroupToMapped (n + 2) 1 ∈
      identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
        (n + 1)
  rw [identitySpecialOrthogonalLiteralIdentityGroupToMapped_one]
  constructor
  · rw [
      ← identitySpecialOrthogonalNorthPoleProductMappedGroup_zero (n + 1)]
    exact
      identitySpecialOrthogonalNorthPoleProductMappedGroup_mem_commonMappedGroupSet
        (n + 1)
        ⟨0,
          zero_mem_identitySpecialOrthogonalNorthPoleProductDomainSet
            (n + 1)⟩
  · exact
      self_mem_specialFormPreservingSmoothRealChart_source
        (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero
        1

/-- Higher probability-Haar mass of the exact literal product-chart target. -/
def
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass
    (n : ℕ) : ℝ≥0∞ :=
  identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)
    (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet n)

/-- The selected target probability mass is nonzero. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass_ne_zero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass
        n ≠ 0 := by
  let ν := identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)
  let T :=
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet n
  letI : Measure.IsOpenPosMeasure ν := inferInstance
  change ν T ≠ 0
  exact
    ne_of_gt
      ((isOpen_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
        n).measure_pos ν
        ⟨1,
          one_mem_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n⟩)

/-- The selected target probability mass is finite. -/
theorem
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass_ne_top
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass
        n ≠ ⊤ := by
  exact
    ne_of_lt
      (measure_lt_top
        (identitySpecialOrthogonalProbabilityHaarMeasure (n + 1))
        (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n))

/-- Evaluating the restricted local comparison on the whole group leaves the
same selected target probability mass on both scalar sides. -/
theorem
    identitySpecialOrthogonalSphereStep_mul_two_mul_lowerMass_mul_selectedTargetMass_eq_transition_mul_higherMass_mul_selectedTargetMass
    (n : ℕ) :
    (identitySpecialOrthogonalSphereStep (n + 2) *
        (2 * identitySpecialOrthogonalDifferentialMeasure n Set.univ)) *
        identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass
          n =
      ((Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|)⁻¹ *
        identitySpecialOrthogonalDifferentialMeasure (n + 1) Set.univ) *
        identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass
          n := by
  let T :=
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet n
  let ν :=
    identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)
  have hT : MeasurableSet T :=
    measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
      n
  have hmeasure :=
    identitySpecialOrthogonalSphereStep_smul_two_smul_restrict_lowerMass_probabilityHaar_eq_smul_literalHigherDifferential
      n
  rw [
    identitySpecialOrthogonalDifferentialMeasure_eq_univ_smul_probabilityHaar
      (n + 1)] at hmeasure
  have hmass :=
    congrArg
      (fun μ : Measure (identitySpecialOrthogonalGroup (n + 1)) =>
        μ Set.univ)
      hmeasure
  simpa only [
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass,
    Measure.smul_apply,
    Measure.restrict_apply_univ,
    ENNReal.smul_def,
    smul_eq_mul,
    mul_assoc] using hmass

/-- Cancelling only the finite positive selected target probability mass gives
the explicit scalar identity.  The transition determinant is deliberately
left unsimplified. -/
theorem
    identitySpecialOrthogonalSphereStep_mul_two_mul_lowerMass_eq_transition_mul_higherMass
    (n : ℕ) :
    identitySpecialOrthogonalSphereStep (n + 2) *
        (2 * identitySpecialOrthogonalDifferentialMeasure n Set.univ) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|)⁻¹ *
        identitySpecialOrthogonalDifferentialMeasure (n + 1) Set.univ := by
  let left :=
    identitySpecialOrthogonalSphereStep (n + 2) *
      (2 * identitySpecialOrthogonalDifferentialMeasure n Set.univ)
  let right :=
    (Real.toNNReal
      |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
        (n + 1)|)⁻¹ *
      identitySpecialOrthogonalDifferentialMeasure (n + 1) Set.univ
  let mass :=
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass
      n
  have hmass0 : mass ≠ 0 :=
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass_ne_zero
      n
  have hmassTop : mass ≠ ⊤ :=
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartProbabilityMass_ne_top
      n
  have hmul : left * mass = right * mass :=
    identitySpecialOrthogonalSphereStep_mul_two_mul_lowerMass_mul_selectedTargetMass_eq_transition_mul_higherMass_mul_selectedTargetMass
      n
  change left = right
  calc
    left = left * 1 := (mul_one left).symm
    _ = left * (mass * mass⁻¹) := by
      rw [ENNReal.mul_inv_cancel hmass0 hmassTop]
    _ = (left * mass) * mass⁻¹ := by
      exact (mul_assoc left mass mass⁻¹).symm
    _ = (right * mass) * mass⁻¹ := by
      rw [hmul]
    _ = right * (mass * mass⁻¹) := by
      exact mul_assoc right mass mass⁻¹
    _ = right * 1 := by
      rw [ENNReal.mul_inv_cancel hmass0 hmassTop]
    _ = right := mul_one right

end PositiveDefiniteIntegralLattice
