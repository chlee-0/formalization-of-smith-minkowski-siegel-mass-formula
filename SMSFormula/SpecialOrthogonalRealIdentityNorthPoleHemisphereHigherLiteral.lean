import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereTargetRestriction

/-!
# The normalized positive-hemisphere comparison on the literal higher group

This module transports the mapped higher differential restriction through the
explicit ambient-matrix-preserving mapped-to-literal equivalence.  It then
maps the already opaque normalized local sphere-side comparison through the
same equivalence and substitutes the separate restricted differential-fiber
bind theorem.

The sphere-step, factor two, and reciprocal transition scalar remain
explicit.  No total-mass cancellation, global normalized Haar comparison,
rank recurrence, or Gamma evaluation is used.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleHemisphereHigherLiteralGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleHemisphereHigherLiteralGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

local instance identityNorthPoleHemisphereHigherLiteralMappedGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleHemisphereHigherLiteralMappedGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The exact preimage of the literal higher target under the
mapped-to-literal equivalence is the mapped higher chart set. -/
theorem
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_preimage_literalHigherChartTargetSet
    (n : ℕ) :
    identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 2) ⁻¹'
        identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n =
      identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
        (n + 1) := by
  ext g
  simp only [
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet,
    Set.mem_preimage]
  rw [identitySpecialOrthogonalMappedIdentityGroupToLiteral_leftInverse]

/-- Restricting mapped higher differential Haar to the higher product chart
and applying the explicit equivalence gives canonical literal differential
Haar restricted to the literal higher target.  No Haar uniqueness or
rescaling is used. -/
theorem
    map_restrict_identitySpecialOrthogonalNorthPoleProductHigherDifferentialMeasure_toLiteral
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 2))
        ((specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
              (n + 1))) =
      (identitySpecialOrthogonalDifferentialMeasure (n + 1)).restrict
        (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
          n) := by
  let μ :=
    specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let S :=
    identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet (n + 1)
  let T :=
    identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet n
  let f := identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 2)
  have hf : Measurable f :=
    (continuous_identitySpecialOrthogonalMappedIdentityGroupToLiteral
      (n + 2)).measurable
  have hT : MeasurableSet T :=
    measurableSet_identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
      n
  have hpre : f ⁻¹' T = S :=
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_preimage_literalHigherChartTargetSet
      n
  have hfun :
      f =
        (identitySpecialOrthogonalMappedGroupContinuousEquiv (n + 1) :
          _ → _) := by
    funext g
    exact
      identitySpecialOrthogonalMappedIdentityGroupToLiteral_eq_mappedGroupContinuousEquiv
        (n + 1) g
  change Measure.map f (μ.restrict S) =
    (identitySpecialOrthogonalDifferentialMeasure (n + 1)).restrict T
  calc
    Measure.map f (μ.restrict S) =
        (Measure.map f μ).restrict T := by
      rw [Measure.restrict_map hf hT, hpre]
    _ =
        (identitySpecialOrthogonalDifferentialMeasure (n + 1)).restrict T := by
      rw [hfun, identitySpecialOrthogonalDifferentialMeasure]

/-- Mapping the measurable mapped sphere fiber back to the literal group
recovers the literal sphere fiber pointwise. -/
theorem
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_comp_measurableMappedSphereFiber
    (n : ℕ) :
    identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 2) ∘
        identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
          n =
      identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
        n := by
  funext p
  rw [
    Function.comp_apply,
    identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization,
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_rightInverse]

/-- The existing normalized local sphere-side comparison transported
entirely to the literal higher group. -/
theorem
    identitySpecialOrthogonalSphereStep_smul_two_smul_map_literalSphereFiber_eq_smul_literalHigherDifferential
    (n : ℕ) :
    identitySpecialOrthogonalSphereStep (n + 2) •
        ((2 : ℝ≥0∞) •
          Measure.map
            (identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
              n)
            (identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
              n)) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|)⁻¹ •
        (identitySpecialOrthogonalDifferentialMeasure (n + 1)).restrict
          (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n) := by
  let f := identitySpecialOrthogonalMappedIdentityGroupToLiteral (n + 2)
  let ν :=
    identitySpecialOrthogonalNorthPoleProductRestrictedLiteralLowerDifferentialNormalizedSphereHemisphereMeasure
      n
  let g :=
    identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
      n
  let μ :=
    (specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
          (n + 1))
  let a := identitySpecialOrthogonalSphereStep (n + 2)
  let c :=
    (Real.toNNReal
      |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
        (n + 1)|)⁻¹
  have hf : Measurable f :=
    (continuous_identitySpecialOrthogonalMappedIdentityGroupToLiteral
      (n + 2)).measurable
  have hg : Measurable g :=
    measurable_identitySpecialOrthogonalNorthPoleProductMeasurableMappedSphereFiberParametrization
      n
  have horiginal :
      a • ((2 : ℝ≥0∞) • Measure.map g ν) = c • μ :=
    identitySpecialOrthogonalSphereStep_smul_two_smul_map_restrictedNormalizedSphereFiber_eq_smul_higherDifferential
      n
  have hmapped :=
    congrArg (Measure.map f) horiginal
  change
    a • ((2 : ℝ≥0∞) •
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
          n) ν) =
      c •
        (identitySpecialOrthogonalDifferentialMeasure (n + 1)).restrict
          (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n)
  calc
    a • ((2 : ℝ≥0∞) •
        Measure.map
          (identitySpecialOrthogonalNorthPoleProductMeasurableLiteralSphereFiberParametrization
            n) ν) =
      Measure.map f (a • ((2 : ℝ≥0∞) • Measure.map g ν)) := by
        rw [Measure.map_smul, Measure.map_smul,
          Measure.map_map hf hg,
          identitySpecialOrthogonalMappedIdentityGroupToLiteral_comp_measurableMappedSphereFiber]
    _ = Measure.map f (c • μ) := hmapped
    _ =
      c •
        (identitySpecialOrthogonalDifferentialMeasure (n + 1)).restrict
          (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n) := by
      rw [Measure.map_smul,
        map_restrict_identitySpecialOrthogonalNorthPoleProductHigherDifferentialMeasure_toLiteral]

/-- Substituting the separate target-restricted hemisphere fiber bind gives
the normalized local comparison in intrinsic literal differential-fiber
language.  All three scalars remain explicit. -/
theorem
    identitySpecialOrthogonalSphereStep_smul_two_smul_restrict_hemisphereFiberKernel_eq_smul_literalHigherDifferential
    (n : ℕ) :
    identitySpecialOrthogonalSphereStep (n + 2) •
        ((2 : ℝ≥0∞) •
          (identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
              ((identitySpecialOrthogonalNormalizedSphereMeasure
                (n + 1)).restrict
                (identitySpecialOrthogonalNorthPoleHemisphere (n + 1)))
            ).restrict
              (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
                n)) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar
          (n + 1)|)⁻¹ •
        (identitySpecialOrthogonalDifferentialMeasure (n + 1)).restrict
          (identitySpecialOrthogonalNorthPoleProductLiteralHigherChartTargetSet
            n) := by
  rw [
    ←
      map_identitySpecialOrthogonalNorthPoleHemisphereJointFiber_coupledProduct_eq_restrict_fiberKernel_comp,
    map_identitySpecialOrthogonalNorthPoleHemisphereJointFiber_coupledProduct]
  exact
    identitySpecialOrthogonalSphereStep_smul_two_smul_map_literalSphereFiber_eq_smul_literalHigherDifferential
      n

end PositiveDefiniteIntegralLattice
