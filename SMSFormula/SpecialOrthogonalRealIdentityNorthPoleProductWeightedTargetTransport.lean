import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductWeightedSquareMeasure

/-!
# Fixed-linear weighted target transport for the identity north-pole product

This module transports the pulled-back square-carrier target restriction
through the fixed product-to-higher tangent equivalence.  The
rational-basis determinant scalar remains explicit, first for the unweighted
restricted coordinate Haar measures and then for the target-density-weighted
measures.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductWeightedTargetMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductWeightedTargetBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

/-- The inverse image of the exact higher target under the fixed linear
equivalence is the pulled-back square-carrier target. -/
theorem
    preimage_identitySpecialOrthogonalNorthPoleProductTransitionTargetSet
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n ⁻¹'
        identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n =
      (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
        ).symm ''
        identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n := by
  ext x
  constructor
  · intro hx
    exact
      ⟨identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n x,
        hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/-- The fixed linear equivalence transports the restricted coordinate Haar
with the reciprocal absolute basis determinant. -/
theorem
    map_restrict_identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv_target
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n)
        ((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          ((identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
            ).symm ''
            identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|
          )⁻¹ •
        (identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n) := by
  let e :=
    identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
  let S :=
    e.symm '' identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n
  let T :=
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n
  let μ :=
    identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n
  let ν :=
    identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
      n
  let q : ℝ≥0 :=
    (Real.toNNReal
      |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|)⁻¹
  have hT : MeasurableSet T :=
    (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet_isOpen n
      ).measurableSet
  have hpre : e ⁻¹' T = S := by
    simpa [e, S, T] using
      preimage_identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n
  calc
    Measure.map e (μ.restrict S) =
        Measure.map e (μ.restrict (e ⁻¹' T)) := by rw [hpre]
    _ = (Measure.map e μ).restrict T := by
      rw [Measure.restrict_map e.continuous.measurable hT]
    _ = (q • ν).restrict T := by
      rw [
        map_identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv_sourceCoordinateMeasure]
    _ = q • ν.restrict T := by rw [Measure.restrict_smul]

/-- The square-carrier target density is definitionally the ambient higher
target density pulled back through the fixed linear equivalence. -/
theorem
    identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity_eq_comp
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity n =
      identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity n ∘
        identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n :=
  rfl

/-- The fixed linear equivalence transports the weighted pulled-back target
measure with the same reciprocal absolute rational-basis determinant. -/
theorem
    map_withDensity_identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv_target
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n)
        (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          ((identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
            ).symm ''
            identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity
              n)) =
      (Real.toNNReal
        |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|
          )⁻¹ •
        (((identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
          ).withDensity
            (identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity
              n)) := by
  let e :=
    identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
  let μ :=
    (identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n).restrict
      (e.symm ''
        identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
  let ν :=
    (identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
      n).restrict
      (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
  let g :=
    identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity n
  let q : ℝ≥0 :=
    (Real.toNNReal
      |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n|)⁻¹
  rw [
    identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity_eq_comp]
  calc
    Measure.map e (μ.withDensity (g ∘ e)) =
        (Measure.map e μ).withDensity g :=
      map_withDensity_comp_of_measurable e μ g e.continuous.measurable
        (measurable_identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity
          n)
    _ = (q • ν).withDensity g := by
      rw [
        map_restrict_identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv_target]
    _ = q • ν.withDensity g := by
      ext s hs
      simp [withDensity_apply, hs]

end PositiveDefiniteIntegralLattice
