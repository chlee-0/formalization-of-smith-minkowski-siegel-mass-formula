import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductDensityCocycle

/-!
# Ambient density interface for the identity north-pole product

The differential densities on the exact source and target subtypes are
extended measurably by zero to their ambient tangent carriers.  The higher
target extension is also pulled back through the fixed product-to-higher
linear equivalence, matching the square transition used by the nonlinear
change-of-variables theorem.

The full subtype density cocycle is restated pointwise on the ambient exact
source and almost everywhere for the restricted source-coordinate measure.
-/

open scoped Matrix Matrix.Norms.Operator ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductAmbientDensityMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductAmbientDensityBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

/-- The product source density, extended by zero from the exact open source to
the ambient product tangent carrier. -/
def identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity
    (n : ℕ)
    (x : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    ℝ≥0∞ :=
  Function.extend
    (Subtype.val :
      identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n →
        identitySpecialOrthogonalMappedTangent n ×
          EuclideanSpace ℝ (Fin n))
    (identitySpecialOrthogonalNorthPoleProductSourceDensity n)
    (fun _ => 0) x

/-- The higher identity-chart target density, extended by zero from the exact
open transition target to the ambient higher tangent carrier. -/
def identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity
    (n : ℕ)
    (y : identitySpecialOrthogonalMappedTangent (n + 1)) :
    ℝ≥0∞ :=
  Function.extend
    (Subtype.val :
      identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n →
        identitySpecialOrthogonalMappedTangent (n + 1))
    (identitySpecialOrthogonalNorthPoleProductTargetDensity n)
    (fun _ => 0) y

/-- The ambient higher target density pulled back through the fixed linear
equivalence to the square-transition carrier. -/
def identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity
    (n : ℕ)
    (z : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    ℝ≥0∞ :=
  identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity n
    (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n z)

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n) := by
  exact
    (MeasurableEmbedding.subtype_coe
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
        ).measurableSet).measurable_extend
      (measurable_identitySpecialOrthogonalNorthPoleProductSourceDensity n)
      measurable_const

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity n) := by
  exact
    (MeasurableEmbedding.subtype_coe
      (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet_isOpen n
        ).measurableSet).measurable_extend
      (measurable_identitySpecialOrthogonalNorthPoleProductTargetDensity n)
      measurable_const

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity
        n) :=
  (measurable_identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity
    n).comp
    (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
      ).continuous.measurable

/-- On the exact source, the ambient source extension is the subtype
density. -/
theorem identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity_eq
    (n : ℕ)
    (x : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n))
    (hx :
      x ∈ identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n x =
      identitySpecialOrthogonalNorthPoleProductSourceDensity n ⟨x, hx⟩ := by
  exact
    Function.Injective.extend_apply Subtype.val_injective _ _ ⟨x, hx⟩

/-- On the exact target, the ambient target extension is the subtype
density. -/
theorem identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity_eq
    (n : ℕ)
    (y : identitySpecialOrthogonalMappedTangent (n + 1))
    (hy :
      y ∈ identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n) :
    identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity n y =
      identitySpecialOrthogonalNorthPoleProductTargetDensity n ⟨y, hy⟩ := by
  exact
    Function.Injective.extend_apply Subtype.val_injective _ _ ⟨y, hy⟩

/-- Along the square transition, the pulled-back ambient target extension is
the higher target density along the product transition. -/
theorem
    identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity_eq_alongTransition
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity n
        (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n p.1) =
      identitySpecialOrthogonalNorthPoleProductTargetDensityAlongTransition
        n p := by
  rw [
    identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity,
    identitySpecialOrthogonalNorthPoleProductTransitionSquareMap,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [
    identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity_eq
      n
      (identitySpecialOrthogonalNorthPoleProductTransition n p.1)
      (identitySpecialOrthogonalNorthPoleProductTransitionOnSource n p).2]
  apply congrArg
    (identitySpecialOrthogonalNorthPoleProductTargetDensity n)
  exact Subtype.ext rfl

/-- The subtype cocycle rewritten pointwise on the ambient exact source. -/
theorem identitySpecialOrthogonalNorthPoleProductAmbientDensityCocycle
    (n : ℕ)
    (x : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n))
    (hx :
      x ∈ identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n x =
      identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian n x *
        identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity n
          (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n x) := by
  rw [
    identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity_eq n x hx,
    identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity_eq_alongTransition
      n ⟨x, hx⟩]
  exact
    identitySpecialOrthogonalNorthPoleProductDensityCocycleAt_full n ⟨x, hx⟩

/-- Almost everywhere on the restricted source-coordinate measure, the
ambient source density is the pulled-back target density times the square
Jacobian.  This is the order expected by the generic `withDensity` transport
lemma. -/
theorem
    identitySpecialOrthogonalNorthPoleProductAmbientDensityCocycle_ae
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n =ᵐ[
      (identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
        n).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)]
      fun x =>
        identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity n
            (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n x) *
          identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian
            n x := by
  filter_upwards [
    MeasureTheory.ae_restrict_mem
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
        ).measurableSet] with x hx
  simpa [mul_comm] using
    identitySpecialOrthogonalNorthPoleProductAmbientDensityCocycle n x hx

end PositiveDefiniteIntegralLattice
