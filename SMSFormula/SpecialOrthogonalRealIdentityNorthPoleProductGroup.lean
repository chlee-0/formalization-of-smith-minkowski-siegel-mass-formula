import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductSourceDifferentialMeasure

/-!
# The group product behind the identity north-pole transition

On the exact lower differential/sphere source, this module packages the
group-valued north-pole product represented by the ambient product
coordinate. It then extends that group map measurably to the full product
carrier and proves that its higher identity-chart coordinate agrees with the
product transition on the exact source.

A small measurable extension of the product transition is used only to
reassociate `Measure.map`. The higher target differential theorem is not
substituted, and no chart injectivity, fiber identification, or rank recurrence
is asserted.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductGroupMeasureMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductGroupMeasureMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductGroupMeasureGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductGroupMeasureGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The ambient product coordinate, with its exact-domain proof, on the
pulled-back lower differential/sphere source. -/
def identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource
    (n : ℕ)
    (p :
      identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n) :
    identitySpecialOrthogonalNorthPoleProductDomain n :=
  ⟨identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
      n p.1,
    identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset n
      p.2⟩

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource n) :=
  ((measurable_identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
    n).comp continuous_subtype_val.measurable).subtype_mk

theorem
    identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource_mem_higherChartSource
    (n : ℕ)
    (p :
      identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n) :
    identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource n p ∈
      identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet
        n := by
  rcases p.2 with ⟨q, hq, hqeq⟩
  have heq :
      identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource n p = q := by
    apply Subtype.ext
    exact hqeq.symm
  exact heq.symm ▸ hq

/-- The genuine rank-`n+1` group product on the exact lower
differential/sphere source. -/
def identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource
    (n : ℕ)
    (p :
      identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n) :
    specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
        (algebraMap ℚ ℝ)) :=
  identitySpecialOrthogonalNorthPoleProductMappedGroup n
    (identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource n p)

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource n) :=
  (identitySpecialOrthogonalNorthPoleProductMappedGroup_continuous n
    ).measurable.comp
      (measurable_identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource
        n)

theorem
    identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource_mem_higherChartGroupSet
    (n : ℕ)
    (p :
      identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n) :
    identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource n p ∈
      identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n := by
  refine ⟨
    identitySpecialOrthogonalNorthPoleProductMappedGroup_mem_commonMappedGroupSet
      n
      (identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource n p),
    ?_⟩
  exact
    identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource_mem_higherChartSource
      n p

/-- A globally measurable extension of the actual group product. Its value off
the exact pulled-back source is irrelevant below. -/
def identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
        (algebraMap ℚ ℝ)) :=
  Function.extend
    (Subtype.val :
      identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
          n →
        specialFormPreservingMatrixSubgroup
            ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
          Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    (identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource n)
    (fun _ => 1) p

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n) := by
  exact
    (MeasurableEmbedding.subtype_coe
      (measurableSet_identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n)).measurable_extend
      (measurable_identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource
        n)
      measurable_const

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hp :
      p ∈
        identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
          n) :
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n p =
      identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource n
        ⟨p, hp⟩ := by
  exact
    Function.Injective.extend_apply Subtype.val_injective _ _ ⟨p, hp⟩

/-- A globally measurable product-transition extension, obtained from the
measurable square transition and the fixed linear equivalence. -/
def identitySpecialOrthogonalNorthPoleProductMeasurableTransition
    (n : ℕ)
    (x : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalMappedTangent (n + 1) :=
  identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
    (identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition n x)

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductMeasurableTransition
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductMeasurableTransition n) :=
  (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
    ).continuous.measurable.comp
      (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition
        n)

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableTransition_eq
    (n : ℕ)
    (x : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n))
    (hx :
      x ∈ identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalNorthPoleProductMeasurableTransition n x =
      identitySpecialOrthogonalNorthPoleProductTransition n x := by
  rw [
    identitySpecialOrthogonalNorthPoleProductMeasurableTransition,
    identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition_eq
      n x hx,
    identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv_squareMap]

/-- On the exact pulled-back source, the measurable actual product group's
higher identity-chart coordinate is the original product transition. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHigherCoordinate_measurableLowerGroup_eq
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hp :
      p ∈
        identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
          n) :
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate n
        (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n p) =
      identitySpecialOrthogonalNorthPoleProductTransition n
        (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
          n p) := by
  let ps :
      identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n :=
    ⟨p, hp⟩
  let d := identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource n ps
  have hd :
      d ∈
        identitySpecialOrthogonalNorthPoleProductHigherChartSourceSubtypeSet
          n :=
    identitySpecialOrthogonalNorthPoleProductLowerDomainOnSource_mem_higherChartSource
      n ps
  have hg :
      identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource n ps ∈
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).source := by
    exact
      (identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource_mem_higherChartGroupSet
        n ps).2
  rw [
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup_eq n p hp,
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate_eq
      n
      (identitySpecialOrthogonalNorthPoleProductLowerGroupOnSource n ps)
      hg]
  symm
  exact
    identitySpecialOrthogonalNorthPoleProductTransition_eq_identityChart
      n d hd

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableTransition_lowerSourceAmbient_eq
    (n : ℕ)
    (p :
      specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hp :
      p ∈
        identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
          n) :
    identitySpecialOrthogonalNorthPoleProductMeasurableTransition n
        (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
          n p) =
      identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate n
        (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup
          n p) := by
  rw [
    identitySpecialOrthogonalNorthPoleProductMeasurableTransition_eq
      n
      (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
        n p)
      hp,
    identitySpecialOrthogonalNorthPoleProductHigherCoordinate_measurableLowerGroup_eq
      n p hp]

/-- The lower differential/sphere product restricted to the exact source,
named to keep later measure interfaces compact. -/
def identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
    (n : ℕ) :
    Measure
      (specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereMeasure
    n).restrict
      (identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n)

/-- The measurable transition after the lower source coordinate. -/
def identitySpecialOrthogonalNorthPoleProductTransitionOnLowerSource
    (n : ℕ) :
    (specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) →
      identitySpecialOrthogonalMappedTangent (n + 1) :=
  identitySpecialOrthogonalNorthPoleProductMeasurableTransition n ∘
    identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate n

/-- The higher measurable coordinate after the actual group product. -/
def identitySpecialOrthogonalNorthPoleProductHigherCoordinateOnLowerSource
    (n : ℕ) :
    (specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) →
      identitySpecialOrthogonalMappedTangent (n + 1) :=
  identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate n ∘
    identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n

end PositiveDefiniteIntegralLattice
