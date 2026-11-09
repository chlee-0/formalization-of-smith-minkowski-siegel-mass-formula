import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductWeightedProductMeasure
import SMSFormula.SpecialOrthogonalRealDifferentialInvariance

/-!
# Higher differential target for the identity north-pole product

This module identifies the target-density-weighted higher identity-chart
coordinate measure with the forward chart image of the invariant differential
measure restricted to the exact higher product chart set.

The source product measure is not identified here, and no fiber
disintegration or rank recurrence is asserted.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory Set

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductHigherTargetDifferentialMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductHigherTargetDifferentialBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductHigherTargetDifferentialGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductHigherTargetDifferentialGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The exact higher group set, viewed inside the source subtype of the
higher identity chart. -/
def identitySpecialOrthogonalNorthPoleProductHigherChartGroupWithinSource
    (n : ℕ) :
    Set
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).source :=
  Subtype.val ⁻¹'
    identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n

/-- The exact product-transition target, viewed inside the target subtype of
the higher identity chart. -/
def identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
    (n : ℕ) :
    Set
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).target :=
  Subtype.val ⁻¹'
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n

theorem
    measurableSet_identitySpecialOrthogonalNorthPoleProductHigherChartGroupWithinSource
    (n : ℕ) :
    MeasurableSet
      (identitySpecialOrthogonalNorthPoleProductHigherChartGroupWithinSource
        n) :=
  (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet_isOpen n
    ).measurableSet.preimage continuous_subtype_val.measurable

theorem
    measurableSet_identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
    (n : ℕ) :
    MeasurableSet
      (identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
        n) :=
  (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet_isOpen n
    ).measurableSet.preimage continuous_subtype_val.measurable

/-- The rational higher target-coordinate Haar is the coordinate determinant
measure used by the invariant real chart. -/
theorem
    identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure_eq
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
        n =
      Matrix.skewAdjointRealCoordinateDetMeasure
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) 0 := by
  rw [Matrix.skewAdjointRealCoordinateDetMeasure_eq_addHaar,
    Matrix.skewAdjointRealBasisHaarMeasure]
  rfl

/-- The higher identity-chart homeomorphism carries the exact group subset to
the exact transition-target subset. -/
theorem
    preimage_identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
    (n : ℕ) :
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).toHomeomorphSourceTarget ⁻¹'
        identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
          n =
      identitySpecialOrthogonalNorthPoleProductHigherChartGroupWithinSource
        n := by
  ext x
  constructor
  · rintro ⟨g, hg, hgx⟩
    have hgsource :
        g ∈
          (specialFormPreservingSmoothRealIdentityChart
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
            identityRationalForm_isSymm
            identityRationalForm_det_ne_zero).source :=
      inter_subset_right hg
    have hsub :
        (⟨g, hgsource⟩ :
          (specialFormPreservingSmoothRealIdentityChart
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
            identityRationalForm_isSymm
            identityRationalForm_det_ne_zero).source) = x := by
      apply
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero
          ).toHomeomorphSourceTarget.injective
      exact Subtype.ext hgx
    exact hsub ▸ hg
  · intro hx
    exact ⟨x.1, hx, rfl⟩

/-- Returning the restricted higher chart-target density measure to the
ambient tangent carrier gives exactly the transition target-coordinate Haar
weighted by the ambient target density. -/
theorem
    map_restrict_identitySpecialOrthogonalNorthPoleProductHigherChartTargetDensityMeasure
    (n : ℕ) :
    Measure.map Subtype.val
        ((specialFormPreservingSmoothRealChartTargetDensityMeasure
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero 1).restrict
            (identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
              n)) =
      ((identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
        n).restrict
          (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
        ).withDensity
          (identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity n) := by
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let i : I.target → identitySpecialOrthogonalMappedTangent (n + 1) :=
    Subtype.val
  let ν :=
    Matrix.skewAdjointRealCoordinateDetMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) 0
  let B :=
    identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget n
  let T :=
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n
  let μ := (Measure.comap i ν).restrict B
  let f :=
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero 1
  let g :=
    identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity n
  have hB : MeasurableSet B :=
    measurableSet_identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
      n
  have hT : MeasurableSet T :=
    (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet_isOpen n
      ).measurableSet
  have hsub : T ⊆ I.target :=
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet_subset_identityChartTarget
      n
  have hfg : f =ᵐ[μ] g ∘ i := by
    filter_upwards [MeasureTheory.ae_restrict_mem hB] with z hz
    change f z =
      identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity n z.1
    rw [identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity_eq
      n z.1 hz]
    apply congrArg f
    apply Subtype.ext
    rfl
  have hmap : Measure.map i μ = ν.restrict T := by
    calc
      Measure.map i μ =
          (Measure.map i (Measure.comap i ν)).restrict T := by
        symm
        exact Measure.restrict_map continuous_subtype_val.measurable hT
      _ = (ν.restrict I.target).restrict T := by
        rw [map_comap_subtype_coe I.open_target.measurableSet]
      _ = ν.restrict T := by
        rw [Measure.restrict_restrict hT]
        congr 1
        exact Set.inter_eq_left.mpr hsub
  rw [
    identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure_eq]
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure]
  change Measure.map i (((Measure.comap i ν).withDensity f).restrict B) =
    (ν.restrict T).withDensity g
  rw [restrict_withDensity hB]
  change Measure.map i (μ.withDensity f) = (ν.restrict T).withDensity g
  calc
    Measure.map i (μ.withDensity f) =
        Measure.map i (μ.withDensity (g ∘ i)) := by
      exact congrArg (Measure.map i) (withDensity_congr_ae hfg)
    _ = (Measure.map i μ).withDensity g :=
      map_withDensity_comp_of_measurable i μ g
        continuous_subtype_val.measurable
        (measurable_identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity
          n)
    _ = (ν.restrict T).withDensity g := by rw [hmap]

/-- A globally measurable extension of the higher identity-chart coordinate
map. Its values off the exact chart source are irrelevant below. -/
def identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
    (n : ℕ)
    (q :
      specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ))) :
    identitySpecialOrthogonalMappedTangent (n + 1) :=
  Function.extend
    (Subtype.val :
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).source →
      specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ)))
    (fun x =>
      ((specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).toHomeomorphSourceTarget x).1)
    (fun _ => 0) q

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
        n) := by
  exact
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).open_source.measurableSet
      ).measurable_extend
        (continuous_subtype_val.measurable.comp
          (specialFormPreservingSmoothRealIdentityChart
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
            identityRationalForm_isSymm
            identityRationalForm_det_ne_zero
            ).toHomeomorphSourceTarget.continuous.measurable)
        measurable_const

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate_eq
    (n : ℕ)
    (q :
      specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ)))
    (hq :
      q ∈
        (specialFormPreservingSmoothRealIdentityChart
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).source) :
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
        n q =
      specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero q := by
  exact
    Function.Injective.extend_apply Subtype.val_injective _ _
      ⟨q, hq⟩

/-- Restricting the invariant higher differential measure to the exact group
set recovers the corresponding restriction of the identity-chart source
density measure. -/
theorem
    restrict_identitySpecialOrthogonalNorthPoleProductHigherDifferentialMeasure
    (n : ℕ) :
    (specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n) =
      Measure.map Subtype.val
        ((specialFormPreservingSmoothRealChartSourceDensityMeasure
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero 1).restrict
            (identitySpecialOrthogonalNorthPoleProductHigherChartGroupWithinSource
              n)) := by
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let μ :=
    specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let σ :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero 1
  let G :=
    identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n
  let S :=
    identitySpecialOrthogonalNorthPoleProductHigherChartGroupWithinSource n
  have hG : MeasurableSet G :=
    (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet_isOpen n
      ).measurableSet
  have hsub : G ⊆ I.source :=
    inter_subset_right
  calc
    μ.restrict G = (μ.restrict I.source).restrict G := by
      symm
      rw [Measure.restrict_restrict hG, Set.inter_eq_left.mpr hsub]
    _ =
        (specialFormPreservingSmoothRealChartAmbientDensityMeasure
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero 1).restrict G := by
      rw [restrict_specialFormPreservingSmoothRealDifferentialMeasure_source]
    _ = Measure.map Subtype.val (σ.restrict S) := by
      exact Measure.restrict_map continuous_subtype_val.measurable hG

/-- Forward higher identity-chart coordinates carry the restricted invariant
differential measure to the restricted chart-target density measure. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate_restrict_differential
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n)
        ((specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet n)) =
      Measure.map Subtype.val
        ((specialFormPreservingSmoothRealChartTargetDensityMeasure
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero 1).restrict
            (identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
              n)) := by
  let I :=
    specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let Φ :=
    identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
      n
  let σ :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero 1
  let τ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero 1
  let S :=
    identitySpecialOrthogonalNorthPoleProductHigherChartGroupWithinSource n
  let B :=
    identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget n
  have hB : MeasurableSet B :=
    measurableSet_identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
      n
  have hpre : I.toHomeomorphSourceTarget ⁻¹' B = S :=
    preimage_identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
      n
  have hchart :
      Measure.map I.toHomeomorphSourceTarget (σ.restrict S) =
        τ.restrict B := by
    calc
      Measure.map I.toHomeomorphSourceTarget (σ.restrict S) =
          Measure.map I.toHomeomorphSourceTarget
            (σ.restrict (I.toHomeomorphSourceTarget ⁻¹' B)) := by
        rw [hpre]
      _ = (Measure.map I.toHomeomorphSourceTarget σ).restrict B := by
        rw [Measure.restrict_map
          I.toHomeomorphSourceTarget.continuous.measurable hB]
      _ = τ.restrict B := by
        rw [map_specialFormPreservingSmoothRealChartSourceDensityMeasure]
  rw [
    restrict_identitySpecialOrthogonalNorthPoleProductHigherDifferentialMeasure]
  calc
    Measure.map Φ (Measure.map Subtype.val (σ.restrict S)) =
        Measure.map (Φ ∘ Subtype.val) (σ.restrict S) := by
      rw [Measure.map_map
        (measurable_identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n)
        continuous_subtype_val.measurable]
    _ = Measure.map
          (Subtype.val ∘ I.toHomeomorphSourceTarget) (σ.restrict S) := by
      apply Measure.map_congr
      filter_upwards [] with x
      exact
        identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate_eq
          n x.1 x.2
    _ = Measure.map Subtype.val
          (Measure.map I.toHomeomorphSourceTarget (σ.restrict S)) := by
      symm
      rw [Measure.map_map continuous_subtype_val.measurable
        I.toHomeomorphSourceTarget.continuous.measurable]
    _ = Measure.map Subtype.val (τ.restrict B) := by rw [hchart]

/-- The exact higher target-coordinate measure in the weighted product
transition is the forward higher identity-chart image of the rank-`n+1`
invariant mapped differential measure on its exact group set. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHigherTargetWeightedMeasure_eq_map_restrict_differential
    (n : ℕ) :
    ((identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
      n).restrict
        (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
      ).withDensity
        (identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity n) =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n)
        ((specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
              n)) := by
  calc
    ((identitySpecialOrthogonalNorthPoleProductTransitionTargetCoordinateMeasure
      n).restrict
        (identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
      ).withDensity
        (identitySpecialOrthogonalNorthPoleProductAmbientTargetDensity n) =
      Measure.map Subtype.val
        ((specialFormPreservingSmoothRealChartTargetDensityMeasure
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero 1).restrict
            (identitySpecialOrthogonalNorthPoleProductTransitionTargetWithinTarget
              n)) := by
        symm
        exact
          map_restrict_identitySpecialOrthogonalNorthPoleProductHigherChartTargetDensityMeasure
            n
    _ =
      Measure.map
        (identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n)
        ((specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero).restrict
            (identitySpecialOrthogonalNorthPoleProductHigherChartGroupSet
              n)) := by
        symm
        exact
          map_identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate_restrict_differential
            n

end PositiveDefiniteIntegralLattice
