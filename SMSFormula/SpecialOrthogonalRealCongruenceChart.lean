import SMSFormula.SpecialOrthogonalRealCongruence

/-!
# Transported real charts under rational congruence

For `F' = Wᵀ F W`, this module transports the fixed identity chart of
`SO(F)(ℝ)` through the continuous group conjugation and tangent congruence
equivalences. The resulting exact source and target are open, and the
transported chart has explicit forward and inverse formulas.

The transported chart is kept separate from the identity chart chosen
independently for `F'`. No equality of those chart domains is asserted.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private def homeomorphInversePreimage
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (s : Set α) :
    s ≃ₜ (e.symm ⁻¹' s) where
  toFun x := ⟨e x.1, by
    change e.symm (e x.1) ∈ s
    rw [e.symm_apply_apply]
    exact x.2⟩
  invFun y := ⟨e.symm y.1, y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact e.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact e.symm.continuous.comp continuous_subtype_val

@[simp]
private theorem coe_homeomorphInversePreimage_apply
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (s : Set α) (x : s) :
    (homeomorphInversePreimage e s x).1 = e x.1 :=
  rfl

@[simp]
private theorem coe_homeomorphInversePreimage_symm_apply
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (s : Set α) (y : e.symm ⁻¹' s) :
    ((homeomorphInversePreimage e s).symm y).1 = e.symm y.1 :=
  rfl

private theorem map_withDensity_homeomorph
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] (e : α ≃ₜ β) (μ : Measure α)
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (fun y ↦ f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  change
    (∫⁻ x in e ⁻¹' s, f x ∂μ) =
      ∫⁻ y in s, (f ∘ e.symm) y ∂Measure.map e μ
  rw [setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp

local instance realCongruenceChartGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realCongruenceChartGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance realCongruenceChartTangentMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceChartTangentBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The image of the source identity-chart domain, expressed as an exact
preimage under inverse group congruence. -/
def specialFormPreservingSmoothRealCongruenceChartSourceSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set (specialFormPreservingMatrixSubgroup
      ((Matrix.skewAdjointCongruenceForm F W).map (algebraMap ℚ ℝ))) :=
  (specialFormPreservingRealCongruenceContinuousMulEquiv F W).symm ⁻¹'
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).source

/-- The image of the source identity-chart target, expressed as an exact
preimage under inverse tangent congruence. -/
def specialFormPreservingSmoothRealCongruenceChartTargetSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule :=
  (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm ⁻¹'
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).target

/-- The exact transported source subtype. -/
abbrev specialFormPreservingSmoothRealCongruenceChartSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :=
  specialFormPreservingSmoothRealCongruenceChartSourceSet F hF hdet W

/-- The exact transported target subtype. -/
abbrev specialFormPreservingSmoothRealCongruenceChartTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :=
  specialFormPreservingSmoothRealCongruenceChartTargetSet F hF hdet W

/-- The transported group-chart source is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruenceChartSourceSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    IsOpen (specialFormPreservingSmoothRealCongruenceChartSourceSet
      F hF hdet W) :=
  (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_source.preimage
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).symm.continuous

/-- The transported tangent-coordinate target is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruenceChartTargetSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    IsOpen (specialFormPreservingSmoothRealCongruenceChartTargetSet
      F hF hdet W) :=
  (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_target.preimage
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm.continuous

/-- Restriction of group congruence to the exact transported chart source. -/
def specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).source ≃ₜ
      specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W :=
  homeomorphInversePreimage
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).source

/-- Restriction of tangent congruence to the exact transported chart target. -/
def specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).target ≃ₜ
      specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W :=
  homeomorphInversePreimage
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).toHomeomorph
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).target

@[simp]
theorem coe_specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (specialFormPreservingSmoothRealIdentityChart F hF hdet).source) :
    (specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
      F hF hdet W x).1 =
      specialFormPreservingRealCongruenceContinuousMulEquiv F W x.1 :=
  rfl

@[simp]
theorem coe_specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : specialFormPreservingSmoothRealCongruenceChartSource
      F hF hdet W) :
    ((specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
      F hF hdet W).symm x).1 =
      (specialFormPreservingRealCongruenceContinuousMulEquiv F W).symm x.1 :=
  rfl

@[simp]
theorem coe_specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (specialFormPreservingSmoothRealIdentityChart F hF hdet).target) :
    (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
      F hF hdet W x).1 =
      Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W x.1 :=
  rfl

@[simp]
theorem coe_specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : specialFormPreservingSmoothRealCongruenceChartTarget
      F hF hdet W) :
    ((specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
      F hF hdet W).symm x).1 =
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm x.1 :=
  rfl

/-- The exact transported cross-form chart. -/
def specialFormPreservingSmoothRealCongruenceChartHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W ≃ₜ
      specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W :=
  (specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
      F hF hdet W).symm.trans
    ((specialFormPreservingSmoothRealIdentityChart
      F hF hdet).toHomeomorphSourceTarget.trans
      (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
        F hF hdet W))

/-- The transported chart is group inverse-congruence, followed by the
source chart and tangent congruence. -/
theorem coe_specialFormPreservingSmoothRealCongruenceChartHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W) :
    (specialFormPreservingSmoothRealCongruenceChartHomeomorph
      F hF hdet W x).1 =
      Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
        (specialFormPreservingSmoothRealIdentityChart F hF hdet
          ((specialFormPreservingRealCongruenceContinuousMulEquiv
            F W).symm x.1)) := by
  rfl

/-- The inverse transported chart is inverse tangent congruence, followed by
the source inverse chart and group congruence. -/
theorem coe_specialFormPreservingSmoothRealCongruenceChartHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
      F hF hdet W).symm y).1 =
      specialFormPreservingRealCongruenceContinuousMulEquiv F W
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm
          ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
            F W).symm y.1)) := by
  rfl

/-- The normalized target-coordinate measure on the transported tangent
domain, at the independently fixed target-form scale. -/
def specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure
      (specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :=
  Measure.comap Subtype.val
    (Matrix.skewAdjointRealCoordinateDetMeasure
      (Matrix.skewAdjointCongruenceForm F W) 0)

/-- The unweighted source-coordinate measure transported through group
congruence to the exact cross-form chart source. -/
def specialFormPreservingSmoothRealCongruenceChartSourceCoordinateMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure
      (specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W) :=
  Measure.map
    (specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
      F hF hdet W)
    (specialFormPreservingSmoothRealIdentityChartSourceMeasure F hF hdet)

/-- Inverse group congruence recovers the unweighted source-coordinate
measure. -/
theorem map_specialFormPreservingSmoothRealCongruenceChartSourceCoordinateMeasure_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
          F hF hdet W).symm
        (specialFormPreservingSmoothRealCongruenceChartSourceCoordinateMeasure
          F hF hdet W) =
      specialFormPreservingSmoothRealIdentityChartSourceMeasure F hF hdet := by
  rw [specialFormPreservingSmoothRealCongruenceChartSourceCoordinateMeasure]
  exact MeasurableEquiv.map_symm_map
    (specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
      F hF hdet W).toMeasurableEquiv

/-- Tangent congruence transports the source identity-chart coordinate
measure to the exact transported target by the reciprocal comparison
determinant. -/
theorem map_specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
          F hF hdet W)
        (specialFormPreservingSmoothRealIdentityChartTargetMeasure
          F hF hdet) =
      (Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure
          F hF hdet W := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  let er := specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
    F hF hdet W
  let s := (specialFormPreservingSmoothRealIdentityChart F hF hdet).target
  let t := specialFormPreservingSmoothRealCongruenceChartTargetSet F hF hdet W
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  let ν := Matrix.skewAdjointRealCoordinateDetMeasure F' 0
  let c : ℝ≥0 := (Real.toNNReal
    |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹
  have hs : MeasurableSet s :=
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_target.measurableSet
  have ht : MeasurableSet t :=
    (isOpen_specialFormPreservingSmoothRealCongruenceChartTargetSet
      F hF hdet W).measurableSet
  have hpre : e ⁻¹' t = s := by
    ext x
    simp only [Set.mem_preimage, t,
      specialFormPreservingSmoothRealCongruenceChartTargetSet,
      e, s]
    rw [e.symm_apply_apply]
  apply (MeasurableEmbedding.subtype_coe ht).map_injective
  calc
    Measure.map Subtype.val
        (Measure.map er (Measure.comap Subtype.val μ)) =
        Measure.map e
          (Measure.map Subtype.val (Measure.comap Subtype.val μ)) := by
      rw [Measure.map_map continuous_subtype_val.measurable er.measurable,
        Measure.map_map e.continuous.measurable
          continuous_subtype_val.measurable]
      congr 1
    _ = Measure.map e (μ.restrict s) := by
      rw [map_comap_subtype_coe hs]
    _ = (Measure.map e μ).restrict t := by
      symm
      rw [Measure.restrict_map e.continuous.measurable ht, hpre]
    _ = (c • ν).restrict t := by
      rw [Matrix.map_skewAdjointRealCoordinateDetMeasure_congruence]
    _ = c • ν.restrict t := by rw [Measure.restrict_smul]
    _ = c • Measure.map Subtype.val (Measure.comap Subtype.val ν) := by
      rw [map_comap_subtype_coe ht]
    _ = Measure.map Subtype.val (c • Measure.comap Subtype.val ν) := by
      rw [Measure.map_smul]

/-- Inverse tangent congruence recovers the target-coordinate
measure from the determinant-scaled transported measure. -/
theorem map_specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
          F hF hdet W).symm
        ((Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
          specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure
            F hF hdet W) =
      specialFormPreservingSmoothRealIdentityChartTargetMeasure
        F hF hdet := by
  rw [←
    map_specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure]
  exact MeasurableEquiv.map_symm_map
    (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
      F hF hdet W).toMeasurableEquiv

/-- The exact transported chart sends its unweighted source-coordinate
measure to the target-form coordinate measure with the reciprocal tangent
comparison determinant. -/
theorem map_specialFormPreservingSmoothRealCongruenceChartSourceCoordinateMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceChartHomeomorph
          F hF hdet W)
        (specialFormPreservingSmoothRealCongruenceChartSourceCoordinateMeasure
          F hF hdet W) =
      (Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure
          F hF hdet W := by
  let es := specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
    F hF hdet W
  let C := (specialFormPreservingSmoothRealIdentityChart
    F hF hdet).toHomeomorphSourceTarget
  let et := specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
    F hF hdet W
  let μ := specialFormPreservingSmoothRealIdentityChartSourceMeasure
    F hF hdet
  calc
    Measure.map (es.symm.trans (C.trans et)) (Measure.map es μ) =
        Measure.map (et ∘ C) μ := by
      rw [Measure.map_map (es.symm.trans (C.trans et)).measurable es.measurable]
      congr 1
      funext x
      simp
    _ = Measure.map et (Measure.map C μ) := by
      rw [Measure.map_map et.measurable C.measurable]
    _ = Measure.map et
        (specialFormPreservingSmoothRealIdentityChartTargetMeasure
          F hF hdet) := by
      rw [map_specialFormPreservingSmoothRealIdentityChartSourceMeasure]
    _ = (Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure
          F hF hdet W :=
      map_specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure
        F hF hdet W

/-- The source-form invariant differential density, transported to the exact
target tangent coordinates. -/
def specialFormPreservingSmoothRealCongruenceChartTargetDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget
      F hF hdet W) : ℝ≥0∞ :=
  specialFormPreservingSmoothRealChartCoordinateDensityENNReal
    F hF hdet 1
    ((specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
      F hF hdet W).symm y)

/-- The transported differential density is continuous. -/
theorem continuous_specialFormPreservingSmoothRealCongruenceChartTargetDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Continuous
      (specialFormPreservingSmoothRealCongruenceChartTargetDensityENNReal
        F hF hdet W) :=
  (continuous_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
    F hF hdet 1).comp
      (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
        F hF hdet W).symm.continuous

/-- The target differential measure in the transported cross-form chart,
expressed at the independently fixed target-form coordinate scale. -/
def specialFormPreservingSmoothRealCongruenceChartTargetDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure
      (specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :=
  (specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure
    F hF hdet W).withDensity
      (specialFormPreservingSmoothRealCongruenceChartTargetDensityENNReal
        F hF hdet W)

/-- The source invariant differential measure transported through group
congruence to the exact cross-form chart source. -/
def specialFormPreservingSmoothRealCongruenceChartSourceDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure
      (specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W) :=
  Measure.map
    (specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
      F hF hdet W)
    (specialFormPreservingSmoothRealChartSourceDensityMeasure
      F hF hdet 1)

/-- Tangent congruence transports the source invariant differential density
to the cross-form target with the reciprocal basis-comparison determinant. -/
theorem map_specialFormPreservingSmoothRealCongruenceChartTargetDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
          F hF hdet W)
        (specialFormPreservingSmoothRealChartTargetDensityMeasure
          F hF hdet 1) =
      (Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        specialFormPreservingSmoothRealCongruenceChartTargetDensityMeasure
          F hF hdet W := by
  let e := specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
    F hF hdet W
  let μ := specialFormPreservingSmoothRealIdentityChartTargetMeasure
    F hF hdet
  let f := specialFormPreservingSmoothRealChartCoordinateDensityENNReal
    F hF hdet 1
  let c : ℝ≥0 := (Real.toNNReal
    |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure]
  change Measure.map e (μ.withDensity f) =
    c •
      (specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure
        F hF hdet W).withDensity (fun y ↦ f (e.symm y))
  rw [map_withDensity_homeomorph e μ f
      (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet 1)]
  rw [map_specialFormPreservingSmoothRealCongruenceChartTargetCoordinateMeasure]
  ext s hs
  simp [withDensity_apply, hs, c]

/-- The exact transported cross-form chart carries its transported invariant
differential measure to the target density measure with the same explicit
reciprocal tangent determinant. -/
theorem map_specialFormPreservingSmoothRealCongruenceChartSourceDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceChartHomeomorph
          F hF hdet W)
        (specialFormPreservingSmoothRealCongruenceChartSourceDensityMeasure
          F hF hdet W) =
      (Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        specialFormPreservingSmoothRealCongruenceChartTargetDensityMeasure
          F hF hdet W := by
  let es := specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
    F hF hdet W
  let C := (specialFormPreservingSmoothRealIdentityChart
    F hF hdet).toHomeomorphSourceTarget
  let et := specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
    F hF hdet W
  let μ := specialFormPreservingSmoothRealChartSourceDensityMeasure
    F hF hdet 1
  calc
    Measure.map (es.symm.trans (C.trans et)) (Measure.map es μ) =
        Measure.map (et ∘ C) μ := by
      rw [Measure.map_map (es.symm.trans (C.trans et)).measurable es.measurable]
      congr 1
      funext x
      simp
    _ = Measure.map et (Measure.map C μ) := by
      rw [Measure.map_map et.measurable C.measurable]
    _ = Measure.map et
        (specialFormPreservingSmoothRealChartTargetDensityMeasure
          F hF hdet 1) := by
      rw [map_specialFormPreservingSmoothRealChartSourceDensityMeasure]
    _ = (Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        specialFormPreservingSmoothRealCongruenceChartTargetDensityMeasure
          F hF hdet W :=
      map_specialFormPreservingSmoothRealCongruenceChartTargetDensityMeasure
        F hF hdet W

end PositiveDefiniteIntegralLattice
