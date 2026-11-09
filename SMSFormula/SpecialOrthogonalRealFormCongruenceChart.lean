import SMSFormula.SpecialOrthogonalRealDiagonalScaling

/-!
# Transported real charts for explicit real form congruences

This module isolates the first chart layer which does not require the change
of basis to be rational.  The source and target forms remain rational, so
their tangent coordinate measures use the fixed rational differential
bases.  The congruence itself is supplied by a real matrix unit.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realFormCongruenceChartGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realFormCongruenceChartGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance realFormCongruenceChartTangentMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realFormCongruenceChartTangentBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- An explicit real congruence between two rational form matrices. -/
structure SpecialOrthogonalRealFormCongruenceData
    (F F' : Matrix (Fin n) (Fin n) ℚ) where
  unit : GL (Fin n) ℝ
  congruence :
    (unit : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        F.map (algebraMap ℚ ℝ) *
        (unit : Matrix (Fin n) (Fin n) ℝ) =
      F'.map (algebraMap ℚ ℝ)

namespace SpecialOrthogonalRealFormCongruenceData

/-- The group equivalence induced by an explicit real congruence. -/
def groupEquiv
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ)) ≃ₜ*
      specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ)) :=
  specialFormPreservingRealFormCongruenceContinuousMulEquiv
    (F.map (algebraMap ℚ ℝ)) (F'.map (algebraMap ℚ ℝ))
    c.unit c.congruence

/-- The tangent equivalence induced by an explicit real congruence. -/
def tangentEquiv
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (F'.map (algebraMap ℚ ℝ))).toSubmodule :=
  Matrix.skewAdjointRealFormCongruenceContinuousLinearEquiv
    (F.map (algebraMap ℚ ℝ)) (F'.map (algebraMap ℚ ℝ))
    c.unit c.congruence

@[simp]
theorem coe_groupEquiv_apply
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    ((c.groupEquiv g).1.1.1 : Matrix (Fin n) (Fin n) ℝ) =
      ((c.unit⁻¹ : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) * g.1.1.1 *
        (c.unit : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

@[simp]
theorem coe_groupEquiv_symm_apply
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (g : specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))) :
    ((c.groupEquiv.symm g).1.1.1 :
      Matrix (Fin n) (Fin n) ℝ) =
      (c.unit : Matrix (Fin n) (Fin n) ℝ) * g.1.1.1 *
        ((c.unit⁻¹ : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) :=
  rfl

@[simp]
theorem coe_tangentEquiv_apply
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (c.tangentEquiv X : Matrix (Fin n) (Fin n) ℝ) =
      ((c.unit : Matrix (Fin n) (Fin n) ℝ)⁻¹) * X.1 *
        (c.unit : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

@[simp]
theorem coe_tangentEquiv_symm_apply
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (Y : (skewAdjointMatricesLieSubalgebra
      (F'.map (algebraMap ℚ ℝ))).toSubmodule) :
    (c.tangentEquiv.symm Y : Matrix (Fin n) (Fin n) ℝ) =
      (c.unit : Matrix (Fin n) (Fin n) ℝ) * Y.1 *
        ((c.unit : Matrix (Fin n) (Fin n) ℝ)⁻¹) :=
  rfl

/-- The determinant comparing the two independently fixed rational tangent
bases across the explicit real congruence. -/
def detScalar
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F') : ℝ :=
  Matrix.skewAdjointRealLinearEquivDetScalar F F' c.tangentEquiv

theorem detScalar_ne_zero
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    c.detScalar ≠ 0 :=
  Matrix.skewAdjointRealLinearEquivDetScalar_ne_zero
    F F' c.tangentEquiv

/-- Tangent coordinate Haar transport for an explicit real congruence. -/
theorem map_tangentCoordinateMeasure
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map c.tangentEquiv
        (Matrix.skewAdjointRealCoordinateDetMeasure F 0) =
      (Real.toNNReal |c.detScalar|)⁻¹ •
        Matrix.skewAdjointRealCoordinateDetMeasure F' 0 :=
  Matrix.map_skewAdjointRealCoordinateDetMeasure_linearEquiv
    F F' c.tangentEquiv

end SpecialOrthogonalRealFormCongruenceData

/-- A rational congruence regarded as explicit real congruence data. This is
the specialization through which the existing rational chart stack can be
refactored without changing its form matrices. -/
def rationalSpecialOrthogonalRealFormCongruenceData
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    SpecialOrthogonalRealFormCongruenceData
      F (Matrix.skewAdjointCongruenceForm F W) where
  unit := rationalMatrixUnitReal W
  congruence := (map_skewAdjointCongruenceForm_real F W).symm

/-- The generic group equivalence specializes extensionally to the
rational group congruence. -/
theorem rationalSpecialOrthogonalRealFormCongruenceData_groupEquiv_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    (rationalSpecialOrthogonalRealFormCongruenceData F W).groupEquiv =
      specialFormPreservingRealCongruenceContinuousMulEquiv F W := by
  ext g i j
  rfl

private def realFormCongruenceHomeomorphInversePreimage
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

/-- The source of the identity chart transported by an explicit real group
congruence. -/
def specialFormPreservingSmoothRealFormCongruenceChartSourceSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set (specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))) :=
  c.groupEquiv.symm ⁻¹'
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).source

/-- The target of the identity chart transported by an explicit real tangent
congruence. -/
def specialFormPreservingSmoothRealFormCongruenceChartTargetSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set ((skewAdjointMatricesLieSubalgebra
      (F'.map (algebraMap ℚ ℝ))).toSubmodule) :=
  c.tangentEquiv.symm ⁻¹'
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).target

abbrev specialFormPreservingSmoothRealFormCongruenceChartSource
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :=
  specialFormPreservingSmoothRealFormCongruenceChartSourceSet
    F F' hF hdet c

abbrev specialFormPreservingSmoothRealFormCongruenceChartTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :=
  specialFormPreservingSmoothRealFormCongruenceChartTargetSet
    F F' hF hdet c

theorem isOpen_specialFormPreservingSmoothRealFormCongruenceChartSourceSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    IsOpen (specialFormPreservingSmoothRealFormCongruenceChartSourceSet
      F F' hF hdet c) :=
  (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_source.preimage
    c.groupEquiv.symm.continuous

theorem isOpen_specialFormPreservingSmoothRealFormCongruenceChartTargetSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    IsOpen (specialFormPreservingSmoothRealFormCongruenceChartTargetSet
      F F' hF hdet c) :=
  (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_target.preimage
    c.tangentEquiv.symm.continuous

/-- Group congruence restricted to the transported source. -/
def specialFormPreservingSmoothRealFormCongruenceChartSourceHomeomorph
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).source ≃ₜ
      specialFormPreservingSmoothRealFormCongruenceChartSource
        F F' hF hdet c :=
  realFormCongruenceHomeomorphInversePreimage c.groupEquiv.toHomeomorph
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).source

/-- Tangent congruence restricted to the transported target. -/
def specialFormPreservingSmoothRealFormCongruenceChartTargetHomeomorph
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).target ≃ₜ
      specialFormPreservingSmoothRealFormCongruenceChartTarget
        F F' hF hdet c :=
  realFormCongruenceHomeomorphInversePreimage c.tangentEquiv.toHomeomorph
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).target

/-- The source identity chart transported through an explicit real
congruence. -/
def specialFormPreservingSmoothRealFormCongruenceChartHomeomorph
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceChartSource
        F F' hF hdet c ≃ₜ
      specialFormPreservingSmoothRealFormCongruenceChartTarget
        F F' hF hdet c :=
  (specialFormPreservingSmoothRealFormCongruenceChartSourceHomeomorph
      F F' hF hdet c).symm.trans
    ((specialFormPreservingSmoothRealIdentityChart
      F hF hdet).toHomeomorphSourceTarget.trans
      (specialFormPreservingSmoothRealFormCongruenceChartTargetHomeomorph
        F F' hF hdet c))

@[simp]
theorem coe_specialFormPreservingSmoothRealFormCongruenceChartHomeomorph_apply
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : specialFormPreservingSmoothRealFormCongruenceChartSource
      F F' hF hdet c) :
    (specialFormPreservingSmoothRealFormCongruenceChartHomeomorph
      F F' hF hdet c x).1 =
      c.tangentEquiv
        (specialFormPreservingSmoothRealIdentityChart F hF hdet
          (c.groupEquiv.symm x.1)) :=
  rfl

@[simp]
theorem coe_specialFormPreservingSmoothRealFormCongruenceChartHomeomorph_symm_apply
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (y : specialFormPreservingSmoothRealFormCongruenceChartTarget
      F F' hF hdet c) :
    ((specialFormPreservingSmoothRealFormCongruenceChartHomeomorph
      F F' hF hdet c).symm y).1 =
      c.groupEquiv
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm
          (c.tangentEquiv.symm y.1)) :=
  rfl

/-- The target coordinate measure at the independently normalized `F'`
scale. -/
def specialFormPreservingSmoothRealFormCongruenceChartTargetCoordinateMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure (specialFormPreservingSmoothRealFormCongruenceChartTarget
      F F' hF hdet c) :=
  Measure.comap Subtype.val
    (Matrix.skewAdjointRealCoordinateDetMeasure F' 0)

/-- The source coordinate measure transported by the group congruence. -/
def specialFormPreservingSmoothRealFormCongruenceChartSourceCoordinateMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure (specialFormPreservingSmoothRealFormCongruenceChartSource
      F F' hF hdet c) :=
  Measure.map
    (specialFormPreservingSmoothRealFormCongruenceChartSourceHomeomorph
      F F' hF hdet c)
    (specialFormPreservingSmoothRealIdentityChartSourceMeasure F hF hdet)

/-- The restricted tangent congruence transports source coordinates with the
explicit reciprocal rational-basis determinant. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceChartTargetCoordinateMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map
        (specialFormPreservingSmoothRealFormCongruenceChartTargetHomeomorph
          F F' hF hdet c)
        (specialFormPreservingSmoothRealIdentityChartTargetMeasure
          F hF hdet) =
      (Real.toNNReal |c.detScalar|)⁻¹ •
        specialFormPreservingSmoothRealFormCongruenceChartTargetCoordinateMeasure
          F F' hF hdet c := by
  let e := c.tangentEquiv
  let er :=
    specialFormPreservingSmoothRealFormCongruenceChartTargetHomeomorph
      F F' hF hdet c
  let s := (specialFormPreservingSmoothRealIdentityChart F hF hdet).target
  let t := specialFormPreservingSmoothRealFormCongruenceChartTargetSet
    F F' hF hdet c
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  let ν := Matrix.skewAdjointRealCoordinateDetMeasure F' 0
  let q : ℝ≥0 := (Real.toNNReal |c.detScalar|)⁻¹
  have hs : MeasurableSet s :=
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_target.measurableSet
  have ht : MeasurableSet t :=
    (isOpen_specialFormPreservingSmoothRealFormCongruenceChartTargetSet
      F F' hF hdet c).measurableSet
  have hpre : e ⁻¹' t = s := by
    ext x
    simp only [Set.mem_preimage, t,
      specialFormPreservingSmoothRealFormCongruenceChartTargetSet,
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
    _ = (q • ν).restrict t := by
      rw [SpecialOrthogonalRealFormCongruenceData.map_tangentCoordinateMeasure]
    _ = q • ν.restrict t := by rw [Measure.restrict_smul]
    _ = q • Measure.map Subtype.val (Measure.comap Subtype.val ν) := by
      rw [map_comap_subtype_coe ht]
    _ = Measure.map Subtype.val (q • Measure.comap Subtype.val ν) := by
      rw [Measure.map_smul]

/-- The full transported chart carries source coordinates to target
coordinates with the same explicit determinant. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceChartSourceCoordinateMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map
        (specialFormPreservingSmoothRealFormCongruenceChartHomeomorph
          F F' hF hdet c)
        (specialFormPreservingSmoothRealFormCongruenceChartSourceCoordinateMeasure
          F F' hF hdet c) =
      (Real.toNNReal |c.detScalar|)⁻¹ •
        specialFormPreservingSmoothRealFormCongruenceChartTargetCoordinateMeasure
          F F' hF hdet c := by
  let es :=
    specialFormPreservingSmoothRealFormCongruenceChartSourceHomeomorph
      F F' hF hdet c
  let C := (specialFormPreservingSmoothRealIdentityChart
    F hF hdet).toHomeomorphSourceTarget
  let et :=
    specialFormPreservingSmoothRealFormCongruenceChartTargetHomeomorph
      F F' hF hdet c
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
    _ = (Real.toNNReal |c.detScalar|)⁻¹ •
        specialFormPreservingSmoothRealFormCongruenceChartTargetCoordinateMeasure
          F F' hF hdet c :=
      map_specialFormPreservingSmoothRealFormCongruenceChartTargetCoordinateMeasure
        F F' hF hdet c

/-- The explicit real congruence from a positive rational diagonal form to
the identity form. -/
def positiveDiagonalRealFormCongruenceData
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    SpecialOrthogonalRealFormCongruenceData (Matrix.diagonal d) 1 where
  unit := positiveDiagonalRealScalingUnit d hd
  congruence := by
    simpa using positiveDiagonalRealScaling_congruence d hd

/-- The generic explicit-congruence determinant specializes to the
positive-diagonal tangent determinant. -/
theorem positiveDiagonalRealFormCongruenceData_detScalar
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    (positiveDiagonalRealFormCongruenceData d hd).detScalar =
      positiveDiagonalSkewAdjointDetScalar d hd :=
  rfl

/-- A positive rational diagonal form is symmetric. -/
theorem positiveDiagonalForm_isSymm
    (d : Fin n → ℚ) :
    (Matrix.diagonal d).IsSymm := by
  simp [Matrix.IsSymm]

/-- A positive rational diagonal form is nonsingular. -/
theorem positiveDiagonalForm_det_ne_zero
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    (Matrix.diagonal d).det ≠ 0 := by
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (hd i)

/-- The positive-diagonal transported chart has the expected coordinate
measure scale relative to the independently normalized identity model. -/
theorem map_positiveDiagonalSmoothRealFormCongruenceChartSourceCoordinateMeasure
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    Measure.map
        (specialFormPreservingSmoothRealFormCongruenceChartHomeomorph
          (Matrix.diagonal d) 1
          (positiveDiagonalForm_isSymm d)
          (positiveDiagonalForm_det_ne_zero d hd)
          (positiveDiagonalRealFormCongruenceData d hd))
        (specialFormPreservingSmoothRealFormCongruenceChartSourceCoordinateMeasure
          (Matrix.diagonal d) 1
          (positiveDiagonalForm_isSymm d)
          (positiveDiagonalForm_det_ne_zero d hd)
          (positiveDiagonalRealFormCongruenceData d hd)) =
      (Real.toNNReal
        |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹ •
        specialFormPreservingSmoothRealFormCongruenceChartTargetCoordinateMeasure
          (Matrix.diagonal d) 1
          (positiveDiagonalForm_isSymm d)
          (positiveDiagonalForm_det_ne_zero d hd)
          (positiveDiagonalRealFormCongruenceData d hd) := by
    rw [← positiveDiagonalRealFormCongruenceData_detScalar d hd]
    exact
      map_specialFormPreservingSmoothRealFormCongruenceChartSourceCoordinateMeasure
        (Matrix.diagonal d) 1
        (positiveDiagonalForm_isSymm d)
        (positiveDiagonalForm_det_ne_zero d hd)
        (positiveDiagonalRealFormCongruenceData d hd)

end PositiveDefiniteIntegralLattice
