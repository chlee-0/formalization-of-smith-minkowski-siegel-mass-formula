import SMSFormula.RationalSpecialOrthogonalAdelicTangentCoordinate
import Mathlib.RingTheory.Flat.Equalizer

/-!
# The full-adelic skew-adjoint tangent carrier

This file proves that scalar extension of the rational skew-adjoint tangent
space to the full rational adele ring is the entire skew-adjoint matrix
carrier.  The key input is flatness of the rational adeles over `ℚ`, which
makes base change preserve the defining kernel.

The exact coordinate-range normalization is then transported to the full
skew-adjoint carrier.  Its measurable structure remains explicitly
coordinate-transported; no measure on the adelic special orthogonal group or
Tamagawa-number theorem is introduced.
-/

noncomputable section

open MeasureTheory Set
open scoped Matrix TensorProduct ENNReal

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable instance rationalAdeleFlat :
    Module.Flat ℚ PositiveDefiniteIntegralLattice.RationalAdele :=
  Module.Flat.of_free

/-- The tensor-product matrix equivalence intertwines the base-changed
rational skew-adjoint operator with the adelic skew-adjoint operator. -/
theorem rationalAdeleTensorProductMatrixEquiv_skewAdjointOperator
    (F : Matrix ι ι ℚ)
    (z : PositiveDefiniteIntegralLattice.RationalAdele ⊗[ℚ] Matrix ι ι ℚ) :
    rationalAdeleTensorProductMatrixEquiv
        ((skewAdjointOperator F).baseChange
          PositiveDefiniteIntegralLattice.RationalAdele z) =
      skewAdjointOperator
        (F.map (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele))
        (rationalAdeleTensorProductMatrixEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a X =>
      rw [LinearMap.baseChange_tmul,
        rationalAdeleTensorProductMatrixEquiv_tmul,
        rationalAdeleTensorProductMatrixEquiv_tmul, map_smul,
        skewAdjointOperator_map_rationalAdele]

/-- Matrix coordinates restrict to an equivalence between the kernels of the
base-changed rational and adelic skew-adjoint operators. -/
def rationalAdeleBaseChangedSkewAdjointKernelEquiv
    (F : Matrix ι ι ℚ) :
    LinearMap.ker
        ((skewAdjointOperator F).baseChange
          PositiveDefiniteIntegralLattice.RationalAdele) ≃ₗ[PositiveDefiniteIntegralLattice.RationalAdele]
      LinearMap.ker
        (skewAdjointOperator
          (F.map (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele))) where
  toFun X := ⟨rationalAdeleTensorProductMatrixEquiv X, by
    change skewAdjointOperator
      (F.map (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele))
      (rationalAdeleTensorProductMatrixEquiv X) = 0
    rw [← rationalAdeleTensorProductMatrixEquiv_skewAdjointOperator,
      X.property, map_zero]⟩
  invFun X := ⟨rationalAdeleTensorProductMatrixEquiv.symm X, by
    change (skewAdjointOperator F).baseChange
      PositiveDefiniteIntegralLattice.RationalAdele
      (rationalAdeleTensorProductMatrixEquiv.symm X) = 0
    apply rationalAdeleTensorProductMatrixEquiv.injective
    rw [rationalAdeleTensorProductMatrixEquiv_skewAdjointOperator,
      LinearEquiv.apply_symm_apply, X.property, map_zero]⟩
  left_inv X :=
    Subtype.ext
      (rationalAdeleTensorProductMatrixEquiv.symm_apply_apply
        (X : PositiveDefiniteIntegralLattice.RationalAdele ⊗[ℚ] Matrix ι ι ℚ))
  right_inv X :=
    Subtype.ext
      (rationalAdeleTensorProductMatrixEquiv.apply_symm_apply
        (X : Matrix ι ι PositiveDefiniteIntegralLattice.RationalAdele))
  map_add' X Y :=
    Subtype.ext
      (rationalAdeleTensorProductMatrixEquiv.map_add
        (X : PositiveDefiniteIntegralLattice.RationalAdele ⊗[ℚ] Matrix ι ι ℚ) Y)
  map_smul' a X :=
    Subtype.ext
      (rationalAdeleTensorProductMatrixEquiv.map_smul a
        (X : PositiveDefiniteIntegralLattice.RationalAdele ⊗[ℚ] Matrix ι ι ℚ))

@[simp]
theorem coe_rationalAdeleBaseChangedSkewAdjointKernelEquiv_apply
    (F : Matrix ι ι ℚ)
    (X : LinearMap.ker
      ((skewAdjointOperator F).baseChange
        PositiveDefiniteIntegralLattice.RationalAdele)) :
    (rationalAdeleBaseChangedSkewAdjointKernelEquiv F X :
      Matrix ι ι PositiveDefiniteIntegralLattice.RationalAdele) =
      rationalAdeleTensorProductMatrixEquiv X :=
  rfl

/-- Flat scalar extension from `ℚ` to the full rational adeles commutes with
the skew-adjoint matrix carrier. -/
def rationalAdeleSkewAdjointScalarExtensionEquiv
    (F : Matrix ι ι ℚ) :
    PositiveDefiniteIntegralLattice.RationalAdele ⊗[ℚ]
        skewAdjointMatricesLieSubalgebra F ≃ₗ[PositiveDefiniteIntegralLattice.RationalAdele]
      skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele)) :=
  LinearEquiv.baseChange ℚ PositiveDefiniteIntegralLattice.RationalAdele _ _
      (skewAdjointOperatorKerEquiv F).symm ≪≫ₗ
    LinearMap.tensorKerEquiv PositiveDefiniteIntegralLattice.RationalAdele
      PositiveDefiniteIntegralLattice.RationalAdele (skewAdjointOperator F) ≪≫ₗ
    rationalAdeleBaseChangedSkewAdjointKernelEquiv F ≪≫ₗ
    skewAdjointOperatorKerEquiv
      (F.map (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele))

@[simp]
theorem coe_rationalAdeleSkewAdjointScalarExtensionEquiv_tmul
    (F : Matrix ι ι ℚ) (a : PositiveDefiniteIntegralLattice.RationalAdele)
    (X : skewAdjointMatricesLieSubalgebra F) :
    (rationalAdeleSkewAdjointScalarExtensionEquiv F
      (a ⊗ₜ[ℚ] X) : Matrix ι ι PositiveDefiniteIntegralLattice.RationalAdele) =
      a • (X : Matrix ι ι ℚ).map
        (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele) := by
  simp only [rationalAdeleSkewAdjointScalarExtensionEquiv,
    LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    LinearMap.tensorKerEquiv_apply]
  rw [coe_skewAdjointOperatorKerEquiv_apply]
  change rationalAdeleTensorProductMatrixEquiv
    ((LinearMap.tensorKer PositiveDefiniteIntegralLattice.RationalAdele
      PositiveDefiniteIntegralLattice.RationalAdele (skewAdjointOperator F)
      (a ⊗ₜ[ℚ] (skewAdjointOperatorKerEquiv F).symm X) :
        PositiveDefiniteIntegralLattice.RationalAdele ⊗[ℚ] Matrix ι ι ℚ)) = _
  rw [LinearMap.tensorKer_tmul,
    rationalAdeleTensorProductMatrixEquiv_tmul,
    coe_skewAdjointOperatorKerEquiv_symm_apply]

end Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Coordinates in the fixed rational differential basis identify linearly
with the full adelic skew-adjoint tangent carrier. -/
noncomputable def fullAdelicSkewAdjointTangentCoordinateEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    (V.InvariantDifferentialCoordinateIndex →
        PositiveDefiniteIntegralLattice.RationalAdele) ≃ₗ[PositiveDefiniteIntegralLattice.RationalAdele]
      skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix :=
  ((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
      PositiveDefiniteIntegralLattice.RationalAdele).equivFun.symm ≪≫ₗ
    Matrix.rationalAdeleSkewAdjointScalarExtensionEquiv V.pairingMatrix

@[simp]
theorem coe_fullAdelicSkewAdjointTangentCoordinateEquiv_apply
    (V : RationalQuadraticSpaceMatrix n)
    (x : V.InvariantDifferentialCoordinateIndex →
      PositiveDefiniteIntegralLattice.RationalAdele) :
    (V.fullAdelicSkewAdjointTangentCoordinateEquiv x :
      Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) =
      V.fullAdelicSkewAdjointCoordinateLinearMap x := by
  change
    (Matrix.rationalAdeleSkewAdjointScalarExtensionEquiv V.pairingMatrix
      (((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
        PositiveDefiniteIntegralLattice.RationalAdele).equivFun.symm x) :
        Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) =
      V.fullAdelicSkewAdjointCoordinateLinearMap x
  rw [Module.Basis.equivFun_symm_apply,
    fullAdelicSkewAdjointCoordinateLinearMap_apply]
  let e :=
    Matrix.rationalAdeleSkewAdjointScalarExtensionEquiv V.pairingMatrix
  have hterm (i : V.InvariantDifferentialCoordinateIndex) :
      ((e (x i •
        ((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
          PositiveDefiniteIntegralLattice.RationalAdele) i) :
          skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :
        Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) =
      x i •
        ((Matrix.skewAdjointFinBasis V.pairingMatrix i :
          V.skewAdjointTangent) : Matrix (Fin n) (Fin n) ℚ).map
            (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele) := by
    rw [e.map_smul]
    change x i •
      ((e
        (((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
          PositiveDefiniteIntegralLattice.RationalAdele) i) :
          skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :
        Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) = _
    rw [Module.Basis.baseChange_apply]
    change x i •
      ((Matrix.rationalAdeleSkewAdjointScalarExtensionEquiv V.pairingMatrix
        (1 ⊗ₜ[ℚ] Matrix.skewAdjointFinBasis V.pairingMatrix i) :
          skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :
        Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) = _
    rw [Matrix.coe_rationalAdeleSkewAdjointScalarExtensionEquiv_tmul,
      one_smul]
  have hsum (s : Finset V.InvariantDifferentialCoordinateIndex) :
      ((e (∑ i ∈ s, x i •
        ((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
          PositiveDefiniteIntegralLattice.RationalAdele) i) :
          skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :
        Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) =
      ∑ i ∈ s, x i •
        ((Matrix.skewAdjointFinBasis V.pairingMatrix i :
          V.skewAdjointTangent) : Matrix (Fin n) (Fin n) ℚ).map
            (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele) := by
    induction s using Finset.induction_on with
    | empty =>
        have hzero := congrArg Subtype.val e.map_zero
        simpa only [Finset.sum_empty] using hzero
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, e.map_add]
        change
          ((e (x i •
            ((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
              PositiveDefiniteIntegralLattice.RationalAdele) i) :
              skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :
            Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) +
            (e (∑ j ∈ s, x j •
              ((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
                PositiveDefiniteIntegralLattice.RationalAdele) j) :
              Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) = _
        rw [hterm, ih]
  exact hsum Finset.univ

/-- The exact coordinate range is the full adelic skew-adjoint matrix
carrier. -/
theorem fullAdelicSkewAdjointCoordinateLinearMap_range_eq
    (V : RationalQuadraticSpaceMatrix n) :
    LinearMap.range V.fullAdelicSkewAdjointCoordinateLinearMap =
      (skewAdjointMatricesLieSubalgebra
        V.fullAdelicFormMatrix).toSubmodule := by
  ext X
  constructor
  · rintro ⟨x, rfl⟩
    exact V.fullAdelicSkewAdjointCoordinateLinearMap_mem x
  · intro hX
    let Y : skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix :=
      ⟨X, hX⟩
    let x := V.fullAdelicSkewAdjointTangentCoordinateEquiv.symm Y
    refine ⟨x, ?_⟩
    have h :=
      congrArg Subtype.val
        (V.fullAdelicSkewAdjointTangentCoordinateEquiv.apply_symm_apply Y)
    change
      (V.fullAdelicSkewAdjointTangentCoordinateEquiv x :
        Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) = X at h
    rw [coe_fullAdelicSkewAdjointTangentCoordinateEquiv_apply] at h
    exact h

/-- The old exact coordinate range and the full skew-adjoint carrier are
linearly equivalent by their identical ambient matrices. -/
noncomputable def fullAdelicSkewAdjointCoordinateRangeEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    V.FullAdelicSkewAdjointCoordinateRange ≃ₗ[
      PositiveDefiniteIntegralLattice.RationalAdele]
      skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix where
  toFun X := ⟨X, V.fullAdelicSkewAdjointCoordinateRange_mem X⟩
  invFun X := ⟨X, by
    change (X : Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) ∈
      LinearMap.range V.fullAdelicSkewAdjointCoordinateLinearMap
    rw [V.fullAdelicSkewAdjointCoordinateLinearMap_range_eq]
    exact X.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_fullAdelicSkewAdjointCoordinateRangeEquiv_apply
    (V : RationalQuadraticSpaceMatrix n)
    (X : V.FullAdelicSkewAdjointCoordinateRange) :
    (V.fullAdelicSkewAdjointCoordinateRangeEquiv X :
      Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) = X :=
  rfl

@[simp]
theorem coe_fullAdelicSkewAdjointCoordinateRangeEquiv_symm_apply
    (V : RationalQuadraticSpaceMatrix n)
    (X : skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :
    (V.fullAdelicSkewAdjointCoordinateRangeEquiv.symm X :
      Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) = X :=
  rfl

theorem continuous_fullAdelicSkewAdjointTangentCoordinateEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    Continuous V.fullAdelicSkewAdjointTangentCoordinateEquiv := by
  have heq :
    (fun x =>
      (V.fullAdelicSkewAdjointTangentCoordinateEquiv x :
        Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele)) =
      V.fullAdelicSkewAdjointCoordinateLinearMap :=
    funext V.coe_fullAdelicSkewAdjointTangentCoordinateEquiv_apply
  have hambient : Continuous
      (fun x =>
        (V.fullAdelicSkewAdjointTangentCoordinateEquiv x :
          Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele)) := by
    rw [heq]
    exact V.continuous_fullAdelicSkewAdjointCoordinateLinearMap
  exact hambient.subtype_mk _

theorem continuous_fullAdelicSkewAdjointCoordinateRangeEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    Continuous V.fullAdelicSkewAdjointCoordinateRangeEquiv :=
  continuous_subtype_val.subtype_mk _

theorem continuous_fullAdelicSkewAdjointCoordinateRangeEquiv_symm
    (V : RationalQuadraticSpaceMatrix n) :
    Continuous V.fullAdelicSkewAdjointCoordinateRangeEquiv.symm :=
  continuous_subtype_val.subtype_mk _

/-- The exact coordinate range is homeomorphic to the full adelic
skew-adjoint carrier. -/
noncomputable def fullAdelicSkewAdjointCoordinateRangeHomeomorph
    (V : RationalQuadraticSpaceMatrix n) :
    V.FullAdelicSkewAdjointCoordinateRange ≃ₜ
      skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix where
  toEquiv := V.fullAdelicSkewAdjointCoordinateRangeEquiv.toEquiv
  continuous_toFun := V.continuous_fullAdelicSkewAdjointCoordinateRangeEquiv
  continuous_invFun :=
    V.continuous_fullAdelicSkewAdjointCoordinateRangeEquiv_symm

/-- The coordinate-transported measurable structure on the full adelic
skew-adjoint carrier.

This is transported from the exact range rather than identified with the
ambient Borel structure; continuity of the coordinate inverse is not
proved here. -/
noncomputable instance fullAdelicSkewAdjointTangentMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :=
  MeasurableSpace.map V.fullAdelicSkewAdjointCoordinateRangeEquiv
    (inferInstance : MeasurableSpace
      V.FullAdelicSkewAdjointCoordinateRange)

theorem measurable_fullAdelicSkewAdjointCoordinateRangeEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    Measurable V.fullAdelicSkewAdjointCoordinateRangeEquiv := by
  intro s hs
  exact hs

theorem measurable_fullAdelicSkewAdjointCoordinateRangeEquiv_symm
    (V : RationalQuadraticSpaceMatrix n) :
    Measurable V.fullAdelicSkewAdjointCoordinateRangeEquiv.symm := by
  intro s hs
  change MeasurableSet
    (V.fullAdelicSkewAdjointCoordinateRangeEquiv ⁻¹'
      (V.fullAdelicSkewAdjointCoordinateRangeEquiv.symm ⁻¹' s))
  simpa only [Set.preimage_preimage, Function.comp_def,
    LinearEquiv.symm_apply_apply] using hs

/-- The exact range and full skew-adjoint carrier as a measurable
equivalence for the transported coordinate structures. -/
noncomputable def fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    V.FullAdelicSkewAdjointCoordinateRange ≃ᵐ
      skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix where
  toEquiv := V.fullAdelicSkewAdjointCoordinateRangeEquiv.toEquiv
  measurable_toFun :=
    V.measurable_fullAdelicSkewAdjointCoordinateRangeEquiv
  measurable_invFun :=
    V.measurable_fullAdelicSkewAdjointCoordinateRangeEquiv_symm

/-- Fixed differential coordinates as a measurable equivalence with the full
adelic skew-adjoint carrier. -/
noncomputable def fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    (V.InvariantDifferentialCoordinateIndex →
        PositiveDefiniteIntegralLattice.RationalAdele) ≃ᵐ
      skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix :=
  V.fullAdelicSkewAdjointCoordinateMeasurableEquiv.trans
    V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv

/-- The normalized differential-coordinate measure on the full adelic
skew-adjoint tangent carrier. -/
noncomputable def fullAdelicSkewAdjointTangentCoordinateMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :=
  Measure.map V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv
    V.fullAdelicSkewAdjointCoordinateMeasure

theorem fullAdelicSkewAdjointTangentCoordinateMeasure_eq_map
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicSkewAdjointTangentCoordinateMeasure =
      Measure.map V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv
        V.invariantDifferentialAdeleCoordinateNormalization.measure := by
  rw [fullAdelicSkewAdjointTangentCoordinateMeasure,
    fullAdelicSkewAdjointCoordinateMeasure,
    Measure.map_map
      V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv.measurable
      V.fullAdelicSkewAdjointCoordinateMeasurableEquiv.measurable]
  rfl

theorem fullAdelicSkewAdjointTangentCoordinateMeasure_map_symm
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.map
        V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv.symm
        V.fullAdelicSkewAdjointTangentCoordinateMeasure =
      V.fullAdelicSkewAdjointCoordinateMeasure :=
  MeasurableEquiv.map_symm_map
    V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv

theorem fullAdelicSkewAdjointTangentCoordinateMeasure_map_coordinateEquiv_symm
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.map V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.symm
        V.fullAdelicSkewAdjointTangentCoordinateMeasure =
      V.invariantDifferentialAdeleCoordinateNormalization.measure := by
  rw [V.fullAdelicSkewAdjointTangentCoordinateMeasure_eq_map]
  exact MeasurableEquiv.map_symm_map
    V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv

theorem measurePreserving_fullAdelicSkewAdjointCoordinateRangeEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurePreserving
      V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv
      V.fullAdelicSkewAdjointCoordinateMeasure
      V.fullAdelicSkewAdjointTangentCoordinateMeasure :=
  ⟨V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv.measurable, rfl⟩

theorem measurePreserving_fullAdelicSkewAdjointCoordinateRangeEquiv_symm
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurePreserving
      V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv.symm
      V.fullAdelicSkewAdjointTangentCoordinateMeasure
      V.fullAdelicSkewAdjointCoordinateMeasure :=
  ⟨V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv.symm.measurable,
    V.fullAdelicSkewAdjointTangentCoordinateMeasure_map_symm⟩

theorem measurePreserving_fullAdelicSkewAdjointTangentCoordinateEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurePreserving
      V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv
      V.invariantDifferentialAdeleCoordinateNormalization.measure
      V.fullAdelicSkewAdjointTangentCoordinateMeasure :=
  ⟨V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.measurable,
    V.fullAdelicSkewAdjointTangentCoordinateMeasure_eq_map.symm⟩

theorem measurePreserving_fullAdelicSkewAdjointTangentCoordinateEquiv_symm
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurePreserving
      V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.symm
      V.fullAdelicSkewAdjointTangentCoordinateMeasure
      V.invariantDifferentialAdeleCoordinateNormalization.measure :=
  ⟨V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.symm.measurable,
    V.fullAdelicSkewAdjointTangentCoordinateMeasure_map_coordinateEquiv_symm⟩

/-- The standard differential parallelotope in the full adelic skew-adjoint
tangent carrier. -/
noncomputable def fullAdelicSkewAdjointTangentStandardParallelotope
    (V : RationalQuadraticSpaceMatrix n) :
    Set (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :=
  V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv ''
    V.fullAdelicSkewAdjointStandardParallelotope

theorem measurableSet_fullAdelicSkewAdjointTangentStandardParallelotope
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSet V.fullAdelicSkewAdjointTangentStandardParallelotope := by
  change MeasurableSet
    (V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv ''
      V.fullAdelicSkewAdjointStandardParallelotope)
  exact
    V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv.measurableEmbedding
      |>.measurableSet_image |>.2
        V.measurableSet_fullAdelicSkewAdjointStandardParallelotope

theorem isCompact_fullAdelicSkewAdjointTangentStandardParallelotope
    (V : RationalQuadraticSpaceMatrix n) :
    IsCompact V.fullAdelicSkewAdjointTangentStandardParallelotope := by
  change IsCompact
    (V.fullAdelicSkewAdjointCoordinateRangeHomeomorph ''
      V.fullAdelicSkewAdjointStandardParallelotope)
  exact V.isCompact_fullAdelicSkewAdjointStandardParallelotope.image
    V.fullAdelicSkewAdjointCoordinateRangeHomeomorph.continuous

@[simp]
theorem fullAdelicSkewAdjointTangentCoordinateMeasure_standardParallelotope
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicSkewAdjointTangentCoordinateMeasure
      V.fullAdelicSkewAdjointTangentStandardParallelotope = 1 := by
  rw [fullAdelicSkewAdjointTangentCoordinateMeasure,
    V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv.map_apply,
    fullAdelicSkewAdjointTangentStandardParallelotope,
    Set.preimage_image_eq _
      V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv.injective]
  exact V.fullAdelicSkewAdjointCoordinateMeasure_standardParallelotope

theorem fullAdelicSkewAdjointTangentCoordinateMeasure_univ
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicSkewAdjointTangentCoordinateMeasure Set.univ =
      V.fullAdelicSkewAdjointCoordinateMeasure Set.univ := by
  rw [fullAdelicSkewAdjointTangentCoordinateMeasure,
    V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv.map_apply]
  rw [Set.preimage_univ]

theorem fullAdelicSkewAdjointTangentCoordinateMeasure_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicSkewAdjointTangentCoordinateMeasure ≠ 0 := by
  intro hzero
  have h : (1 : ENNReal) = 0 := calc
    1 = V.fullAdelicSkewAdjointTangentCoordinateMeasure
        V.fullAdelicSkewAdjointTangentStandardParallelotope :=
      V.fullAdelicSkewAdjointTangentCoordinateMeasure_standardParallelotope.symm
    _ = 0 := by rw [hzero]; rfl
  exact one_ne_zero h

noncomputable instance fullAdelicSkewAdjointTangentCoordinateMeasure_sigmaFinite
    (V : RationalQuadraticSpaceMatrix n) :
    SigmaFinite V.fullAdelicSkewAdjointTangentCoordinateMeasure :=
  V.fullAdelicSkewAdjointCoordinateRangeMeasurableEquiv.sigmaFinite_map

/-- Unit parallelotope mass excludes every nontrivial scalar rescaling on the
full adelic skew-adjoint tangent carrier. -/
theorem fullAdelicSkewAdjointTangentCoordinateMeasure_smul_normalized_iff
    (V : RationalQuadraticSpaceMatrix n) (c : ENNReal) :
    (c • V.fullAdelicSkewAdjointTangentCoordinateMeasure)
        V.fullAdelicSkewAdjointTangentStandardParallelotope = 1 ↔
      c = 1 := by
  rw [Measure.smul_apply,
    V.fullAdelicSkewAdjointTangentCoordinateMeasure_standardParallelotope,
    smul_eq_mul, mul_one]

end RationalQuadraticSpaceMatrix
