import SMSFormula.RationalSpecialOrthogonalDifferentialNormalization
import Mathlib.RingTheory.Flat.Basic

/-!
# Full-adelic coordinates in the rational skew-adjoint tangent model

This file maps the fixed rational skew-adjoint basis into matrices over the
full rational adele ring.  Scalar extension into matrices is injective because
the rational adeles are flat over `ℚ`; its exact range is therefore linearly
equivalent to the fixed adelic coordinate space.

The range receives the measurable structure transported through this
equivalence.  This gives an exact coordinate measure, inverse recovery, and
unit-parallelotope normalization without asserting that the range is every
skew-adjoint matrix over the nonfield adele ring.  No measure on an adelic
special orthogonal group is constructed here.
-/

noncomputable section

open MeasureTheory Set
open scoped Matrix TensorProduct ENNReal

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Tensor-product matrix coordinates over the full rational adele ring.

Unlike `tensorProductMatrixEquiv`, this only uses the commutative-ring
structure of the target. -/
def rationalAdeleTensorProductMatrixEquiv :
    PositiveDefiniteIntegralLattice.RationalAdele ⊗[ℚ] Matrix ι ι ℚ ≃ₗ[
      PositiveDefiniteIntegralLattice.RationalAdele]
      Matrix ι ι PositiveDefiniteIntegralLattice.RationalAdele :=
  TensorProduct.piRight ℚ PositiveDefiniteIntegralLattice.RationalAdele
      PositiveDefiniteIntegralLattice.RationalAdele (fun _ : ι ↦ ι → ℚ) ≪≫ₗ
    LinearEquiv.piCongrRight
      (fun _ : ι ↦
        TensorProduct.piScalarRight ℚ PositiveDefiniteIntegralLattice.RationalAdele
          PositiveDefiniteIntegralLattice.RationalAdele ι)

@[simp]
theorem rationalAdeleTensorProductMatrixEquiv_tmul
    (a : PositiveDefiniteIntegralLattice.RationalAdele) (X : Matrix ι ι ℚ) :
    rationalAdeleTensorProductMatrixEquiv (a ⊗ₜ[ℚ] X) =
      a • X.map (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele) := by
  ext i j
  change
    (TensorProduct.piScalarRight ℚ PositiveDefiniteIntegralLattice.RationalAdele
      PositiveDefiniteIntegralLattice.RationalAdele ι
      ((TensorProduct.piRight ℚ PositiveDefiniteIntegralLattice.RationalAdele
        PositiveDefiniteIntegralLattice.RationalAdele (fun _ : ι ↦ ι → ℚ)
        (a ⊗ₜ[ℚ] X)) i)) j = _
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  simp [Algebra.smul_def, mul_comm]

/-- The skew-adjoint operator commutes with mapping rational matrix entries
into the full rational adeles. -/
theorem skewAdjointOperator_map_rationalAdele
    (F X : Matrix ι ι ℚ) :
    (skewAdjointOperator F X).map
        (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele) =
      skewAdjointOperator
        (F.map (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele))
        (X.map (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele)) := by
  rw [skewAdjointOperator_apply, skewAdjointOperator_apply,
    Matrix.map_add _ (map_add (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele)),
    Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

end Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

private noncomputable instance rationalAdeleFlat :
    Module.Flat ℚ PositiveDefiniteIntegralLattice.RationalAdele :=
  Module.Flat.of_free

/-- The full-adelic matrix represented by coordinates in the fixed rational
skew-adjoint basis. -/
noncomputable def fullAdelicSkewAdjointCoordinateLinearMap
    (V : RationalQuadraticSpaceMatrix n) :
    (V.InvariantDifferentialCoordinateIndex →
        PositiveDefiniteIntegralLattice.RationalAdele) →ₗ[PositiveDefiniteIntegralLattice.RationalAdele]
      Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele :=
  Matrix.rationalAdeleTensorProductMatrixEquiv.toLinearMap.comp
    ((V.skewAdjointTangent.toSubmodule.subtype.baseChange
      PositiveDefiniteIntegralLattice.RationalAdele).comp
      ((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
        PositiveDefiniteIntegralLattice.RationalAdele).equivFun.symm.toLinearMap)

@[simp]
theorem fullAdelicSkewAdjointCoordinateLinearMap_apply
    (V : RationalQuadraticSpaceMatrix n)
    (x : V.InvariantDifferentialCoordinateIndex →
      PositiveDefiniteIntegralLattice.RationalAdele) :
    V.fullAdelicSkewAdjointCoordinateLinearMap x =
      ∑ i, x i •
        ((Matrix.skewAdjointFinBasis V.pairingMatrix i :
          V.skewAdjointTangent) : Matrix (Fin n) (Fin n) ℚ).map
            (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele) := by
  change Matrix.rationalAdeleTensorProductMatrixEquiv
      ((V.skewAdjointTangent.toSubmodule.subtype.baseChange
        PositiveDefiniteIntegralLattice.RationalAdele)
        (((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
          PositiveDefiniteIntegralLattice.RationalAdele).equivFun.symm x)) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp

theorem fullAdelicSkewAdjointCoordinateLinearMap_injective
    (V : RationalQuadraticSpaceMatrix n) :
    Function.Injective V.fullAdelicSkewAdjointCoordinateLinearMap := by
  have hsubtype :
      Function.Injective V.skewAdjointTangent.toSubmodule.subtype :=
    V.skewAdjointTangent.toSubmodule.subtype_injective
  have hbase :
      Function.Injective
        (V.skewAdjointTangent.toSubmodule.subtype.baseChange
          PositiveDefiniteIntegralLattice.RationalAdele) := by
    simpa [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap
        (M := PositiveDefiniteIntegralLattice.RationalAdele)
        V.skewAdjointTangent.toSubmodule.subtype hsubtype)
  change Function.Injective
    (fun x =>
      Matrix.rationalAdeleTensorProductMatrixEquiv
        ((V.skewAdjointTangent.toSubmodule.subtype.baseChange
          PositiveDefiniteIntegralLattice.RationalAdele)
          (((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
            PositiveDefiniteIntegralLattice.RationalAdele).equivFun.symm x)))
  exact
    Matrix.rationalAdeleTensorProductMatrixEquiv.injective.comp
      (hbase.comp
        ((Matrix.skewAdjointFinBasis V.pairingMatrix).baseChange
          PositiveDefiniteIntegralLattice.RationalAdele).equivFun.symm.injective)

/-- Every matrix represented by the fixed coordinates is skew-adjoint for the
adelically mapped rational form. -/
theorem fullAdelicSkewAdjointCoordinateLinearMap_mem
    (V : RationalQuadraticSpaceMatrix n)
    (x : V.InvariantDifferentialCoordinateIndex →
      PositiveDefiniteIntegralLattice.RationalAdele) :
    V.fullAdelicSkewAdjointCoordinateLinearMap x ∈
      skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix := by
  rw [fullAdelicSkewAdjointCoordinateLinearMap_apply]
  apply (skewAdjointMatricesLieSubalgebra
    V.fullAdelicFormMatrix).toSubmodule.sum_mem
  intro i _
  apply (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix).smul_mem
  rw [← Matrix.mem_ker_skewAdjointOperator_iff]
  change Matrix.skewAdjointOperator V.fullAdelicFormMatrix
    (((Matrix.skewAdjointFinBasis V.pairingMatrix i :
      V.skewAdjointTangent) : Matrix (Fin n) (Fin n) ℚ).map
        (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele)) = 0
  rw [fullAdelicFormMatrix,
    ← Matrix.skewAdjointOperator_map_rationalAdele]
  have hi :
      Matrix.skewAdjointOperator V.pairingMatrix
        (Matrix.skewAdjointFinBasis V.pairingMatrix i) = 0 :=
    LinearMap.mem_ker.mp
      ((Matrix.mem_ker_skewAdjointOperator_iff V.pairingMatrix
        (Matrix.skewAdjointFinBasis V.pairingMatrix i)).mpr
          (Matrix.skewAdjointFinBasis V.pairingMatrix i).property)
  simp [hi]

/-- The exact full-adelic matrix range generated by the fixed rational
skew-adjoint basis. -/
abbrev FullAdelicSkewAdjointCoordinateRange
    (V : RationalQuadraticSpaceMatrix n) :=
  LinearMap.range V.fullAdelicSkewAdjointCoordinateLinearMap

theorem fullAdelicSkewAdjointCoordinateRange_mem
    (V : RationalQuadraticSpaceMatrix n)
    (X : V.FullAdelicSkewAdjointCoordinateRange) :
    (X : Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) ∈
      skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix := by
  rcases X.property with ⟨x, hx⟩
  rw [← hx]
  exact V.fullAdelicSkewAdjointCoordinateLinearMap_mem x

/-- Coordinates are linearly equivalent to their exact full-adelic matrix
range.  No surjectivity onto all skew-adjoint adelic matrices is asserted. -/
noncomputable def fullAdelicSkewAdjointCoordinateEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    (V.InvariantDifferentialCoordinateIndex →
        PositiveDefiniteIntegralLattice.RationalAdele) ≃ₗ[PositiveDefiniteIntegralLattice.RationalAdele]
      V.FullAdelicSkewAdjointCoordinateRange :=
  LinearEquiv.ofInjective V.fullAdelicSkewAdjointCoordinateLinearMap
    V.fullAdelicSkewAdjointCoordinateLinearMap_injective

@[simp]
theorem coe_fullAdelicSkewAdjointCoordinateEquiv_apply
    (V : RationalQuadraticSpaceMatrix n)
    (x : V.InvariantDifferentialCoordinateIndex →
      PositiveDefiniteIntegralLattice.RationalAdele) :
    (V.fullAdelicSkewAdjointCoordinateEquiv x :
      Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) =
      V.fullAdelicSkewAdjointCoordinateLinearMap x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem continuous_fullAdelicSkewAdjointCoordinateLinearMap
    (V : RationalQuadraticSpaceMatrix n) :
    Continuous V.fullAdelicSkewAdjointCoordinateLinearMap := by
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  simp only [fullAdelicSkewAdjointCoordinateLinearMap_apply,
    Matrix.sum_apply, Matrix.smul_apply]
  fun_prop

theorem continuous_fullAdelicSkewAdjointCoordinateEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    Continuous V.fullAdelicSkewAdjointCoordinateEquiv :=
  V.continuous_fullAdelicSkewAdjointCoordinateLinearMap.subtype_mk _

/-- The coordinate-transported measurable structure on the exact adelic
matrix range.

This is given explicitly because continuity of the inverse coordinate map over
the nonfield adele ring is not proved here. -/
noncomputable instance fullAdelicSkewAdjointCoordinateRangeMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FullAdelicSkewAdjointCoordinateRange :=
  MeasurableSpace.map V.fullAdelicSkewAdjointCoordinateEquiv
    (inferInstance : MeasurableSpace
      (V.InvariantDifferentialCoordinateIndex →
        PositiveDefiniteIntegralLattice.RationalAdele))

theorem measurable_fullAdelicSkewAdjointCoordinateEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    Measurable V.fullAdelicSkewAdjointCoordinateEquiv := by
  intro s hs
  exact hs

theorem measurable_fullAdelicSkewAdjointCoordinateEquiv_symm
    (V : RationalQuadraticSpaceMatrix n) :
    Measurable V.fullAdelicSkewAdjointCoordinateEquiv.symm := by
  intro s hs
  change MeasurableSet
    (V.fullAdelicSkewAdjointCoordinateEquiv ⁻¹'
      (V.fullAdelicSkewAdjointCoordinateEquiv.symm ⁻¹' s))
  simpa only [Set.preimage_preimage, Function.comp_def,
    LinearEquiv.symm_apply_apply] using hs

/-- The fixed coordinates as a measurable equivalence with their exact
full-adelic matrix range. -/
noncomputable def fullAdelicSkewAdjointCoordinateMeasurableEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    (V.InvariantDifferentialCoordinateIndex →
        PositiveDefiniteIntegralLattice.RationalAdele) ≃ᵐ
      V.FullAdelicSkewAdjointCoordinateRange where
  toEquiv := V.fullAdelicSkewAdjointCoordinateEquiv.toEquiv
  measurable_toFun := V.measurable_fullAdelicSkewAdjointCoordinateEquiv
  measurable_invFun := V.measurable_fullAdelicSkewAdjointCoordinateEquiv_symm

/-- The differential-coordinate measure transported to the exact full-adelic
matrix range. -/
noncomputable def fullAdelicSkewAdjointCoordinateMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure V.FullAdelicSkewAdjointCoordinateRange :=
  Measure.map V.fullAdelicSkewAdjointCoordinateMeasurableEquiv
    V.invariantDifferentialAdeleCoordinateNormalization.measure

theorem fullAdelicSkewAdjointCoordinateMeasure_map_symm
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.map V.fullAdelicSkewAdjointCoordinateMeasurableEquiv.symm
        V.fullAdelicSkewAdjointCoordinateMeasure =
      V.invariantDifferentialAdeleCoordinateNormalization.measure :=
  MeasurableEquiv.map_symm_map
    V.fullAdelicSkewAdjointCoordinateMeasurableEquiv

theorem measurePreserving_fullAdelicSkewAdjointCoordinateEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurePreserving V.fullAdelicSkewAdjointCoordinateMeasurableEquiv
      V.invariantDifferentialAdeleCoordinateNormalization.measure
      V.fullAdelicSkewAdjointCoordinateMeasure :=
  ⟨V.fullAdelicSkewAdjointCoordinateMeasurableEquiv.measurable, rfl⟩

theorem measurePreserving_fullAdelicSkewAdjointCoordinateEquiv_symm
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurePreserving V.fullAdelicSkewAdjointCoordinateMeasurableEquiv.symm
      V.fullAdelicSkewAdjointCoordinateMeasure
      V.invariantDifferentialAdeleCoordinateNormalization.measure :=
  ⟨V.fullAdelicSkewAdjointCoordinateMeasurableEquiv.symm.measurable,
    V.fullAdelicSkewAdjointCoordinateMeasure_map_symm⟩

/-- The image of the standard coordinate parallelotope in the exact adelic
matrix range. -/
noncomputable def fullAdelicSkewAdjointStandardParallelotope
    (V : RationalQuadraticSpaceMatrix n) :
    Set V.FullAdelicSkewAdjointCoordinateRange :=
  V.fullAdelicSkewAdjointCoordinateMeasurableEquiv ''
    V.invariantDifferentialAdeleStandardParallelotope

theorem measurableSet_fullAdelicSkewAdjointStandardParallelotope
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSet V.fullAdelicSkewAdjointStandardParallelotope := by
  change MeasurableSet
    (V.fullAdelicSkewAdjointCoordinateMeasurableEquiv ''
      V.invariantDifferentialAdeleStandardParallelotope)
  exact
    V.fullAdelicSkewAdjointCoordinateMeasurableEquiv.measurableEmbedding
      |>.measurableSet_image |>.2
        (by
          rw [invariantDifferentialAdeleStandardParallelotope,
            PositiveDefiniteIntegralLattice.rationalAdeleCoordinateStandardBlock]
          exact MeasurableSet.univ_pi
            (δ := Fin (Module.finrank ℚ V.skewAdjointTangent))
            (fun _ =>
              PositiveDefiniteIntegralLattice.measurableSet_rationalAdeleStandardBlock))

theorem isCompact_fullAdelicSkewAdjointStandardParallelotope
    (V : RationalQuadraticSpaceMatrix n) :
    IsCompact V.fullAdelicSkewAdjointStandardParallelotope := by
  change IsCompact
    (V.fullAdelicSkewAdjointCoordinateEquiv ''
      V.invariantDifferentialAdeleStandardParallelotope)
  exact
    (PositiveDefiniteIntegralLattice.rationalAdeleCoordinatePositiveCompacts
      (Module.finrank ℚ V.skewAdjointTangent)).isCompact.image
        V.continuous_fullAdelicSkewAdjointCoordinateEquiv

@[simp]
theorem fullAdelicSkewAdjointCoordinateMeasure_standardParallelotope
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicSkewAdjointCoordinateMeasure
      V.fullAdelicSkewAdjointStandardParallelotope = 1 := by
  rw [fullAdelicSkewAdjointCoordinateMeasure,
    V.fullAdelicSkewAdjointCoordinateMeasurableEquiv.map_apply,
    fullAdelicSkewAdjointStandardParallelotope]
  rw [Set.preimage_image_eq _
    V.fullAdelicSkewAdjointCoordinateMeasurableEquiv.injective]
  exact V.invariantDifferentialAdeleCoordinateNormalization.standardParallelotope_eq_one

theorem fullAdelicSkewAdjointCoordinateMeasure_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicSkewAdjointCoordinateMeasure ≠ 0 := by
  intro hzero
  have h : (1 : ENNReal) = 0 := calc
    1 = V.fullAdelicSkewAdjointCoordinateMeasure
        V.fullAdelicSkewAdjointStandardParallelotope :=
      V.fullAdelicSkewAdjointCoordinateMeasure_standardParallelotope.symm
    _ = 0 := by rw [hzero]; rfl
  exact one_ne_zero h

noncomputable instance fullAdelicSkewAdjointCoordinateMeasure_sigmaFinite
    (V : RationalQuadraticSpaceMatrix n) :
    SigmaFinite V.fullAdelicSkewAdjointCoordinateMeasure :=
  V.fullAdelicSkewAdjointCoordinateMeasurableEquiv.sigmaFinite_map

/-- Unit parallelotope mass removes every nontrivial scalar rescaling after
transport to the exact adelic matrix range. -/
theorem fullAdelicSkewAdjointCoordinateMeasure_smul_normalized_iff
    (V : RationalQuadraticSpaceMatrix n) (c : ENNReal) :
    (c • V.fullAdelicSkewAdjointCoordinateMeasure)
        V.fullAdelicSkewAdjointStandardParallelotope = 1 ↔
      c = 1 := by
  rw [Measure.smul_apply,
    V.fullAdelicSkewAdjointCoordinateMeasure_standardParallelotope,
    smul_eq_mul, mul_one]

end RationalQuadraticSpaceMatrix
