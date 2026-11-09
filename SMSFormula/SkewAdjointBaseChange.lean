import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Instances.Matrix

/-!
# Base change for skew-adjoint matrices

This file identifies skew-adjoint matrices with the kernel of their defining
linear operator and proves that this kernel commutes with extension of scalars
between fields.
-/

noncomputable section

open scoped Matrix TensorProduct

namespace Matrix

variable {R Q K ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear operator whose kernel consists of the matrices skew-adjoint
with respect to `F`. -/
def skewAdjointOperator [CommRing R] (F : Matrix ι ι R) :
    Matrix ι ι R →ₗ[R] Matrix ι ι R where
  toFun X := Xᵀ * F + F * X
  map_add' X Y := by
    simp [Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a X := by simp

@[simp]
theorem skewAdjointOperator_apply [CommRing R] (F X : Matrix ι ι R) :
    skewAdjointOperator F X = Xᵀ * F + F * X :=
  rfl

theorem mem_ker_skewAdjointOperator_iff [CommRing R] (F X : Matrix ι ι R) :
    X ∈ LinearMap.ker (skewAdjointOperator F) ↔
      X ∈ skewAdjointMatricesLieSubalgebra F := by
  rw [LinearMap.mem_ker, skewAdjointOperator_apply,
    mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_neg]
  constructor
  · exact fun h ↦ eq_neg_of_add_eq_zero_left h
  · intro h
    rw [h, neg_add_cancel]

/-- The defining-kernel model of the skew-adjoint matrix Lie subalgebra. -/
def skewAdjointOperatorKerEquiv [CommRing R] (F : Matrix ι ι R) :
    LinearMap.ker (skewAdjointOperator F) ≃ₗ[R]
      skewAdjointMatricesLieSubalgebra F where
  toFun X := ⟨X, (mem_ker_skewAdjointOperator_iff F X).mp X.property⟩
  invFun X := ⟨X, (mem_ker_skewAdjointOperator_iff F X).mpr X.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_skewAdjointOperatorKerEquiv_apply [CommRing R] (F : Matrix ι ι R)
    (X : LinearMap.ker (skewAdjointOperator F)) :
    (skewAdjointOperatorKerEquiv F X : Matrix ι ι R) = X :=
  rfl

@[simp]
theorem coe_skewAdjointOperatorKerEquiv_symm_apply [CommRing R]
    (F : Matrix ι ι R) (X : skewAdjointMatricesLieSubalgebra F) :
    ((skewAdjointOperatorKerEquiv F).symm X : Matrix ι ι R) = X :=
  rfl

/-- The finite-coordinate identification of scalar-extended matrices with
matrices over the larger field. -/
def tensorProductMatrixEquiv [Field Q] [Field K] [Algebra Q K] :
    K ⊗[Q] Matrix ι ι Q ≃ₗ[K] Matrix ι ι K :=
  TensorProduct.piRight Q K K (fun _ : ι ↦ ι → Q) ≪≫ₗ
    LinearEquiv.piCongrRight
      (fun _ : ι ↦ TensorProduct.piScalarRight Q K K ι)

@[simp]
theorem tensorProductMatrixEquiv_tmul [Field Q] [Field K] [Algebra Q K]
    (a : K) (X : Matrix ι ι Q) :
    tensorProductMatrixEquiv (Q := Q) (K := K) (a ⊗ₜ[Q] X) =
      a • X.map (algebraMap Q K) := by
  ext i j
  change (TensorProduct.piScalarRight Q K K ι
    ((TensorProduct.piRight Q K K (fun _ : ι ↦ ι → Q) (a ⊗ₜ[Q] X)) i)) j = _
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  simp [Algebra.smul_def, mul_comm]

@[simp]
theorem skewAdjointOperator_map [Field Q] [Field K] [Algebra Q K]
    (F X : Matrix ι ι Q) :
    (skewAdjointOperator F X).map (algebraMap Q K) =
      skewAdjointOperator (F.map (algebraMap Q K))
        (X.map (algebraMap Q K)) := by
  rw [skewAdjointOperator_apply, skewAdjointOperator_apply,
    Matrix.map_add _ (map_add (algebraMap Q K)), Matrix.map_mul,
    Matrix.map_mul, Matrix.transpose_map]

theorem tensorProductMatrixEquiv_skewAdjointOperator
    [Field Q] [Field K] [Algebra Q K] (F : Matrix ι ι Q)
    (z : K ⊗[Q] Matrix ι ι Q) :
    tensorProductMatrixEquiv (Q := Q) (K := K)
        ((skewAdjointOperator F).baseChange K z) =
      skewAdjointOperator (F.map (algebraMap Q K))
        (tensorProductMatrixEquiv (Q := Q) (K := K) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a X =>
      rw [LinearMap.baseChange_tmul, tensorProductMatrixEquiv_tmul,
        tensorProductMatrixEquiv_tmul, map_smul, skewAdjointOperator_map]

/-- The matrix-coordinate equivalence restricted to the kernels of the
skew-adjoint operators. -/
def baseChangedSkewAdjointKernelEquiv [Field Q] [Field K] [Algebra Q K]
    (F : Matrix ι ι Q) :
    LinearMap.ker ((skewAdjointOperator F).baseChange K) ≃ₗ[K]
      LinearMap.ker (skewAdjointOperator (F.map (algebraMap Q K))) where
  toFun X := ⟨tensorProductMatrixEquiv (Q := Q) (K := K) X, by
    change skewAdjointOperator (F.map (algebraMap Q K))
      (tensorProductMatrixEquiv (Q := Q) (K := K) X) = 0
    rw [← tensorProductMatrixEquiv_skewAdjointOperator, X.property, map_zero]⟩
  invFun X := ⟨(tensorProductMatrixEquiv (Q := Q) (K := K)).symm X, by
    change (skewAdjointOperator F).baseChange K
      ((tensorProductMatrixEquiv (Q := Q) (K := K)).symm X) = 0
    apply (tensorProductMatrixEquiv (Q := Q) (K := K)).injective
    rw [tensorProductMatrixEquiv_skewAdjointOperator,
      LinearEquiv.apply_symm_apply, X.property, map_zero]⟩
  left_inv X :=
    Subtype.ext ((tensorProductMatrixEquiv (Q := Q) (K := K)).symm_apply_apply
      (X : K ⊗[Q] Matrix ι ι Q))
  right_inv X :=
    Subtype.ext ((tensorProductMatrixEquiv (Q := Q) (K := K)).apply_symm_apply
      (X : Matrix ι ι K))
  map_add' X Y :=
    Subtype.ext ((tensorProductMatrixEquiv (Q := Q) (K := K)).map_add
      (X : K ⊗[Q] Matrix ι ι Q) Y)
  map_smul' a X :=
    Subtype.ext ((tensorProductMatrixEquiv (Q := Q) (K := K)).map_smul a
      (X : K ⊗[Q] Matrix ι ι Q))

@[simp]
theorem coe_baseChangedSkewAdjointKernelEquiv_apply
    [Field Q] [Field K] [Algebra Q K] (F : Matrix ι ι Q)
    (X : LinearMap.ker ((skewAdjointOperator F).baseChange K)) :
    (baseChangedSkewAdjointKernelEquiv (K := K) F X : Matrix ι ι K) =
      tensorProductMatrixEquiv (Q := Q) (K := K) X :=
  rfl

local instance fieldExtensionFlat [Field Q] [Field K] [Algebra Q K] :
    Module.Flat Q K :=
  Module.Flat.of_free

/-- Scalar extension commutes with the skew-adjoint matrix Lie subalgebra. -/
def skewAdjointScalarExtensionEquiv [Field Q] [Field K] [Algebra Q K]
    (F : Matrix ι ι Q) :
    K ⊗[Q] skewAdjointMatricesLieSubalgebra F ≃ₗ[K]
      skewAdjointMatricesLieSubalgebra (F.map (algebraMap Q K)) :=
  LinearEquiv.baseChange Q K _ _ (skewAdjointOperatorKerEquiv F).symm ≪≫ₗ
    LinearMap.tensorKerEquiv K K (skewAdjointOperator F) ≪≫ₗ
    baseChangedSkewAdjointKernelEquiv (K := K) F ≪≫ₗ
    skewAdjointOperatorKerEquiv (F.map (algebraMap Q K))

@[simp]
theorem coe_skewAdjointScalarExtensionEquiv_tmul
    [Field Q] [Field K] [Algebra Q K] (F : Matrix ι ι Q) (a : K)
    (X : skewAdjointMatricesLieSubalgebra F) :
    (skewAdjointScalarExtensionEquiv (K := K) F (a ⊗ₜ[Q] X) : Matrix ι ι K) =
      a • (X : Matrix ι ι Q).map (algebraMap Q K) := by
  simp only [skewAdjointScalarExtensionEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearMap.tensorKerEquiv_apply]
  rw [coe_skewAdjointOperatorKerEquiv_apply]
  change tensorProductMatrixEquiv (Q := Q) (K := K)
    ((LinearMap.tensorKer K K (skewAdjointOperator F)
      (a ⊗ₜ[Q] (skewAdjointOperatorKerEquiv F).symm X) :
        K ⊗[Q] Matrix ι ι Q)) = _
  rw [LinearMap.tensorKer_tmul, tensorProductMatrixEquiv_tmul,
    coe_skewAdjointOperatorKerEquiv_symm_apply]

/-- On pure tensors, direct scalar extension of skew-adjoint matrices agrees
with scalar extension through an intermediate field, after cancelling the
iterated base change. The conclusion is stated in ambient matrix coordinates
to avoid transporting across the propositionally equal iterated mapped form. -/
@[simp]
theorem coe_skewAdjointScalarExtensionEquiv_tower_tmul
    {L : Type*} [Field Q] [Field K] [Field L] [Algebra Q K] [Algebra K L]
    [Algebra Q L] [IsScalarTower Q K L] (F : Matrix ι ι Q) (a : L) (b : K)
    (X : skewAdjointMatricesLieSubalgebra F) :
    (skewAdjointScalarExtensionEquiv (Q := K) (K := L)
        (F.map (algebraMap Q K))
        (LinearEquiv.baseChange K L _ _
          (skewAdjointScalarExtensionEquiv (Q := Q) (K := K) F)
          (a ⊗ₜ[K] (b ⊗ₜ[Q] X))) : Matrix ι ι L) =
      (skewAdjointScalarExtensionEquiv (Q := Q) (K := L) F
        (TensorProduct.AlgebraTensorModule.cancelBaseChange Q K L L _
          (a ⊗ₜ[K] (b ⊗ₜ[Q] X))) : Matrix ι ι L) := by
  rw [LinearEquiv.baseChange_tmul, coe_skewAdjointScalarExtensionEquiv_tmul,
    coe_skewAdjointScalarExtensionEquiv_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    coe_skewAdjointScalarExtensionEquiv_tmul]
  ext i j
  simp [Matrix.map_apply, IsScalarTower.algebraMap_apply Q K L]
  rw [Algebra.smul_def]
  ring

/-- Transport a supplied basis of the skew-adjoint matrices through scalar
extension. -/
def skewAdjointScalarExtensionBasis {J : Type*}
    [Field Q] [Field K] [Algebra Q K] (F : Matrix ι ι Q)
    (b : Module.Basis J Q (skewAdjointMatricesLieSubalgebra F)) :
    Module.Basis J K (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap Q K))) :=
  (b.baseChange K).map (skewAdjointScalarExtensionEquiv (K := K) F)

@[simp]
theorem coe_skewAdjointScalarExtensionBasis_apply {J : Type*}
    [Field Q] [Field K] [Algebra Q K] (F : Matrix ι ι Q)
    (b : Module.Basis J Q (skewAdjointMatricesLieSubalgebra F)) (j : J) :
    (skewAdjointScalarExtensionBasis (K := K) F b j : Matrix ι ι K) =
      (b j : Matrix ι ι Q).map (algebraMap Q K) := by
  simp [skewAdjointScalarExtensionBasis]

/-- A supplied skew-adjoint basis has the same ambient matrices after direct
scalar extension or scalar extension through an intermediate field. -/
@[simp]
theorem coe_skewAdjointScalarExtensionBasis_tower_apply
    {J L : Type*} [Field Q] [Field K] [Field L] [Algebra Q K] [Algebra K L]
    [Algebra Q L] [IsScalarTower Q K L] (F : Matrix ι ι Q)
    (b : Module.Basis J Q (skewAdjointMatricesLieSubalgebra F)) (j : J) :
    (skewAdjointScalarExtensionBasis (Q := K) (K := L)
        (F.map (algebraMap Q K))
        (skewAdjointScalarExtensionBasis (K := K) F b) j : Matrix ι ι L) =
      (skewAdjointScalarExtensionBasis (K := L) F b j : Matrix ι ι L) := by
  simp only [skewAdjointScalarExtensionBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply]
  have h := coe_skewAdjointScalarExtensionEquiv_tower_tmul
    (F := F) (a := (1 : L)) (b := (1 : K)) (X := b j)
  rw [LinearEquiv.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul] at h
  simpa only [one_smul] using h

/-- The determinant form of a supplied skew-adjoint basis evaluates on
scalar-extended rational vectors as the scalar extension of the original
determinant. -/
theorem skewAdjointScalarExtensionBasis_det_apply
    {J : Type*} [Fintype J] [DecidableEq J]
    [Field Q] [Field K] [Algebra Q K] (F : Matrix ι ι Q)
    (b : Module.Basis J Q (skewAdjointMatricesLieSubalgebra F))
    (v : J → skewAdjointMatricesLieSubalgebra F) :
    (skewAdjointScalarExtensionBasis (K := K) F b).det
        (fun j ↦ skewAdjointScalarExtensionEquiv (K := K) F
          (1 ⊗ₜ[Q] v j)) =
      algebraMap Q K (b.det v) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp [skewAdjointScalarExtensionBasis, Module.Basis.toMatrix_apply,
    Algebra.smul_def]

/-- A fixed classical finite basis of the skew-adjoint matrices over a field.
This is not an explicit elementary matrix basis. -/
def skewAdjointFinBasis [Field Q] (F : Matrix ι ι Q) :
    Module.Basis
      (Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F))) Q
      (skewAdjointMatricesLieSubalgebra F) :=
  Module.finBasis Q (skewAdjointMatricesLieSubalgebra F)

/-- The determinant form attached to the fixed skew-adjoint finite basis. -/
def skewAdjointDetForm [Field Q] (F : Matrix ι ι Q) :
    skewAdjointMatricesLieSubalgebra F
      [⋀^Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F))]→ₗ[Q] Q :=
  (skewAdjointFinBasis F).det

theorem skewAdjointDetForm_ne_zero [Field Q] (F : Matrix ι ι Q) :
    skewAdjointDetForm F ≠ 0 :=
  (skewAdjointFinBasis F).det_ne_zero

/-- The fixed skew-adjoint basis after extension to a larger field. -/
def skewAdjointScalarExtensionFinBasis [Field Q] [Field K] [Algebra Q K]
    (F : Matrix ι ι Q) :
    Module.Basis
      (Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F))) K
      (skewAdjointMatricesLieSubalgebra (F.map (algebraMap Q K))) :=
  skewAdjointScalarExtensionBasis (K := K) F (skewAdjointFinBasis F)

/-- The determinant form of the fixed scalar-extended skew-adjoint basis. -/
def skewAdjointScalarExtensionDetForm [Field Q] [Field K] [Algebra Q K]
    (F : Matrix ι ι Q) :
    skewAdjointMatricesLieSubalgebra (F.map (algebraMap Q K))
      [⋀^Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F))]→ₗ[K] K :=
  (skewAdjointScalarExtensionFinBasis (K := K) F).det

theorem skewAdjointScalarExtensionDetForm_ne_zero
    [Field Q] [Field K] [Algebra Q K] (F : Matrix ι ι Q) :
    skewAdjointScalarExtensionDetForm (K := K) F ≠ 0 :=
  (skewAdjointScalarExtensionFinBasis (K := K) F).det_ne_zero

theorem skewAdjointScalarExtensionDetForm_apply
    [Field Q] [Field K] [Algebra Q K] (F : Matrix ι ι Q)
    (v : Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F)) →
      skewAdjointMatricesLieSubalgebra F) :
    skewAdjointScalarExtensionDetForm (K := K) F
        (fun j ↦ skewAdjointScalarExtensionEquiv (K := K) F
          (1 ⊗ₜ[Q] v j)) =
      algebraMap Q K (skewAdjointDetForm F v) := by
  exact skewAdjointScalarExtensionBasis_det_apply F
    (skewAdjointFinBasis F) v

open scoped Matrix.Norms.Operator

/-- The scalar-extended skew-adjoint determinant form as a continuous
alternating map over a complete nontrivially normed field. -/
def skewAdjointScalarExtensionContinuousDetForm
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q) :
    (skewAdjointMatricesLieSubalgebra (F.map (algebraMap Q K))).toSubmodule
      [⋀^Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F))]→L[K] K := by
  let b : Module.Basis
      (Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F))) K
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap Q K))).toSubmodule :=
    skewAdjointScalarExtensionFinBasis (K := K) F
  refine { skewAdjointScalarExtensionDetForm (K := K) F with cont := ?_ }
  have hmatrix : Continuous
      (fun v : Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F)) →
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap Q K))).toSubmodule =>
        b.toMatrix v) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simpa only [Module.Basis.toMatrix_apply] using
      (b.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)
  simpa only [skewAdjointScalarExtensionDetForm, Module.Basis.det_apply, b] using
    hmatrix.matrix_det

@[simp]
theorem skewAdjointScalarExtensionContinuousDetForm_toAlternatingMap
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q) :
    (skewAdjointScalarExtensionContinuousDetForm (K := K) F).toAlternatingMap =
      skewAdjointScalarExtensionDetForm (K := K) F :=
  rfl

theorem skewAdjointScalarExtensionContinuousDetForm_apply
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q)
    (v : Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F)) →
      skewAdjointMatricesLieSubalgebra F) :
    skewAdjointScalarExtensionContinuousDetForm (K := K) F
        (fun j ↦ skewAdjointScalarExtensionEquiv (K := K) F
          (1 ⊗ₜ[Q] v j)) =
      algebraMap Q K (skewAdjointDetForm F v) :=
  skewAdjointScalarExtensionDetForm_apply F v

theorem skewAdjointScalarExtensionContinuousDetForm_ne_zero
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q) :
    skewAdjointScalarExtensionContinuousDetForm (K := K) F ≠ 0 := by
  intro hzero
  apply skewAdjointScalarExtensionDetForm_ne_zero (K := K) F
  have := congrArg ContinuousAlternatingMap.toAlternatingMap hzero
  simpa using this

/-- The scalar-extended determinant form as a constant differential form on
the fixed skew-adjoint normed model. -/
def skewAdjointScalarExtensionCoordinateDetForm
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q) :
    (skewAdjointMatricesLieSubalgebra (F.map (algebraMap Q K))).toSubmodule →
      (skewAdjointMatricesLieSubalgebra (F.map (algebraMap Q K))).toSubmodule
        [⋀^Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F))]→L[K] K :=
  fun _ ↦ skewAdjointScalarExtensionContinuousDetForm (K := K) F

@[simp]
theorem skewAdjointScalarExtensionCoordinateDetForm_apply
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap Q K))).toSubmodule) :
    skewAdjointScalarExtensionCoordinateDetForm (K := K) F x =
      skewAdjointScalarExtensionContinuousDetForm (K := K) F :=
  rfl

theorem skewAdjointScalarExtensionCoordinateDetForm_apply_scalarExtension
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap Q K))).toSubmodule)
    (v : Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F)) →
      skewAdjointMatricesLieSubalgebra F) :
    skewAdjointScalarExtensionCoordinateDetForm (K := K) F x
        (fun j ↦ skewAdjointScalarExtensionEquiv (K := K) F
          (1 ⊗ₜ[Q] v j)) =
      algebraMap Q K (skewAdjointDetForm F v) :=
  skewAdjointScalarExtensionContinuousDetForm_apply F v

theorem skewAdjointScalarExtensionCoordinateDetForm_apply_ne_zero
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap Q K))).toSubmodule) :
    skewAdjointScalarExtensionCoordinateDetForm (K := K) F x ≠ 0 :=
  skewAdjointScalarExtensionContinuousDetForm_ne_zero F

set_option backward.isDefEq.respectTransparency false in
theorem contDiff_skewAdjointScalarExtensionCoordinateDetForm
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q) :
    ContDiff K ⊤ (skewAdjointScalarExtensionCoordinateDetForm (K := K) F) :=
  contDiff_const

theorem skewAdjointScalarExtensionCoordinateDetForm_apply_finBasis
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap Q K))).toSubmodule) :
    skewAdjointScalarExtensionCoordinateDetForm (K := K) F x
        (skewAdjointScalarExtensionFinBasis (K := K) F) = 1 := by
  let b : Module.Basis
      (Fin (Module.finrank Q (skewAdjointMatricesLieSubalgebra F))) K
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap Q K))).toSubmodule :=
    skewAdjointScalarExtensionFinBasis (K := K) F
  simpa only [skewAdjointScalarExtensionCoordinateDetForm,
    skewAdjointScalarExtensionContinuousDetForm,
    skewAdjointScalarExtensionDetForm, b] using b.det_self

set_option backward.isDefEq.respectTransparency false in
theorem extDeriv_skewAdjointScalarExtensionCoordinateDetForm
    [Field Q] [NontriviallyNormedField K] [CompleteSpace K] [Algebra Q K]
    (F : Matrix ι ι Q) :
    extDeriv (skewAdjointScalarExtensionCoordinateDetForm (K := K) F) = 0 := by
  funext x
  rw [extDeriv]
  have hfd : fderiv K
      (skewAdjointScalarExtensionCoordinateDetForm (K := K) F) x = 0 := by
    change fderiv K
      (fun _ : (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap Q K))).toSubmodule =>
          skewAdjointScalarExtensionContinuousDetForm (K := K) F) x = 0
    exact fderiv_const_apply _
  rw [hfd]
  ext v
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp

end Matrix
