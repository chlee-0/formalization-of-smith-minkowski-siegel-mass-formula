import SMSFormula.SkewAdjointBaseChange
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Linearization of the form-preserving matrix equation

This file isolates algebraically the first-order terms of the form-preserving
and determinant-one equations. It identifies their Fréchet derivatives at the
identity over a complete nontrivially normed field, then packages the
complemented kernel and actual linear range of the paired derivative. For a
symmetric form it also restricts the nonlinear constraint to symmetric
matrices, constructs a right inverse to its derivative, and gives a local
zero-fiber chart in skew-adjoint matrix coordinates. It does not construct a
manifold or Lie-group structure on either subgroup.
-/

open scoped Matrix

namespace Matrix

variable {R ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The polynomial constraint cutting out matrices that preserve `F`. -/
def formPreservingConstraint [CommRing R] (F : Matrix ι ι R) :
    Matrix ι ι R → Matrix ι ι R :=
  fun g ↦ gᵀ * F * g - F

omit [DecidableEq ι] in
@[simp]
theorem formPreservingConstraint_apply [CommRing R]
    (F g : Matrix ι ι R) :
    formPreservingConstraint F g = gᵀ * F * g - F :=
  rfl

omit [DecidableEq ι] in
theorem formPreservingConstraint_eq_zero_iff [CommRing R]
    (F g : Matrix ι ι R) :
    formPreservingConstraint F g = 0 ↔ gᵀ * F * g = F := by
  rw [formPreservingConstraint_apply, sub_eq_zero]

@[simp]
theorem formPreservingConstraint_one [CommRing R] (F : Matrix ι ι R) :
    formPreservingConstraint F 1 = 0 := by
  simp [formPreservingConstraint]

/-- Exact expansion of the form-preserving constraint along `1 + tX`.
The linear term is `skewAdjointOperator F X`; the remaining term is quadratic
in `t`. -/
theorem formPreservingConstraint_one_add_smul [CommRing R]
    (F X : Matrix ι ι R) (t : R) :
    formPreservingConstraint F (1 + t • X) =
      t • skewAdjointOperator F X + t ^ 2 • (Xᵀ * F * X) := by
  simp only [formPreservingConstraint_apply, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_smul, Matrix.add_mul,
    Matrix.mul_add, one_mul, mul_one, skewAdjointOperator_apply]
  simp only [smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, pow_two]
  module

/-- A skew-adjoint direction kills the linear term in the form-preserving
constraint. -/
theorem formPreservingConstraint_one_add_smul_of_mem_skewAdjoint
    [CommRing R] (F : Matrix ι ι R)
    (X : skewAdjointMatricesLieSubalgebra F) (t : R) :
    formPreservingConstraint F (1 + t • (X : Matrix ι ι R)) =
      t ^ 2 • ((X : Matrix ι ι R)ᵀ * F * X) := by
  rw [formPreservingConstraint_one_add_smul]
  have hX : skewAdjointOperator F (X : Matrix ι ι R) = 0 := by
    exact LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff F X).mpr X.property)
  rw [hX, smul_zero, zero_add]

/-- The subspace of symmetric square matrices. -/
def symmetricMatricesSubmodule [Semiring R] : Submodule R (Matrix ι ι R) where
  carrier := {X | X.IsSymm}
  zero_mem' := isSymm_zero
  add_mem' := fun hX hY ↦ hX.add hY
  smul_mem' := fun c _ hX ↦ hX.smul c

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem mem_symmetricMatricesSubmodule [Semiring R] (X : Matrix ι ι R) :
    X ∈ symmetricMatricesSubmodule (R := R) (ι := ι) ↔ X.IsSymm :=
  Iff.rfl

omit [DecidableEq ι] in
/-- For a symmetric form, the form-preserving constraint is symmetric. -/
theorem formPreservingConstraint_isSymm [CommRing R]
    (F : Matrix ι ι R) (hF : F.IsSymm) (g : Matrix ι ι R) :
    (formPreservingConstraint F g).IsSymm := by
  simp [formPreservingConstraint, IsSymm, Matrix.transpose_mul, hF.eq, Matrix.mul_assoc]

/-- For a symmetric form, the skew-adjoint operator takes symmetric values. -/
theorem skewAdjointOperator_isSymm [CommRing R]
    (F : Matrix ι ι R) (hF : F.IsSymm) (X : Matrix ι ι R) :
    (skewAdjointOperator F X).IsSymm := by
  simp [skewAdjointOperator_apply, IsSymm, Matrix.transpose_mul, hF.eq, add_comm]

/-- The form-preserving constraint with codomain restricted to symmetric
matrices. -/
def symmetricFormPreservingConstraint [CommRing R]
    (F : Matrix ι ι R) (hF : F.IsSymm) :
    Matrix ι ι R → symmetricMatricesSubmodule (R := R) (ι := ι) :=
  fun g ↦ ⟨formPreservingConstraint F g, formPreservingConstraint_isSymm F hF g⟩

omit [DecidableEq ι] in
@[simp]
theorem coe_symmetricFormPreservingConstraint_apply [CommRing R]
    (F : Matrix ι ι R) (hF : F.IsSymm) (g : Matrix ι ι R) :
    (symmetricFormPreservingConstraint F hF g : Matrix ι ι R) =
      formPreservingConstraint F g :=
  rfl

/-- The polynomial constraint cutting out determinant-one matrices. -/
def determinantOneConstraint [CommRing R] (g : Matrix ι ι R) : R :=
  g.det - 1

@[simp]
theorem determinantOneConstraint_apply [CommRing R] (g : Matrix ι ι R) :
    determinantOneConstraint g = g.det - 1 :=
  rfl

@[simp]
theorem determinantOneConstraint_one [CommRing R] :
    determinantOneConstraint (1 : Matrix ι ι R) = 0 := by
  simp [determinantOneConstraint]

/-- Exact determinant-one expansion along `1 + tX`; its linear term is
`trace X * t`. -/
theorem determinantOneConstraint_one_add_smul [CommRing R]
    (X : Matrix ι ι R) (t : R) :
    determinantOneConstraint (1 + t • X) =
      X.trace * t +
        (Matrix.det
          (1 + (Polynomial.X : Polynomial R) • X.map Polynomial.C)).divX.divX.eval t *
          t ^ 2 := by
  rw [determinantOneConstraint, Matrix.det_one_add_smul]
  ring

/-- For a nonsingular form in characteristic different from two, every
skew-adjoint matrix has trace zero. Thus the determinant-one first-order
condition adds no new restriction to the form-preserving linearization. -/
theorem trace_eq_zero_of_mem_skewAdjoint [Field R]
    (F : Matrix ι ι R) (hF : F.det ≠ 0) (hchar : ringChar R ≠ 2)
    (X : skewAdjointMatricesLieSubalgebra F) :
    (X : Matrix ι ι R).trace = 0 := by
  have hFdet : IsUnit F.det := isUnit_iff_ne_zero.mpr hF
  have hFunit : IsUnit F := F.isUnit_iff_isUnit_det.mpr hFdet
  have hker : skewAdjointOperator F (X : Matrix ι ι R) = 0 :=
    LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff F X).mpr X.property)
  have hEq : (X : Matrix ι ι R)ᵀ * F = -(F * X) :=
    eq_neg_of_add_eq_zero_left hker
  have hconj : F⁻¹ * (X : Matrix ι ι R)ᵀ * F = -(X : Matrix ι ι R) := by
    rw [Matrix.mul_assoc, hEq, Matrix.mul_neg, ← Matrix.mul_assoc,
      F.nonsing_inv_mul hFdet, one_mul]
  have htrace : (X : Matrix ι ι R).trace = -(X : Matrix ι ι R).trace := by
    calc
      (X : Matrix ι ι R).trace = (X : Matrix ι ι R)ᵀ.trace :=
        (Matrix.trace_transpose (X : Matrix ι ι R)).symm
      _ = (F⁻¹ * (X : Matrix ι ι R)ᵀ * F).trace :=
        (Matrix.trace_conj' hFunit (X : Matrix ι ι R)ᵀ).symm
      _ = (-(X : Matrix ι ι R)).trace := congrArg Matrix.trace hconj
      _ = -(X : Matrix ι ι R).trace := by simp
  have htwo_trace : (2 : R) * (X : Matrix ι ι R).trace = 0 := by
    calc
      (2 : R) * (X : Matrix ι ι R).trace =
          (X : Matrix ι ι R).trace + (X : Matrix ι ι R).trace := by ring
      _ = -(X : Matrix ι ι R).trace + (X : Matrix ι ι R).trace :=
        congrArg (fun z ↦ z + (X : Matrix ι ι R).trace) htrace
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp htwo_trace).resolve_left (Ring.two_ne_zero hchar)

/-- Along a skew-adjoint direction for a nonsingular form in characteristic
different from two, the determinant-one constraint has no linear term. -/
theorem determinantOneConstraint_one_add_smul_of_mem_skewAdjoint [Field R]
    (F : Matrix ι ι R) (hF : F.det ≠ 0) (hchar : ringChar R ≠ 2)
    (X : skewAdjointMatricesLieSubalgebra F) (t : R) :
    determinantOneConstraint (1 + t • (X : Matrix ι ι R)) =
      (Matrix.det
        (1 + (Polynomial.X : Polynomial R) •
          (X : Matrix ι ι R).map Polynomial.C)).divX.divX.eval t * t ^ 2 := by
  rw [determinantOneConstraint_one_add_smul,
    trace_eq_zero_of_mem_skewAdjoint F hF hchar X, zero_mul, zero_add]

/-- A matrix preserving a nonsingular form has determinant squared equal to
one. No symmetry hypothesis is needed. -/
theorem det_sq_eq_one_of_formPreservingConstraint_eq_zero [Field R]
    (F g : Matrix ι ι R) (hF : F.det ≠ 0)
    (hg : formPreservingConstraint F g = 0) : g.det ^ 2 = 1 := by
  have hdet := congrArg Matrix.det
    ((formPreservingConstraint_eq_zero_iff F g).mp hg)
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  apply mul_right_cancel₀ hF
  calc
    g.det ^ 2 * F.det = g.det * F.det * g.det := by ring
    _ = F.det := hdet
    _ = 1 * F.det := (one_mul F.det).symm

/-- The matrix-valued carrier of the determinant-one form-preserving group. -/
def specialOrthogonalMatrixSet [CommRing R] (F : Matrix ι ι R) :
    Set (Matrix ι ι R) :=
  {g | formPreservingConstraint F g = 0 ∧ g.det = 1}

@[simp]
theorem mem_specialOrthogonalMatrixSet [CommRing R]
    (F g : Matrix ι ι R) :
    g ∈ specialOrthogonalMatrixSet F ↔
      formPreservingConstraint F g = 0 ∧ g.det = 1 :=
  Iff.rfl

/-- The matrix identity as a point of the special-orthogonal carrier. -/
def specialOrthogonalMatrixIdentity [CommRing R] (F : Matrix ι ι R) :
    specialOrthogonalMatrixSet F :=
  ⟨1, formPreservingConstraint_one F, det_one⟩

section Analytic

open scoped Matrix.Norms.Operator Topology

open Filter

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

noncomputable local instance : CompleteSpace (Matrix ι ι K) :=
  FiniteDimensional.complete K _

noncomputable local instance :
    CompleteSpace (symmetricMatricesSubmodule (R := K) (ι := ι)) :=
  FiniteDimensional.complete K _

/-- Matrix transpose as a continuous linear map for the operator norm. -/
noncomputable def transposeContinuousLinearMap :
    Matrix ι ι K →L[K] Matrix ι ι K :=
  ⟨(transposeLinearEquiv ι ι K K).toLinearMap,
    (transposeLinearEquiv ι ι K K).toLinearMap.continuous_of_finiteDimensional⟩

omit [DecidableEq ι] in
@[simp]
theorem transposeContinuousLinearMap_apply (X : Matrix ι ι K) :
    transposeContinuousLinearMap X = Xᵀ :=
  rfl

/-- The skew-adjoint operator as a continuous linear map for the operator norm. -/
noncomputable def skewAdjointOperatorContinuousLinearMap (F : Matrix ι ι K) :
    Matrix ι ι K →L[K] Matrix ι ι K :=
  ⟨skewAdjointOperator F,
    (skewAdjointOperator F).continuous_of_finiteDimensional⟩

@[simp]
theorem skewAdjointOperatorContinuousLinearMap_toLinearMap (F : Matrix ι ι K) :
    (skewAdjointOperatorContinuousLinearMap F).toLinearMap = skewAdjointOperator F :=
  rfl

@[simp]
theorem skewAdjointOperatorContinuousLinearMap_apply (F X : Matrix ι ι K) :
    skewAdjointOperatorContinuousLinearMap F X = Xᵀ * F + F * X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Over every complete nontrivially normed field, the Fréchet derivative at
the identity of the form-preserving constraint is the skew-adjoint operator. -/
theorem hasFDerivAt_formPreservingConstraint_one (F : Matrix ι ι K) :
    HasFDerivAt (formPreservingConstraint F)
      (skewAdjointOperatorContinuousLinearMap F) 1 := by
  have htranspose : HasFDerivAt (fun g : Matrix ι ι K ↦ gᵀ)
      transposeContinuousLinearMap 1 := by
    simpa [transposeContinuousLinearMap] using
      (transposeContinuousLinearMap (K := K) (ι := ι)).hasFDerivAt
  convert ((htranspose.mul_const' F).mul' (hasFDerivAt_id 1)).sub_const F using 1
  ext X i j
  simp [skewAdjointOperatorContinuousLinearMap_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, add_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The form-preserving constraint is strictly Fréchet differentiable at the
identity, with derivative the skew-adjoint operator. -/
theorem hasStrictFDerivAt_formPreservingConstraint_one (F : Matrix ι ι K) :
    HasStrictFDerivAt (formPreservingConstraint F)
      (skewAdjointOperatorContinuousLinearMap F) 1 := by
  have htranspose : HasStrictFDerivAt (fun g : Matrix ι ι K ↦ gᵀ)
      transposeContinuousLinearMap 1 := by
    simpa [transposeContinuousLinearMap] using
      (transposeContinuousLinearMap (K := K) (ι := ι)).hasStrictFDerivAt
  convert ((htranspose.mul_const' F).mul' (hasStrictFDerivAt_id 1)).sub_const F using 1
  ext X i j
  simp [skewAdjointOperatorContinuousLinearMap_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, add_comm]

omit [CompleteSpace K] in
/-- A Leibniz-formula bound used to make the determinant alternating map
continuous on finite row spaces. -/
theorem norm_det_le_card_perm_mul_prod_row_norm (M : Matrix ι ι K) :
    ‖M.det‖ ≤ Fintype.card (Equiv.Perm ι) * ∏ i, ‖M i‖ := by
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ ≤
        ∑ σ : Equiv.Perm ι, ∏ i, ‖M (σ i)‖ := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hsign (z : K) : ‖Equiv.Perm.sign σ • z‖ = ‖z‖ := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
      rw [hsign, norm_prod]
      refine Finset.prod_le_prod (fun i hi ↦ norm_nonneg _) ?_
      intro i hi
      exact norm_le_pi_norm (M (σ i)) i
    _ = ∑ _σ : Equiv.Perm ι, ∏ i, ‖M i‖ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact Equiv.prod_comp σ (fun i ↦ ‖M i‖)
    _ = Fintype.card (Equiv.Perm ι) * ∏ i, ‖M i‖ := by simp

/-- The determinant as a continuous alternating map in the matrix rows. -/
noncomputable def detRowContinuousAlternatingMap :
    (ι → K) [⋀^ι]→L[K] K :=
  (detRowAlternating : (ι → K) [⋀^ι]→ₗ[K] K).mkContinuous
    (Fintype.card (Equiv.Perm ι)) norm_det_le_card_perm_mul_prod_row_norm

omit [CompleteSpace K] in
@[simp]
theorem detRowContinuousAlternatingMap_apply (M : Matrix ι ι K) :
    detRowContinuousAlternatingMap M = M.det :=
  rfl

/-- Matrix trace as a continuous linear map for the operator norm. -/
noncomputable def traceContinuousLinearMap : Matrix ι ι K →L[K] K :=
  ⟨traceLinearMap ι K K, (traceLinearMap ι K K).continuous_of_finiteDimensional⟩

omit [DecidableEq ι] in
@[simp]
theorem traceContinuousLinearMap_apply (M : Matrix ι ι K) :
    traceContinuousLinearMap M = M.trace :=
  rfl

omit [CompleteSpace K] in
private theorem det_updateRow_one (X : Matrix ι ι K) (i : ι) :
    Matrix.det (Function.update (1 : Matrix ι ι K) i (X i)) = X i i := by
  rw [show Function.update (1 : Matrix ι ι K) i (X i) =
      (1 : Matrix ι ι K).updateRow i (∑ k, (X i k) • (1 : Matrix ι ι K) k) by
    ext j k
    by_cases hji : j = i
    · subst j
      simpa [Matrix.mul_apply] using
        (congrArg (fun M : Matrix ι ι K ↦ M i k) (Matrix.mul_one X)).symm
    · simp [hji]]
  rw [det_updateRow_sum, det_one]
  simp

/-- The Fréchet derivative of matrix determinant at the identity is trace. -/
theorem hasFDerivAt_det_one :
    HasFDerivAt (det : Matrix ι ι K → K) traceContinuousLinearMap 1 := by
  convert (detRowContinuousAlternatingMap (K := K) (ι := ι)).toContinuousMultilinearMap
    |>.hasFDerivAt (1 : Matrix ι ι K) using 1
  ext X
  rw [traceContinuousLinearMap_apply]
  calc
    X.trace = ∑ i, detRowContinuousAlternatingMap
        (Function.update (1 : Matrix ι ι K) i (X i)) := by
      simp only [detRowContinuousAlternatingMap_apply, det_updateRow_one]
      rfl
    _ = _ := (ContinuousMultilinearMap.linearDeriv_apply
      (f := (detRowContinuousAlternatingMap (K := K) (ι := ι)).toContinuousMultilinearMap)
      (x := (1 : Matrix ι ι K)) (y := X)).symm

/-- The Fréchet derivative of the determinant-one constraint at the identity
is trace. -/
theorem hasFDerivAt_determinantOneConstraint_one :
    HasFDerivAt (determinantOneConstraint : Matrix ι ι K → K)
      traceContinuousLinearMap 1 := by
  convert (hasFDerivAt_det_one (K := K) (ι := ι)).sub_const 1 using 1

/-- The paired equations cutting out determinant-one form-preserving matrices
inside the ambient matrix space. -/
def specialOrthogonalConstraint (F g : Matrix ι ι K) : Matrix ι ι K × K :=
  (formPreservingConstraint F g, determinantOneConstraint g)

/-- The continuous linear map obtained by pairing the skew-adjoint and trace
operators. -/
noncomputable def specialOrthogonalConstraintDerivative (F : Matrix ι ι K) :
    Matrix ι ι K →L[K] Matrix ι ι K × K :=
  (skewAdjointOperatorContinuousLinearMap F).prod traceContinuousLinearMap

@[simp]
theorem specialOrthogonalConstraintDerivative_apply (F X : Matrix ι ι K) :
    specialOrthogonalConstraintDerivative F X =
      (skewAdjointOperator F X, X.trace) :=
  rfl

/-- The derivative at the identity of the paired special-orthogonal
constraint. -/
theorem hasFDerivAt_specialOrthogonalConstraint_one (F : Matrix ι ι K) :
    HasFDerivAt (specialOrthogonalConstraint F)
      (specialOrthogonalConstraintDerivative F) 1 := by
  exact (hasFDerivAt_formPreservingConstraint_one F).prodMk
    hasFDerivAt_determinantOneConstraint_one

/-- For a nonsingular form in characteristic different from two, adding trace
to the skew-adjoint operator does not change its kernel. -/
theorem ker_specialOrthogonalConstraintDerivative (F : Matrix ι ι K)
    (hF : F.det ≠ 0) (hchar : ringChar K ≠ 2) :
    LinearMap.ker (specialOrthogonalConstraintDerivative F).toLinearMap =
      LinearMap.ker (skewAdjointOperator F) := by
  ext X
  change (skewAdjointOperator F X, X.trace) = 0 ↔ skewAdjointOperator F X = 0
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    apply Prod.ext
    · exact h
    · change X.trace = 0
      exact trace_eq_zero_of_mem_skewAdjoint F hF hchar
        ⟨X, (mem_ker_skewAdjointOperator_iff F X).mp h⟩

/-- The kernel of the ambient special-orthogonal derivative, identified with
the skew-adjoint matrix Lie subalgebra. -/
noncomputable def specialOrthogonalConstraintDerivativeKerEquiv (F : Matrix ι ι K)
    (hF : F.det ≠ 0) (hchar : ringChar K ≠ 2) :
    LinearMap.ker (specialOrthogonalConstraintDerivative F).toLinearMap ≃ₗ[K]
      skewAdjointMatricesLieSubalgebra F :=
  LinearEquiv.ofEq _ _ (ker_specialOrthogonalConstraintDerivative F hF hchar) ≪≫ₗ
    skewAdjointOperatorKerEquiv F

@[simp]
theorem coe_specialOrthogonalConstraintDerivativeKerEquiv_apply
    (F : Matrix ι ι K) (hF : F.det ≠ 0) (hchar : ringChar K ≠ 2)
    (X : LinearMap.ker (specialOrthogonalConstraintDerivative F).toLinearMap) :
    (specialOrthogonalConstraintDerivativeKerEquiv F hF hchar X : Matrix ι ι K) = X :=
  rfl

/-- The kernel of the ambient special-orthogonal derivative is continuously
complemented. This is the splitting hypothesis used by Mathlib's implicit
function theorem. -/
theorem specialOrthogonalConstraintDerivative_ker_closedComplemented
    (F : Matrix ι ι K) :
    (specialOrthogonalConstraintDerivative F).ker.ClosedComplemented :=
  (specialOrthogonalConstraintDerivative F).ker_closedComplemented_of_finiteDimensional_range

/-- A continuous projection from ambient matrices onto the kernel of the
special-orthogonal derivative. -/
noncomputable def specialOrthogonalConstraintKernelProjection (F : Matrix ι ι K) :
    Matrix ι ι K →L[K] (specialOrthogonalConstraintDerivative F).ker :=
  Classical.choose (specialOrthogonalConstraintDerivative_ker_closedComplemented F)

@[simp]
theorem specialOrthogonalConstraintKernelProjection_apply
    (F : Matrix ι ι K)
    (X : (specialOrthogonalConstraintDerivative F).ker) :
    specialOrthogonalConstraintKernelProjection F X = X :=
  Classical.choose_spec (specialOrthogonalConstraintDerivative_ker_closedComplemented F) X

/-- The actual linear range of the paired special-orthogonal derivative. -/
noncomputable abbrev specialOrthogonalConstraintDerivativeRange (F : Matrix ι ι K) :=
  (specialOrthogonalConstraintDerivative F).range

/-- The paired derivative with its codomain restricted to its actual range. -/
noncomputable def specialOrthogonalConstraintDerivativeRangeMap (F : Matrix ι ι K) :
    Matrix ι ι K →L[K] specialOrthogonalConstraintDerivativeRange F :=
  (specialOrthogonalConstraintDerivative F).rangeRestrict

@[simp]
theorem coe_specialOrthogonalConstraintDerivativeRangeMap_apply
    (F X : Matrix ι ι K) :
    (specialOrthogonalConstraintDerivativeRangeMap F X : Matrix ι ι K × K) =
      (skewAdjointOperator F X, X.trace) :=
  rfl

/-- Restriction to the actual derivative range makes the derivative
surjective. -/
theorem specialOrthogonalConstraintDerivativeRangeMap_range_eq_top
    (F : Matrix ι ι K) :
    LinearMap.range (specialOrthogonalConstraintDerivativeRangeMap F).toLinearMap = ⊤ := by
  exact LinearMap.range_rangeRestrict _

@[simp]
theorem ker_specialOrthogonalConstraintDerivativeRangeMap
    (F : Matrix ι ι K) :
    LinearMap.ker (specialOrthogonalConstraintDerivativeRangeMap F).toLinearMap =
      LinearMap.ker (specialOrthogonalConstraintDerivative F).toLinearMap := by
  change (specialOrthogonalConstraintDerivative F).toLinearMap.rangeRestrict.ker = _
  exact (specialOrthogonalConstraintDerivative F).toLinearMap.ker_rangeRestrict

/-- For a nonsingular form in characteristic different from two, the paired
derivative is not surjective onto the full matrix-product codomain. -/
theorem specialOrthogonalConstraintDerivative_range_ne_top
    (F : Matrix ι ι K) (hF : F.det ≠ 0) (hchar : ringChar K ≠ 2) :
    LinearMap.range (specialOrthogonalConstraintDerivative F).toLinearMap ≠ ⊤ := by
  intro htop
  have hsurj : Function.Surjective
      (specialOrthogonalConstraintDerivative F).toLinearMap :=
    LinearMap.range_eq_top.mp htop
  obtain ⟨X, hX⟩ := hsurj (0, 1)
  have hskew : skewAdjointOperator F X = 0 := congrArg Prod.fst hX
  have htrace : X.trace = 0 :=
    trace_eq_zero_of_mem_skewAdjoint F hF hchar
      ⟨X, (mem_ker_skewAdjointOperator_iff F X).mp hskew⟩
  have hone : X.trace = 1 := congrArg Prod.snd hX
  exact zero_ne_one (htrace.symm.trans hone)

/-- The skew-adjoint operator with codomain restricted to symmetric matrices. -/
noncomputable def symmetricSkewAdjointOperatorContinuousLinearMap
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    Matrix ι ι K →L[K] symmetricMatricesSubmodule (R := K) (ι := ι) :=
  (skewAdjointOperatorContinuousLinearMap F).codRestrict _
    (skewAdjointOperator_isSymm F hF)

@[simp]
theorem coe_symmetricSkewAdjointOperatorContinuousLinearMap_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (X : Matrix ι ι K) :
    (symmetricSkewAdjointOperatorContinuousLinearMap F hF X : Matrix ι ι K) =
      skewAdjointOperator F X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The derivative at the identity of the symmetric-valued form constraint. -/
theorem hasFDerivAt_symmetricFormPreservingConstraint_one
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    HasFDerivAt (symmetricFormPreservingConstraint F hF)
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF) 1 := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [
    (hasFDerivAt_formPreservingConstraint_one F).isLittleO.bound hc] with x hx
  change ‖((symmetricFormPreservingConstraint F hF x -
    symmetricFormPreservingConstraint F hF 1 -
    symmetricSkewAdjointOperatorContinuousLinearMap F hF (x - 1) :
      symmetricMatricesSubmodule (R := K) (ι := ι)) : Matrix ι ι K)‖ ≤
        c * ‖x - 1‖
  rw [show ((symmetricFormPreservingConstraint F hF x -
      symmetricFormPreservingConstraint F hF 1 -
      symmetricSkewAdjointOperatorContinuousLinearMap F hF (x - 1) :
        symmetricMatricesSubmodule (R := K) (ι := ι)) : Matrix ι ι K) =
      formPreservingConstraint F x - formPreservingConstraint F 1 -
        skewAdjointOperator F (x - 1) by rfl]
  exact hx

set_option backward.isDefEq.respectTransparency false in
/-- The symmetric-valued form constraint is strictly Fréchet differentiable
at the identity, with the restricted skew-adjoint derivative. -/
theorem hasStrictFDerivAt_symmetricFormPreservingConstraint_one
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    HasStrictFDerivAt (symmetricFormPreservingConstraint F hF)
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF) 1 := by
  constructor
  rw [Asymptotics.isLittleOTVS_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [
    (hasStrictFDerivAt_formPreservingConstraint_one F).isLittleO.bound hc] with p hp
  change ‖((symmetricFormPreservingConstraint F hF p.1 -
    symmetricFormPreservingConstraint F hF p.2 -
    symmetricSkewAdjointOperatorContinuousLinearMap F hF (p.1 - p.2) :
      symmetricMatricesSubmodule (R := K) (ι := ι)) : Matrix ι ι K)‖ ≤
        c * ‖p.1 - p.2‖
  rw [show ((symmetricFormPreservingConstraint F hF p.1 -
      symmetricFormPreservingConstraint F hF p.2 -
      symmetricSkewAdjointOperatorContinuousLinearMap F hF (p.1 - p.2) :
        symmetricMatricesSubmodule (R := K) (ι := ι)) : Matrix ι ι K) =
      formPreservingConstraint F p.1 - formPreservingConstraint F p.2 -
        skewAdjointOperator F (p.1 - p.2) by rfl]
  exact hp

/-- The kernel of the symmetric-valued derivative is continuously
complemented, as required by the implicit-function theorem. -/
theorem symmetricSkewAdjointOperator_ker_closedComplemented
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker.ClosedComplemented :=
  (symmetricSkewAdjointOperatorContinuousLinearMap F hF)
    |>.ker_closedComplemented_of_finiteDimensional_range

/-- The algebraic right inverse `Y ↦ 2⁻¹ • (F⁻¹ * Y)` for the symmetric-valued
skew-adjoint operator. -/
noncomputable def symmetricSkewAdjointOperatorRightInverseLinearMap
    (F : Matrix ι ι K) :
    symmetricMatricesSubmodule (R := K) (ι := ι) →ₗ[K] Matrix ι ι K :=
  (2 : K)⁻¹ • (LinearMap.mulLeft K F⁻¹).comp
    (symmetricMatricesSubmodule (R := K) (ι := ι)).subtype

omit [CompleteSpace K] in
@[simp]
theorem symmetricSkewAdjointOperatorRightInverseLinearMap_apply
    (F : Matrix ι ι K) (Y : symmetricMatricesSubmodule (R := K) (ι := ι)) :
    symmetricSkewAdjointOperatorRightInverseLinearMap F Y =
      (2 : K)⁻¹ • (F⁻¹ * (Y : Matrix ι ι K)) :=
  rfl

/-- The continuous right-inverse candidate for the symmetric-valued
skew-adjoint operator. -/
noncomputable def symmetricSkewAdjointOperatorRightInverse
    (F : Matrix ι ι K) :
    symmetricMatricesSubmodule (R := K) (ι := ι) →L[K] Matrix ι ι K :=
  ⟨symmetricSkewAdjointOperatorRightInverseLinearMap F,
    (symmetricSkewAdjointOperatorRightInverseLinearMap F).continuous_of_finiteDimensional⟩

@[simp]
theorem symmetricSkewAdjointOperatorRightInverse_apply
    (F : Matrix ι ι K) (Y : symmetricMatricesSubmodule (R := K) (ι := ι)) :
    symmetricSkewAdjointOperatorRightInverse F Y =
      (2 : K)⁻¹ • (F⁻¹ * (Y : Matrix ι ι K)) :=
  rfl

/-- For a symmetric nonsingular form in characteristic different from two,
the displayed map is a right inverse to the restricted derivative. -/
theorem symmetricSkewAdjointOperator_rightInverse
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Function.RightInverse (symmetricSkewAdjointOperatorRightInverse F)
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF) := by
  intro Y
  apply Subtype.ext
  simp only [coe_symmetricSkewAdjointOperatorContinuousLinearMap_apply,
    symmetricSkewAdjointOperatorRightInverse_apply, skewAdjointOperator_apply,
    Matrix.transpose_smul, Matrix.transpose_mul, Y.property.eq,
    F.transpose_nonsing_inv, hF.eq]
  have hunit : IsUnit F.det := isUnit_iff_ne_zero.mpr hdet
  rw [smul_mul, Matrix.mul_smul,
    Matrix.nonsing_inv_mul_cancel_right (A := F) (Y : Matrix ι ι K) hunit,
    Matrix.mul_nonsing_inv_cancel_left (A := F) (Y : Matrix ι ι K) hunit]
  rw [← add_smul]
  have hhalf : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ (Ring.two_ne_zero hchar)]
  rw [hhalf, one_smul]

/-- The derivative of the symmetric-valued form constraint is surjective for
a symmetric nonsingular form in characteristic different from two. -/
theorem symmetricSkewAdjointOperator_range_eq_top
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    LinearMap.range (symmetricSkewAdjointOperatorContinuousLinearMap F hF).toLinearMap = ⊤ := by
  rw [LinearMap.range_eq_top]
  exact (symmetricSkewAdjointOperator_rightInverse F hF hdet hchar).surjective

/-- The implicit-function chart at the identity for the symmetric-valued
form-preserving constraint. Its first coordinate is the constraint, while its
second coordinate lies in the skew-adjoint derivative kernel. -/
noncomputable def symmetricFormPreservingIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    OpenPartialHomeomorph (Matrix ι ι K)
      (symmetricMatricesSubmodule (R := K) (ι := ι) ×
        (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  (hasStrictFDerivAt_symmetricFormPreservingConstraint_one F hF)
    |>.implicitToOpenPartialHomeomorphOfComplemented
      (symmetricFormPreservingConstraint F hF)
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF)
      (symmetricSkewAdjointOperator_range_eq_top F hF hdet hchar)
      (symmetricSkewAdjointOperator_ker_closedComplemented F hF)

@[simp]
theorem symmetricFormPreservingIdentityChart_fst
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : Matrix ι ι K) :
    (symmetricFormPreservingIdentityChart F hF hdet hchar g).fst =
      symmetricFormPreservingConstraint F hF g :=
  rfl

/-- The identity belongs to the source of the implicit-function chart. -/
theorem one_mem_symmetricFormPreservingIdentityChart_source
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (1 : Matrix ι ι K) ∈
      (symmetricFormPreservingIdentityChart F hF hdet hchar).source := by
  exact (hasStrictFDerivAt_symmetricFormPreservingConstraint_one F hF)
    |>.mem_implicitToOpenPartialHomeomorphOfComplemented_source
      (symmetricSkewAdjointOperator_range_eq_top F hF hdet hchar)
      (symmetricSkewAdjointOperator_ker_closedComplemented F hF)

set_option backward.isDefEq.respectTransparency false in
/-- The chart sends the matrix identity to the two zero coordinates. -/
@[simp]
theorem symmetricFormPreservingIdentityChart_one
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    symmetricFormPreservingIdentityChart F hF hdet hchar 1 = (0, 0) := by
  rw [symmetricFormPreservingIdentityChart]
  rw [HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_self]
  apply Prod.ext
  · apply Subtype.ext
    simp
  · rfl

/-- The zero constraint and zero kernel coordinate belong to the chart target. -/
theorem zero_mem_symmetricFormPreservingIdentityChart_target
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (0, 0) ∈
      (symmetricFormPreservingIdentityChart F hF hdet hchar).target := by
  have h := (symmetricFormPreservingIdentityChart F hF hdet hchar).map_source
    (one_mem_symmetricFormPreservingIdentityChart_source F hF hdet hchar)
  simpa only [symmetricFormPreservingIdentityChart_one] using h

omit [CompleteSpace K] in
/-- The open determinant component containing the matrix identity when the
characteristic is not two. -/
def determinantOneIdentityNeighborhood : Set (Matrix ι ι K) :=
  {g | g.det ≠ -1}

omit [CompleteSpace K] in
@[simp]
theorem mem_determinantOneIdentityNeighborhood (g : Matrix ι ι K) :
    g ∈ determinantOneIdentityNeighborhood (K := K) (ι := ι) ↔ g.det ≠ -1 :=
  Iff.rfl

omit [CompleteSpace K] in
/-- The determinant component excluding `-1` is open. -/
theorem isOpen_determinantOneIdentityNeighborhood :
    IsOpen (determinantOneIdentityNeighborhood (K := K) (ι := ι)) := by
  change IsOpen ((fun g : Matrix ι ι K ↦
    detRowContinuousAlternatingMap g) ⁻¹' ({(-1 : K)}ᶜ))
  exact isOpen_compl_singleton.preimage
    (detRowContinuousAlternatingMap (K := K) (ι := ι)).toContinuousMultilinearMap.cont

omit [CompleteSpace K] in
/-- In characteristic different from two, the determinant component contains
the matrix identity. -/
theorem one_mem_determinantOneIdentityNeighborhood
    (hchar : ringChar K ≠ 2) :
    (1 : Matrix ι ι K) ∈
      determinantOneIdentityNeighborhood (K := K) (ι := ι) := by
  rw [mem_determinantOneIdentityNeighborhood, det_one]
  intro h
  have htwo : (2 : K) = 0 := by linear_combination h
  exact Ring.two_ne_zero hchar htwo

omit [CompleteSpace K] in
/-- On the determinant component excluding `-1`, preserving a nonsingular
form forces determinant one. -/
theorem det_eq_one_of_mem_determinantOneIdentityNeighborhood
    (F g : Matrix ι ι K) (hF : F.det ≠ 0)
    (hgU : g ∈ determinantOneIdentityNeighborhood (K := K) (ι := ι))
    (hg : formPreservingConstraint F g = 0) : g.det = 1 := by
  rcases sq_eq_one_iff.mp
      (det_sq_eq_one_of_formPreservingConstraint_eq_zero F g hF hg) with h | h
  · exact h
  · exact (hgU h).elim

omit [CompleteSpace K] in
/-- Near the identity, every matrix preserving a nonsingular form has
determinant one. This isolates the local determinant-one component of the
form-preserving zero locus. -/
theorem eventually_det_eq_one_of_formPreservingConstraint_eq_zero
    (F : Matrix ι ι K) (hF : F.det ≠ 0) (hchar : ringChar K ≠ 2) :
    ∀ᶠ g : Matrix ι ι K in 𝓝 1,
      formPreservingConstraint F g = 0 → g.det = 1 := by
  filter_upwards [isOpen_determinantOneIdentityNeighborhood.mem_nhds
    (one_mem_determinantOneIdentityNeighborhood hchar)] with g hgU hg
  exact det_eq_one_of_mem_determinantOneIdentityNeighborhood F g hF hgU hg

/-- The form-preserving identity chart restricted to the open determinant
component containing the identity. -/
noncomputable def symmetricFormPreservingDetOneIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    OpenPartialHomeomorph (Matrix ι ι K)
      (symmetricMatricesSubmodule (R := K) (ι := ι) ×
        (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  (symmetricFormPreservingIdentityChart F hF hdet hchar).restrOpen
    determinantOneIdentityNeighborhood
    isOpen_determinantOneIdentityNeighborhood

@[simp]
theorem symmetricFormPreservingDetOneIdentityChart_fst
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : Matrix ι ι K) :
    (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar g).fst =
      symmetricFormPreservingConstraint F hF g :=
  rfl

@[simp]
theorem symmetricFormPreservingDetOneIdentityChart_source
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).source =
      (symmetricFormPreservingIdentityChart F hF hdet hchar).source ∩
        determinantOneIdentityNeighborhood :=
  rfl

/-- The restricted chart source still contains the matrix identity. -/
theorem one_mem_symmetricFormPreservingDetOneIdentityChart_source
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (1 : Matrix ι ι K) ∈
      (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).source := by
  rw [symmetricFormPreservingDetOneIdentityChart_source]
  exact ⟨one_mem_symmetricFormPreservingIdentityChart_source F hF hdet hchar,
    one_mem_determinantOneIdentityNeighborhood hchar⟩

/-- Every zero-first-coordinate point in the restricted chart source has
determinant one. -/
theorem det_eq_one_of_mem_symmetricFormPreservingDetOneIdentityChart_source_of_fst_eq_zero
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : Matrix ι ι K)
    (hg : g ∈ (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).source)
    (hzero : (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar g).fst = 0) :
    g.det = 1 := by
  rw [symmetricFormPreservingDetOneIdentityChart_source] at hg
  have hconstraint : formPreservingConstraint F g = 0 := by
    rw [symmetricFormPreservingDetOneIdentityChart_fst] at hzero
    exact congrArg Subtype.val hzero
  exact det_eq_one_of_mem_determinantOneIdentityNeighborhood
    F g hdet hg.2 hconstraint

/-- The zero-constraint fiber in the determinant-one identity chart source. -/
def specialOrthogonalIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) : Set (Matrix ι ι K) :=
  {g | g ∈ (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).source ∧
    (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar g).fst = 0}

/-- Kernel coordinates whose zero-constraint pair lies in the determinant-one
identity chart target. -/
def specialOrthogonalIdentityKernelNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Set (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker :=
  {y | (0, y) ∈ (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).target}

/-- The available skew-adjoint kernel coordinates form an open set. -/
theorem isOpen_specialOrthogonalIdentityKernelNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    IsOpen (specialOrthogonalIdentityKernelNeighborhood F hF hdet hchar) := by
  exact (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).open_target.preimage
    (continuous_const.prodMk continuous_id)

@[simp]
theorem symmetricFormPreservingDetOneIdentityChart_one
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    symmetricFormPreservingDetOneIdentityChart F hF hdet hchar 1 = (0, 0) :=
  symmetricFormPreservingIdentityChart_one F hF hdet hchar

/-- The zero coordinate pair lies in the determinant-one chart target. -/
theorem zero_mem_symmetricFormPreservingDetOneIdentityChart_target
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (0, 0) ∈ (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).target := by
  have h := (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).map_source
    (one_mem_symmetricFormPreservingDetOneIdentityChart_source F hF hdet hchar)
  simpa only [symmetricFormPreservingDetOneIdentityChart_one] using h

/-- Zero belongs to the open kernel-coordinate neighborhood. -/
theorem zero_mem_specialOrthogonalIdentityKernelNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (0 : (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) ∈
      specialOrthogonalIdentityKernelNeighborhood F hF hdet hchar :=
  zero_mem_symmetricFormPreservingDetOneIdentityChart_target F hF hdet hchar

/-- The matrix identity belongs to the local special-orthogonal zero fiber. -/
theorem one_mem_specialOrthogonalIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (1 : Matrix ι ι K) ∈ specialOrthogonalIdentityZeroFiber F hF hdet hchar :=
  ⟨one_mem_symmetricFormPreservingDetOneIdentityChart_source F hF hdet hchar,
    by rw [symmetricFormPreservingDetOneIdentityChart_one]⟩

private def specialOrthogonalIdentityProductZeroSlice
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Set (symmetricMatricesSubmodule (R := K) (ι := ι) ×
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  {p | p ∈ (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).target ∧
    p.1 = 0}

private theorem image_specialOrthogonalIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    symmetricFormPreservingDetOneIdentityChart F hF hdet hchar ''
        specialOrthogonalIdentityZeroFiber F hF hdet hchar =
      specialOrthogonalIdentityProductZeroSlice F hF hdet hchar := by
  let e := symmetricFormPreservingDetOneIdentityChart F hF hdet hchar
  ext p
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨e.mapsTo hg.1, hg.2⟩
  · rintro hp
    refine ⟨e.symm p, ?_, e.right_inv hp.1⟩
    exact ⟨e.map_target hp.1, by rw [e.right_inv hp.1]; exact hp.2⟩

private noncomputable def specialOrthogonalIdentityProductZeroSliceHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalIdentityProductZeroSlice F hF hdet hchar ≃ₜ
      specialOrthogonalIdentityKernelNeighborhood F hF hdet hchar where
  toFun p := ⟨p.1.2, by
    rw [specialOrthogonalIdentityKernelNeighborhood, ← p.2.2]
    exact p.2.1⟩
  invFun y := ⟨(0, y.1), y.2, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact p.2.2.symm
    · rfl
  right_inv y := rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_snd.comp continuous_subtype_val) (fun p => by
      rw [specialOrthogonalIdentityKernelNeighborhood, ← p.2.2]
      exact p.2.1)
  continuous_invFun := Continuous.subtype_mk
    (continuous_const.prodMk continuous_subtype_val) (fun y => ⟨y.2, rfl⟩)

/-- The determinant-one form-preserving zero fiber near the identity is
homeomorphic to an open neighborhood of zero in the skew-adjoint derivative
kernel. -/
noncomputable def specialOrthogonalIdentityZeroFiberHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalIdentityZeroFiber F hF hdet hchar ≃ₜ
      specialOrthogonalIdentityKernelNeighborhood F hF hdet hchar :=
  ((symmetricFormPreservingDetOneIdentityChart F hF hdet hchar)
    |>.homeomorphOfImageSubsetSource (fun _ hg ↦ hg.1)
      (image_specialOrthogonalIdentityZeroFiber F hF hdet hchar)).trans
    (specialOrthogonalIdentityProductZeroSliceHomeomorph F hF hdet hchar)

@[simp]
theorem specialOrthogonalIdentityZeroFiberHomeomorph_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialOrthogonalIdentityZeroFiber F hF hdet hchar) :
    (specialOrthogonalIdentityZeroFiberHomeomorph F hF hdet hchar g :
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) =
        (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar g).snd :=
  rfl

/-- Restricting the skew-adjoint operator's codomain to symmetric matrices
does not change its kernel. -/
theorem ker_symmetricSkewAdjointOperatorContinuousLinearMap
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    LinearMap.ker (symmetricSkewAdjointOperatorContinuousLinearMap F hF).toLinearMap =
      LinearMap.ker (skewAdjointOperator F) := by
  ext X
  change (⟨skewAdjointOperator F X, skewAdjointOperator_isSymm F hF X⟩ :
    symmetricMatricesSubmodule (R := K) (ι := ι)) = 0 ↔
      skewAdjointOperator F X = 0
  exact Subtype.ext_iff

/-- The symmetric derivative kernel identified with the underlying submodule
of Mathlib's skew-adjoint matrix Lie subalgebra. -/
noncomputable def symmetricSkewAdjointOperatorKerEquiv
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker ≃ₗ[K]
      (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
  LinearEquiv.ofEq _ _
      (ker_symmetricSkewAdjointOperatorContinuousLinearMap F hF) ≪≫ₗ
    skewAdjointOperatorKerEquiv F

/-- The symmetric derivative kernel and skew-adjoint submodule are
continuously linearly equivalent for the induced operator norms. -/
noncomputable def symmetricSkewAdjointOperatorKerContinuousLinearEquiv
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker ≃L[K]
      (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
  (symmetricSkewAdjointOperatorKerEquiv F hF).toContinuousLinearEquiv

@[simp]
theorem coe_symmetricSkewAdjointOperatorKerContinuousLinearEquiv_apply
    (F : Matrix ι ι K) (hF : F.IsSymm)
    (X : (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :
    (symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF X :
      Matrix ι ι K) = X :=
  rfl

/-- The skew-adjoint coordinates available in the local special-orthogonal
identity chart. -/
def specialOrthogonalIdentitySkewAdjointNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Set ((skewAdjointMatricesLieSubalgebra F).toSubmodule) :=
  symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF ''
    specialOrthogonalIdentityKernelNeighborhood F hF hdet hchar

/-- The available skew-adjoint coordinates form an open set. -/
theorem isOpen_specialOrthogonalIdentitySkewAdjointNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    IsOpen (specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar) := by
  exact (symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF).toHomeomorph
    |>.isOpen_image.mpr
      (isOpen_specialOrthogonalIdentityKernelNeighborhood F hF hdet hchar)

/-- Zero belongs to the open skew-adjoint coordinate neighborhood. -/
theorem zero_mem_specialOrthogonalIdentitySkewAdjointNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (0 : (skewAdjointMatricesLieSubalgebra F).toSubmodule) ∈
      specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar := by
  refine ⟨0,
    zero_mem_specialOrthogonalIdentityKernelNeighborhood F hF hdet hchar, ?_⟩
  exact map_zero (symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF)

/-- The local special-orthogonal zero fiber in skew-adjoint matrix
coordinates. -/
noncomputable def specialOrthogonalIdentityZeroFiberSkewAdjointHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalIdentityZeroFiber F hF hdet hchar ≃ₜ
      specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar :=
  (specialOrthogonalIdentityZeroFiberHomeomorph F hF hdet hchar).trans
    ((symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF).toHomeomorph.image
      (specialOrthogonalIdentityKernelNeighborhood F hF hdet hchar))

@[simp]
theorem specialOrthogonalIdentityZeroFiberSkewAdjointHomeomorph_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialOrthogonalIdentityZeroFiber F hF hdet hchar) :
    ((specialOrthogonalIdentityZeroFiberSkewAdjointHomeomorph F hF hdet hchar g :
      (skewAdjointMatricesLieSubalgebra F).toSubmodule) : Matrix ι ι K) =
        (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar g).snd :=
  rfl

/-- The open identity neighborhood in the matrix-valued special-orthogonal
carrier cut out by the implicit-function chart source. -/
def specialOrthogonalIdentityCarrierNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) : Set (specialOrthogonalMatrixSet F) :=
  {g | (g : Matrix ι ι K) ∈
    (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).source}

/-- The local special-orthogonal carrier neighborhood is open. -/
theorem isOpen_specialOrthogonalIdentityCarrierNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    IsOpen (specialOrthogonalIdentityCarrierNeighborhood F hF hdet hchar) := by
  exact (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar).open_source.preimage
    continuous_subtype_val

/-- The matrix identity belongs to the local special-orthogonal carrier
neighborhood. -/
theorem specialOrthogonalMatrixIdentity_mem_identityCarrierNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalMatrixIdentity F ∈
      specialOrthogonalIdentityCarrierNeighborhood F hF hdet hchar :=
  one_mem_symmetricFormPreservingDetOneIdentityChart_source F hF hdet hchar

/-- The zero fiber and the corresponding open neighborhood in the
matrix-valued special-orthogonal carrier are homeomorphic. -/
noncomputable def specialOrthogonalIdentityZeroFiberCarrierHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalIdentityZeroFiber F hF hdet hchar ≃ₜ
      specialOrthogonalIdentityCarrierNeighborhood F hF hdet hchar where
  toFun g := ⟨⟨g, by
    refine ⟨?_,
      det_eq_one_of_mem_symmetricFormPreservingDetOneIdentityChart_source_of_fst_eq_zero
        F hF hdet hchar g g.property.1 g.property.2⟩
    have hg := g.property.2
    rw [symmetricFormPreservingDetOneIdentityChart_fst] at hg
    exact congrArg Subtype.val hg⟩, g.property.1⟩
  invFun g := ⟨g, g.property, by
    rw [symmetricFormPreservingDetOneIdentityChart_fst]
    apply Subtype.ext
    exact g.1.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun g => by
      refine ⟨?_,
        det_eq_one_of_mem_symmetricFormPreservingDetOneIdentityChart_source_of_fst_eq_zero
          F hF hdet hchar g g.property.1 g.property.2⟩
      have hg := g.property.2
      rw [symmetricFormPreservingDetOneIdentityChart_fst] at hg
      exact congrArg Subtype.val hg)) (fun g => g.property.1)
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun g =>
      ⟨g.property, by
        rw [symmetricFormPreservingDetOneIdentityChart_fst]
        apply Subtype.ext
        exact g.1.2.1⟩)

@[simp]
theorem coe_specialOrthogonalIdentityZeroFiberCarrierHomeomorph_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialOrthogonalIdentityZeroFiber F hF hdet hchar) :
    ((specialOrthogonalIdentityZeroFiberCarrierHomeomorph F hF hdet hchar g :
      specialOrthogonalMatrixSet F) : Matrix ι ι K) = g :=
  rfl

/-- The open special-orthogonal carrier neighborhood in skew-adjoint matrix
coordinates. -/
noncomputable def specialOrthogonalIdentityCarrierSkewAdjointHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalIdentityCarrierNeighborhood F hF hdet hchar ≃ₜ
      specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar :=
  (specialOrthogonalIdentityZeroFiberCarrierHomeomorph F hF hdet hchar).symm.trans
    (specialOrthogonalIdentityZeroFiberSkewAdjointHomeomorph F hF hdet hchar)

@[simp]
theorem specialOrthogonalIdentityCarrierSkewAdjointHomeomorph_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialOrthogonalIdentityCarrierNeighborhood F hF hdet hchar) :
    ((specialOrthogonalIdentityCarrierSkewAdjointHomeomorph F hF hdet hchar g :
      (skewAdjointMatricesLieSubalgebra F).toSubmodule) : Matrix ι ι K) =
      (symmetricFormPreservingDetOneIdentityChart F hF hdet hchar
        (g : Matrix ι ι K)).snd :=
  rfl

end Analytic

section RCLikeRegularity

open scoped Matrix.Norms.Operator Topology ContDiff

variable {K : Type*} [RCLike K]

noncomputable local instance : CompleteSpace (Matrix ι ι K) :=
  FiniteDimensional.complete K _

noncomputable local instance :
    CompleteSpace (symmetricMatricesSubmodule (R := K) (ι := ι)) :=
  FiniteDimensional.complete K _

/-- Over a real or complex scalar field, the symmetric-valued form constraint
has maximal global `ContDiff` regularity. -/
theorem contDiff_symmetricFormPreservingConstraint
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    ContDiff K ⊤ (symmetricFormPreservingConstraint F hF) := by
  let hcomp : (symmetricMatricesSubmodule (R := K) (ι := ι)).ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional _
  let p : Matrix ι ι K →L[K]
      symmetricMatricesSubmodule (R := K) (ι := ι) := Classical.choose hcomp
  rw [show symmetricFormPreservingConstraint F hF =
      fun g ↦ p (formPreservingConstraint F g) by
    funext g
    exact (Classical.choose_spec hcomp
      (symmetricFormPreservingConstraint F hF g)).symm]
  apply p.contDiff.comp
  change ContDiff K ⊤ (fun g ↦ transposeContinuousLinearMap g * F * g - F)
  fun_prop

/-- Over a real or complex scalar field, the symmetric-valued form constraint
has maximal `ContDiffAt` regularity at the identity. -/
theorem contDiffAt_symmetricFormPreservingConstraint_one
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    ContDiffAt K ⊤ (symmetricFormPreservingConstraint F hF) 1 :=
  (contDiff_symmetricFormPreservingConstraint F hF).contDiffAt

/-- The real or complex form-preserving identity chart is globally smooth as
a coordinate map. -/
theorem contDiff_symmetricFormPreservingIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ContDiff K ⊤ (symmetricFormPreservingIdentityChart F hF hdet hchar) := by
  let hker := symmetricSkewAdjointOperator_ker_closedComplemented F hF
  change ContDiff K ⊤ (fun g ↦
    (symmetricFormPreservingConstraint F hF g, Classical.choose hker (g - 1)))
  exact (contDiff_symmetricFormPreservingConstraint F hF).prodMk (by fun_prop)

/-- Over a real or complex scalar field, the inverse of the existing
form-preserving identity chart has maximal `ContDiffAt` regularity at its
central coordinate. -/
theorem contDiffAt_symmetricFormPreservingIdentityChart_symm_zero
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ContDiffAt K ⊤ (symmetricFormPreservingIdentityChart F hF hdet hchar).symm
      (0, 0) := by
  let hf := hasStrictFDerivAt_symmetricFormPreservingConstraint_one F hF
  let hf' := symmetricSkewAdjointOperator_range_eq_top F hF hdet hchar
  let hker := symmetricSkewAdjointOperator_ker_closedComplemented F hF
  let φ := hf.implicitFunctionDataOfComplemented
    (symmetricFormPreservingConstraint F hF)
    (symmetricSkewAdjointOperatorContinuousLinearMap F hF) hf' hker
  have hl : ContDiffAt K ⊤ φ.leftFun φ.pt := by
    dsimp [φ, hf, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
    exact contDiffAt_symmetricFormPreservingConstraint_one F hF
  have hr : ContDiffAt K ⊤ φ.rightFun φ.pt := by
    dsimp [φ, hf, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
    fun_prop
  have h := ImplicitFunctionData.contDiffAt_implicitFunction hl hr (by simp)
  have hzero : symmetricFormPreservingConstraint F hF 1 = 0 := by
    apply Subtype.ext
    simp [coe_symmetricFormPreservingConstraint_apply]
  change ContDiffAt K ⊤ φ.toOpenPartialHomeomorph.symm (0, 0)
  convert h using 1
  simp [φ, hzero, HasStrictFDerivAt.implicitFunctionDataOfComplemented]

/-- The real or complex identity-chart inverse is smooth on one open
neighborhood of zero contained in the chart target. The existing
`ContDiffAt K ⊤` theorem has analytic order `ω`, so Mathlib can select a
single neighborhood supporting order `∞`. -/
theorem exists_isOpen_contDiffOn_infty_symmetricFormPreservingIdentityChart_symm_zero
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ u, IsOpen u ∧ (0, 0) ∈ u ∧
      u ⊆ (symmetricFormPreservingIdentityChart F hF hdet hchar).target ∧
      ContDiffOn K ∞
        (symmetricFormPreservingIdentityChart F hF hdet hchar).symm u := by
  have h := contDiffAt_symmetricFormPreservingIdentityChart_symm_zero
    F hF hdet hchar
  obtain ⟨u, hu, hzero, hcont⟩ :=
    h.contDiffOn' (m := (∞ : WithTop ℕ∞)) (by simp) (by simp)
  have hcont' : ContDiffOn K ∞
      (symmetricFormPreservingIdentityChart F hF hdet hchar).symm u := by
    simpa using hcont
  refine ⟨u ∩ (symmetricFormPreservingIdentityChart F hF hdet hchar).target,
    hu.inter (symmetricFormPreservingIdentityChart F hF hdet hchar).open_target,
    ⟨hzero, zero_mem_symmetricFormPreservingIdentityChart_target F hF hdet hchar⟩,
    Set.inter_subset_right, ?_⟩
  exact hcont'.mono Set.inter_subset_left

/-- A selected common smooth target neighborhood for the real or complex
form-preserving identity chart. -/
noncomputable def symmetricFormPreservingIdentityChartSmoothTarget
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Set (symmetricMatricesSubmodule (R := K) (ι := ι) ×
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  Classical.choose
    (exists_isOpen_contDiffOn_infty_symmetricFormPreservingIdentityChart_symm_zero
      F hF hdet hchar)

/-- The selected common smooth target neighborhood is open. -/
theorem isOpen_symmetricFormPreservingIdentityChartSmoothTarget
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    IsOpen (symmetricFormPreservingIdentityChartSmoothTarget
      F hF hdet hchar) :=
  (Classical.choose_spec
    (exists_isOpen_contDiffOn_infty_symmetricFormPreservingIdentityChart_symm_zero
      F hF hdet hchar)).1

/-- The central zero coordinate belongs to the common smooth target. -/
theorem zero_mem_symmetricFormPreservingIdentityChartSmoothTarget
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (0, 0) ∈ symmetricFormPreservingIdentityChartSmoothTarget
      F hF hdet hchar :=
  (Classical.choose_spec
    (exists_isOpen_contDiffOn_infty_symmetricFormPreservingIdentityChart_symm_zero
      F hF hdet hchar)).2.1

/-- The common smooth target lies inside the original identity-chart target. -/
theorem symmetricFormPreservingIdentityChartSmoothTarget_subset
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    symmetricFormPreservingIdentityChartSmoothTarget F hF hdet hchar ⊆
      (symmetricFormPreservingIdentityChart F hF hdet hchar).target :=
  (Classical.choose_spec
    (exists_isOpen_contDiffOn_infty_symmetricFormPreservingIdentityChart_symm_zero
      F hF hdet hchar)).2.2.1

/-- The original inverse chart is smooth on the selected common target. -/
theorem contDiffOn_infty_symmetricFormPreservingIdentityChart_symm_smoothTarget
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ContDiffOn K ∞ (symmetricFormPreservingIdentityChart F hF hdet hchar).symm
      (symmetricFormPreservingIdentityChartSmoothTarget F hF hdet hchar) :=
  (Classical.choose_spec
    (exists_isOpen_contDiffOn_infty_symmetricFormPreservingIdentityChart_symm_zero
      F hF hdet hchar)).2.2.2

/-- The identity chart restricted to a target neighborhood on which both
directions are smooth. -/
noncomputable def symmetricFormPreservingSmoothIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    OpenPartialHomeomorph (Matrix ι ι K)
      (symmetricMatricesSubmodule (R := K) (ι := ι) ×
        (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  ((symmetricFormPreservingIdentityChart F hF hdet hchar).symm.restrOpen
    (symmetricFormPreservingIdentityChartSmoothTarget F hF hdet hchar)
    (isOpen_symmetricFormPreservingIdentityChartSmoothTarget
      F hF hdet hchar)).symm

/-- The smooth restricted chart has exactly the selected common target. -/
@[simp]
theorem symmetricFormPreservingSmoothIdentityChart_target
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (symmetricFormPreservingSmoothIdentityChart F hF hdet hchar).target =
      symmetricFormPreservingIdentityChartSmoothTarget F hF hdet hchar := by
  rw [symmetricFormPreservingSmoothIdentityChart,
    OpenPartialHomeomorph.symm_target, OpenPartialHomeomorph.restrOpen_source]
  exact Set.inter_eq_right.mpr
    (symmetricFormPreservingIdentityChartSmoothTarget_subset F hF hdet hchar)

/-- The selected target of the smooth restricted chart contains zero. -/
theorem zero_mem_symmetricFormPreservingSmoothIdentityChart_target
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (0, 0) ∈
      (symmetricFormPreservingSmoothIdentityChart F hF hdet hchar).target := by
  rw [symmetricFormPreservingSmoothIdentityChart_target]
  exact zero_mem_symmetricFormPreservingIdentityChartSmoothTarget F hF hdet hchar

/-- The matrix identity belongs to the source of the smooth restricted chart. -/
theorem one_mem_symmetricFormPreservingSmoothIdentityChart_source
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (1 : Matrix ι ι K) ∈
      (symmetricFormPreservingSmoothIdentityChart F hF hdet hchar).source := by
  let e := symmetricFormPreservingIdentityChart F hF hdet hchar
  let er := e.symm.restrOpen
    (symmetricFormPreservingIdentityChartSmoothTarget F hF hdet hchar)
    (isOpen_symmetricFormPreservingIdentityChartSmoothTarget F hF hdet hchar)
  have hz : (0, 0) ∈ er.source := by
    change (0, 0) ∈ e.target ∩
      symmetricFormPreservingIdentityChartSmoothTarget F hF hdet hchar
    exact ⟨zero_mem_symmetricFormPreservingIdentityChart_target F hF hdet hchar,
      zero_mem_symmetricFormPreservingIdentityChartSmoothTarget F hF hdet hchar⟩
  have hinv : e.symm (0, 0) = 1 := by
    rw [← symmetricFormPreservingIdentityChart_one F hF hdet hchar]
    exact e.left_inv
      (one_mem_symmetricFormPreservingIdentityChart_source F hF hdet hchar)
  have hm := er.map_source hz
  simpa [symmetricFormPreservingSmoothIdentityChart, er, e, hinv] using hm

/-- The smooth restricted identity chart has smooth forward coordinates. -/
theorem contDiffOn_infty_symmetricFormPreservingSmoothIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ContDiffOn K ∞ (symmetricFormPreservingSmoothIdentityChart F hF hdet hchar)
      (symmetricFormPreservingSmoothIdentityChart F hF hdet hchar).source := by
  simpa [symmetricFormPreservingSmoothIdentityChart] using
    (contDiff_symmetricFormPreservingIdentityChart F hF hdet hchar).contDiffOn.of_le
      (show (∞ : WithTop ℕ∞) ≤ ⊤ by simp)

/-- The inverse smooth restricted identity chart is smooth on its target. -/
theorem contDiffOn_infty_symmetricFormPreservingSmoothIdentityChart_symm
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ContDiffOn K ∞
      (symmetricFormPreservingSmoothIdentityChart F hF hdet hchar).symm
      (symmetricFormPreservingSmoothIdentityChart F hF hdet hchar).target := by
  rw [symmetricFormPreservingSmoothIdentityChart_target]
  simpa [symmetricFormPreservingSmoothIdentityChart] using
    contDiffOn_infty_symmetricFormPreservingIdentityChart_symm_smoothTarget
      F hF hdet hchar

/-- The common smooth identity chart restricted to the determinant identity
neighborhood that selects the positive branch on its zero fiber. -/
noncomputable def symmetricFormPreservingSmoothDetOneIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    OpenPartialHomeomorph (Matrix ι ι K)
      (symmetricMatricesSubmodule (R := K) (ι := ι) ×
        (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  (symmetricFormPreservingSmoothIdentityChart F hF hdet hchar).restrOpen
    determinantOneIdentityNeighborhood isOpen_determinantOneIdentityNeighborhood

/-- The inverse of the original identity chart is exactly the implicit
function supplied by the complemented-kernel implicit function theorem. -/
theorem symmetricFormPreservingIdentityChart_symm_zero_eq_implicitFunctionOfComplemented
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (y : (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :
    (symmetricFormPreservingIdentityChart F hF hdet hchar).symm (0, y) =
      HasStrictFDerivAt.implicitFunctionOfComplemented
        (symmetricFormPreservingConstraint F hF)
        (symmetricSkewAdjointOperatorContinuousLinearMap F hF)
        (hasStrictFDerivAt_symmetricFormPreservingConstraint_one F hF)
        (symmetricSkewAdjointOperator_range_eq_top F hF hdet hchar)
        (symmetricSkewAdjointOperator_ker_closedComplemented F hF)
        0 y :=
  rfl

/-- Restricting the identity chart to its selected smooth target and
determinant-one source does not change its inverse function. -/
theorem symmetricFormPreservingSmoothDetOneIdentityChart_symm_zero_eq_implicitFunctionOfComplemented
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (y : (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :
    (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar).symm (0, y) =
      HasStrictFDerivAt.implicitFunctionOfComplemented
        (symmetricFormPreservingConstraint F hF)
        (symmetricSkewAdjointOperatorContinuousLinearMap F hF)
        (hasStrictFDerivAt_symmetricFormPreservingConstraint_one F hF)
        (symmetricSkewAdjointOperator_range_eq_top F hF hdet hchar)
        (symmetricSkewAdjointOperator_ker_closedComplemented F hF)
        0 y := by
  rw [show
    (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar).symm (0, y) =
        (symmetricFormPreservingIdentityChart
          F hF hdet hchar).symm (0, y) by
      simp only [symmetricFormPreservingSmoothDetOneIdentityChart,
        OpenPartialHomeomorph.coe_restrOpen_symm,
        symmetricFormPreservingSmoothIdentityChart,
        OpenPartialHomeomorph.symm_symm,
        OpenPartialHomeomorph.coe_restrOpen]]
  exact symmetricFormPreservingIdentityChart_symm_zero_eq_implicitFunctionOfComplemented
    F hF hdet hchar y

/-- At the central zero coordinate, the inverse smooth determinant-one chart
has derivative the canonical inclusion of the skew-adjoint kernel. -/
theorem hasFDerivAt_symmetricFormPreservingSmoothDetOneIdentityChart_symm_zero
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    HasFDerivAt
      (fun y : (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker =>
        (symmetricFormPreservingSmoothDetOneIdentityChart
          F hF hdet hchar).symm (0, y))
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker.subtypeL 0 := by
  rw [show
    (fun y : (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker =>
      (symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar).symm (0, y)) =
      fun y =>
        HasStrictFDerivAt.implicitFunctionOfComplemented
          (symmetricFormPreservingConstraint F hF)
          (symmetricSkewAdjointOperatorContinuousLinearMap F hF)
          (hasStrictFDerivAt_symmetricFormPreservingConstraint_one F hF)
          (symmetricSkewAdjointOperator_range_eq_top F hF hdet hchar)
          (symmetricSkewAdjointOperator_ker_closedComplemented F hF)
          0 y by
    funext y
    exact
      symmetricFormPreservingSmoothDetOneIdentityChart_symm_zero_eq_implicitFunctionOfComplemented
        F hF hdet hchar y]
  have hzero : symmetricFormPreservingConstraint F hF 1 = 0 := by
    apply Subtype.ext
    simp [coe_symmetricFormPreservingConstraint_apply]
  have h :=
    ((hasStrictFDerivAt_symmetricFormPreservingConstraint_one F hF)
      |>.to_implicitFunctionOfComplemented
        (symmetricSkewAdjointOperator_range_eq_top F hF hdet hchar)
        (symmetricSkewAdjointOperator_ker_closedComplemented F hF)).hasFDerivAt
  rwa [hzero] at h

/-- In the canonical skew-adjoint coordinates, the inverse identity chart has
derivative the ambient matrix inclusion at zero. -/
theorem hasFDerivAt_specialOrthogonalSmoothIdentityInverseCoordinate_zero
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    HasFDerivAt
      (fun y : (skewAdjointMatricesLieSubalgebra F).toSubmodule =>
        (symmetricFormPreservingSmoothDetOneIdentityChart
          F hF hdet hchar).symm
            (0, (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
              F hF).symm y))
      (skewAdjointMatricesLieSubalgebra F).toSubmodule.subtypeL 0 := by
  let e := symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
  have hchart :=
    hasFDerivAt_symmetricFormPreservingSmoothDetOneIdentityChart_symm_zero
      F hF hdet hchar
  have hcomp := hchart.comp 0 e.symm.hasFDerivAt
  convert hcomp using 1

set_option backward.isDefEq.respectTransparency false in
/-- Along a skew-adjoint line through the identity, the forward chart
coordinate is exactly the supplied tangent vector. -/
theorem specialOrthogonalSmoothIdentityForwardCoordinate_one_add
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (X : (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
    symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
        (symmetricFormPreservingSmoothDetOneIdentityChart
          F hF hdet hchar (1 + (X : Matrix ι ι K))).snd = X := by
  let e := symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
  let hf := hasStrictFDerivAt_symmetricFormPreservingConstraint_one F hF
  let hf' := symmetricSkewAdjointOperator_range_eq_top F hF hdet hchar
  let hker := symmetricSkewAdjointOperator_ker_closedComplemented F hF
  have hchart :
      symmetricFormPreservingSmoothDetOneIdentityChart
          F hF hdet hchar (1 + (X : Matrix ι ι K)) =
        symmetricFormPreservingIdentityChart
          F hF hdet hchar (1 + (X : Matrix ι ι K)) := by
    simp only [symmetricFormPreservingSmoothDetOneIdentityChart,
      OpenPartialHomeomorph.coe_restrOpen,
      symmetricFormPreservingSmoothIdentityChart,
      OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.coe_restrOpen_symm]
  have hcoe : ((e.symm X :
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :
        Matrix ι ι K) = X := by
    have h :=
      coe_symmetricSkewAdjointOperatorKerContinuousLinearEquiv_apply
        F hF (e.symm X)
    simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using h.symm
  have hpoint :
      (1 + (X : Matrix ι ι K)) =
        (e.symm X :
          (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) + 1 := by
    rw [show ((e.symm X :
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :
        Matrix ι ι K) = X from hcoe]
    exact add_comm _ _
  have himp :=
    HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply_ker
      hf hf' hker (e.symm X)
  rw [hchart, hpoint, show
    symmetricFormPreservingIdentityChart F hF hdet hchar =
      hf.implicitToOpenPartialHomeomorphOfComplemented
        (symmetricFormPreservingConstraint F hF)
        (symmetricSkewAdjointOperatorContinuousLinearMap F hF) hf' hker from rfl,
    himp]
  exact e.apply_symm_apply X

/-- The constant derivative of the ambient forward skew-adjoint coordinate:
project to the complemented kernel, then identify that kernel with the
skew-adjoint tangent carrier. -/
noncomputable def specialOrthogonalSmoothIdentityForwardCoordinateDerivative
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    Matrix ι ι K →L[K]
      (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
  (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
    F hF).toContinuousLinearMap.comp
      (Classical.choose
        (symmetricSkewAdjointOperator_ker_closedComplemented F hF))

set_option backward.isDefEq.respectTransparency false in
/-- The ambient forward skew-adjoint coordinate has its explicit constant
derivative at every matrix. -/
theorem hasFDerivAt_specialOrthogonalSmoothIdentityForwardCoordinate
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (q : Matrix ι ι K) :
    HasFDerivAt
      (fun q : Matrix ι ι K =>
        symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
          (symmetricFormPreservingSmoothDetOneIdentityChart
            F hF hdet hchar q).snd)
      (specialOrthogonalSmoothIdentityForwardCoordinateDerivative F hF) q := by
  let e := symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
  let p := Classical.choose
    (symmetricSkewAdjointOperator_ker_closedComplemented F hF)
  rw [show
    (fun q : Matrix ι ι K =>
      symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
        (symmetricFormPreservingSmoothDetOneIdentityChart
          F hF hdet hchar q).snd) =
      fun q => e (p (q - 1)) by
    funext q
    simp only [symmetricFormPreservingSmoothDetOneIdentityChart,
      OpenPartialHomeomorph.coe_restrOpen,
      symmetricFormPreservingSmoothIdentityChart,
      OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.coe_restrOpen_symm,
      symmetricFormPreservingIdentityChart,
      HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply,
      e, p]]
  exact e.hasFDerivAt.comp q
    (p.hasFDerivAt.comp q ((hasFDerivAt_id q).sub_const 1))

/-- The forward-coordinate derivative is inverse to the inclusion of the
skew-adjoint tangent carrier into the ambient matrix space. -/
theorem specialOrthogonalSmoothIdentityForwardCoordinateDerivative_comp_subtypeL
    (F : Matrix ι ι K) (hF : F.IsSymm) :
    (specialOrthogonalSmoothIdentityForwardCoordinateDerivative F hF).comp
        (skewAdjointMatricesLieSubalgebra F).toSubmodule.subtypeL =
      ContinuousLinearMap.id K
        ((skewAdjointMatricesLieSubalgebra F).toSubmodule) := by
  let e := symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
  let hker := symmetricSkewAdjointOperator_ker_closedComplemented F hF
  let p := Classical.choose hker
  apply ContinuousLinearMap.ext
  intro X
  change e (p (X : Matrix ι ι K)) = X
  have hcoe : ((e.symm X :
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :
        Matrix ι ι K) = X := by
    have h :=
      coe_symmetricSkewAdjointOperatorKerContinuousLinearEquiv_apply
        F hF (e.symm X)
    simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using h.symm
  rw [← hcoe, show
    p ((e.symm X :
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :
        Matrix ι ι K) = e.symm X from Classical.choose_spec hker (e.symm X)]
  exact e.apply_symm_apply X

@[simp]
theorem symmetricFormPreservingSmoothDetOneIdentityChart_source
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (symmetricFormPreservingSmoothDetOneIdentityChart F hF hdet hchar).source =
      (symmetricFormPreservingSmoothIdentityChart F hF hdet hchar).source ∩
        determinantOneIdentityNeighborhood :=
  rfl

/-- The smooth determinant-component chart source contains the matrix
identity. -/
theorem one_mem_symmetricFormPreservingSmoothDetOneIdentityChart_source
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (1 : Matrix ι ι K) ∈
      (symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar).source := by
  rw [symmetricFormPreservingSmoothDetOneIdentityChart_source]
  exact ⟨one_mem_symmetricFormPreservingSmoothIdentityChart_source
      F hF hdet hchar,
    one_mem_determinantOneIdentityNeighborhood hchar⟩

@[simp]
theorem symmetricFormPreservingSmoothDetOneIdentityChart_one
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    symmetricFormPreservingSmoothDetOneIdentityChart F hF hdet hchar 1 =
      (0, 0) := by
  simp [symmetricFormPreservingSmoothDetOneIdentityChart,
    symmetricFormPreservingSmoothIdentityChart]

/-- The smooth determinant-component chart target contains zero. -/
theorem zero_mem_symmetricFormPreservingSmoothDetOneIdentityChart_target
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (0, 0) ∈ (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar).target := by
  have h := (symmetricFormPreservingSmoothDetOneIdentityChart
    F hF hdet hchar).map_source
      (one_mem_symmetricFormPreservingSmoothDetOneIdentityChart_source
        F hF hdet hchar)
  simpa using h

/-- The inverse smooth determinant-one chart sends its central zero
coordinate back to the matrix identity. -/
@[simp]
theorem symmetricFormPreservingSmoothDetOneIdentityChart_symm_zero
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar).symm (0, 0) = 1 := by
  rw [← symmetricFormPreservingSmoothDetOneIdentityChart_one
    F hF hdet hchar]
  exact (symmetricFormPreservingSmoothDetOneIdentityChart
    F hF hdet hchar).left_inv
      (one_mem_symmetricFormPreservingSmoothDetOneIdentityChart_source
        F hF hdet hchar)

/-- The determinant-component chart remains smooth on its source. -/
theorem contDiffOn_infty_symmetricFormPreservingSmoothDetOneIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ContDiffOn K ∞ (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar)
      (symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar).source := by
  exact (contDiffOn_infty_symmetricFormPreservingSmoothIdentityChart
    F hF hdet hchar).mono (fun _ hx ↦ hx.1)

/-- The inverse determinant-component chart remains smooth on its target. -/
theorem contDiffOn_infty_symmetricFormPreservingSmoothDetOneIdentityChart_symm
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ContDiffOn K ∞ (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar).symm
      (symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar).target := by
  apply (contDiffOn_infty_symmetricFormPreservingSmoothIdentityChart_symm
    F hF hdet hchar).mono
  intro y hy
  change y ∈ ((symmetricFormPreservingSmoothIdentityChart
    F hF hdet hchar).toPartialEquiv.restr
      determinantOneIdentityNeighborhood).target at hy
  rw [PartialEquiv.restr_target] at hy
  exact hy.1

@[simp]
theorem symmetricFormPreservingSmoothDetOneIdentityChart_fst
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : Matrix ι ι K) :
    (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar g).fst = symmetricFormPreservingConstraint F hF g := by
  simp [symmetricFormPreservingSmoothDetOneIdentityChart,
    symmetricFormPreservingSmoothIdentityChart]

/-- The zero-constraint fiber in the common smooth determinant-component
chart. -/
def specialOrthogonalSmoothIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) : Set (Matrix ι ι K) :=
  {g | g ∈ (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar).source ∧
    (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar g).fst = 0}

/-- Kernel coordinates whose zero-constraint pair lies in the common smooth
determinant-component chart target. -/
def specialOrthogonalSmoothIdentityKernelNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Set (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker :=
  {y | (0, y) ∈ (symmetricFormPreservingSmoothDetOneIdentityChart
    F hF hdet hchar).target}

/-- The common smooth kernel-coordinate neighborhood is open. -/
theorem isOpen_specialOrthogonalSmoothIdentityKernelNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    IsOpen (specialOrthogonalSmoothIdentityKernelNeighborhood
      F hF hdet hchar) := by
  exact (symmetricFormPreservingSmoothDetOneIdentityChart
    F hF hdet hchar).open_target.preimage
      (continuous_const.prodMk continuous_id)

/-- Zero belongs to the common smooth kernel-coordinate neighborhood. -/
theorem zero_mem_specialOrthogonalSmoothIdentityKernelNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (0 : (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) ∈
      specialOrthogonalSmoothIdentityKernelNeighborhood F hF hdet hchar :=
  zero_mem_symmetricFormPreservingSmoothDetOneIdentityChart_target
    F hF hdet hchar

/-- The matrix identity belongs to the common smooth zero fiber. -/
theorem one_mem_specialOrthogonalSmoothIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (1 : Matrix ι ι K) ∈
      specialOrthogonalSmoothIdentityZeroFiber F hF hdet hchar :=
  ⟨one_mem_symmetricFormPreservingSmoothDetOneIdentityChart_source
      F hF hdet hchar,
    by simp⟩

/-- Every matrix in the common smooth zero fiber has determinant one. -/
theorem det_eq_one_of_mem_specialOrthogonalSmoothIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : Matrix ι ι K)
    (hg : g ∈ specialOrthogonalSmoothIdentityZeroFiber F hF hdet hchar) :
    g.det = 1 := by
  apply det_eq_one_of_mem_determinantOneIdentityNeighborhood F g hdet
  · exact (symmetricFormPreservingSmoothDetOneIdentityChart_source
      F hF hdet hchar ▸ hg.1).2
  · have hz := hg.2
    rw [symmetricFormPreservingSmoothDetOneIdentityChart_fst] at hz
    exact congrArg Subtype.val hz

private def specialOrthogonalSmoothIdentityProductZeroSlice
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Set (symmetricMatricesSubmodule (R := K) (ι := ι) ×
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  {p | p ∈ (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar).target ∧ p.1 = 0}

private theorem image_specialOrthogonalSmoothIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    symmetricFormPreservingSmoothDetOneIdentityChart F hF hdet hchar ''
        specialOrthogonalSmoothIdentityZeroFiber F hF hdet hchar =
      specialOrthogonalSmoothIdentityProductZeroSlice F hF hdet hchar := by
  let e := symmetricFormPreservingSmoothDetOneIdentityChart F hF hdet hchar
  ext p
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨e.mapsTo hg.1, hg.2⟩
  · rintro hp
    refine ⟨e.symm p, ?_, e.right_inv hp.1⟩
    exact ⟨e.map_target hp.1, by rw [e.right_inv hp.1]; exact hp.2⟩

private noncomputable def specialOrthogonalSmoothIdentityProductZeroSliceHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalSmoothIdentityProductZeroSlice F hF hdet hchar ≃ₜ
      specialOrthogonalSmoothIdentityKernelNeighborhood F hF hdet hchar where
  toFun p := ⟨p.1.2, by
    rw [specialOrthogonalSmoothIdentityKernelNeighborhood, ← p.2.2]
    exact p.2.1⟩
  invFun y := ⟨(0, y.1), y.2, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact p.2.2.symm
    · rfl
  right_inv y := rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_snd.comp continuous_subtype_val) (fun p => by
      rw [specialOrthogonalSmoothIdentityKernelNeighborhood, ← p.2.2]
      exact p.2.1)
  continuous_invFun := Continuous.subtype_mk
    (continuous_const.prodMk continuous_subtype_val) (fun y => ⟨y.2, rfl⟩)

/-- The common smooth special-orthogonal zero fiber is homeomorphic to its
open derivative-kernel coordinate neighborhood. -/
noncomputable def specialOrthogonalSmoothIdentityZeroFiberHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalSmoothIdentityZeroFiber F hF hdet hchar ≃ₜ
      specialOrthogonalSmoothIdentityKernelNeighborhood F hF hdet hchar :=
  ((symmetricFormPreservingSmoothDetOneIdentityChart F hF hdet hchar)
    |>.homeomorphOfImageSubsetSource (fun _ hg ↦ hg.1)
      (image_specialOrthogonalSmoothIdentityZeroFiber F hF hdet hchar)).trans
    (specialOrthogonalSmoothIdentityProductZeroSliceHomeomorph
      F hF hdet hchar)

/-- The common smooth skew-adjoint coordinate neighborhood at the identity. -/
def specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Set ((skewAdjointMatricesLieSubalgebra F).toSubmodule) :=
  symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF ''
    specialOrthogonalSmoothIdentityKernelNeighborhood F hF hdet hchar

/-- The common smooth skew-adjoint coordinate neighborhood is open. -/
theorem isOpen_specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    IsOpen (specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      F hF hdet hchar) := by
  exact (symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF).toHomeomorph
    |>.isOpen_image.mpr
      (isOpen_specialOrthogonalSmoothIdentityKernelNeighborhood
        F hF hdet hchar)

/-- Zero belongs to the common smooth skew-adjoint neighborhood. -/
theorem zero_mem_specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (0 : (skewAdjointMatricesLieSubalgebra F).toSubmodule) ∈
      specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar := by
  refine ⟨0,
    zero_mem_specialOrthogonalSmoothIdentityKernelNeighborhood
      F hF hdet hchar, ?_⟩
  exact map_zero (symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF)

/-- The common smooth special-orthogonal zero fiber in skew-adjoint
coordinates. -/
noncomputable def specialOrthogonalSmoothIdentityZeroFiberSkewAdjointHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalSmoothIdentityZeroFiber F hF hdet hchar ≃ₜ
      specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar :=
  (specialOrthogonalSmoothIdentityZeroFiberHomeomorph
    F hF hdet hchar).trans
    ((symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF).toHomeomorph.image
      (specialOrthogonalSmoothIdentityKernelNeighborhood F hF hdet hchar))

@[simp]
theorem specialOrthogonalSmoothIdentityZeroFiberSkewAdjointHomeomorph_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialOrthogonalSmoothIdentityZeroFiber F hF hdet hchar) :
    (specialOrthogonalSmoothIdentityZeroFiberSkewAdjointHomeomorph
      F hF hdet hchar g :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) =
      symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
        (symmetricFormPreservingSmoothDetOneIdentityChart
          F hF hdet hchar g).snd :=
  rfl

@[simp]
theorem coe_specialOrthogonalSmoothIdentityZeroFiberSkewAdjointHomeomorph_symm_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (y : specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      F hF hdet hchar) :
    ((specialOrthogonalSmoothIdentityZeroFiberSkewAdjointHomeomorph
      F hF hdet hchar).symm y : Matrix ι ι K) =
        (symmetricFormPreservingSmoothDetOneIdentityChart
          F hF hdet hchar).symm
            (0, (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
              F hF).symm y) :=
  rfl

/-- The ambient forward-coordinate formula of the common smooth zero-fiber
chart is smooth on that fiber. -/
theorem contDiffOn_infty_specialOrthogonalSmoothIdentityZeroFiberCoordinate
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ContDiffOn K ∞ (fun g ↦
      symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
        (symmetricFormPreservingSmoothDetOneIdentityChart
          F hF hdet hchar g).snd)
      (specialOrthogonalSmoothIdentityZeroFiber F hF hdet hchar) := by
  apply (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
    F hF).contDiff.comp_contDiffOn
  apply contDiff_snd.comp_contDiffOn
  exact (contDiffOn_infty_symmetricFormPreservingSmoothDetOneIdentityChart
    F hF hdet hchar).mono (fun _ hg ↦ hg.1)

/-- The ambient inverse-coordinate formula of the common smooth zero-fiber
chart is smooth on the skew-adjoint neighborhood. -/
theorem contDiffOn_infty_specialOrthogonalSmoothIdentityZeroFiberCoordinate_symm
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ContDiffOn K ∞ (fun y ↦
      (symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar).symm
          (0, (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
            F hF).symm y))
      (specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar) := by
  apply (contDiffOn_infty_symmetricFormPreservingSmoothDetOneIdentityChart_symm
    F hF hdet hchar).comp
  · exact (contDiff_const.prodMk
      (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
        F hF).symm.contDiff).contDiffOn
  · rintro y ⟨x, hx, rfl⟩
    simpa using hx

/-- The open identity neighborhood in the matrix-valued special-orthogonal
carrier cut out by the common smooth zero-fiber chart source. -/
def specialOrthogonalSmoothIdentityCarrierNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Set (specialOrthogonalMatrixSet F) :=
  {g | (g : Matrix ι ι K) ∈
    (symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar).source}

/-- The common smooth special-orthogonal carrier neighborhood is open. -/
theorem isOpen_specialOrthogonalSmoothIdentityCarrierNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    IsOpen (specialOrthogonalSmoothIdentityCarrierNeighborhood
      F hF hdet hchar) := by
  exact (symmetricFormPreservingSmoothDetOneIdentityChart
    F hF hdet hchar).open_source.preimage continuous_subtype_val

/-- The matrix identity belongs to the common smooth carrier neighborhood. -/
theorem specialOrthogonalMatrixIdentity_mem_smoothIdentityCarrierNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalMatrixIdentity F ∈
      specialOrthogonalSmoothIdentityCarrierNeighborhood F hF hdet hchar :=
  one_mem_symmetricFormPreservingSmoothDetOneIdentityChart_source
    F hF hdet hchar

/-- The common smooth zero fiber and its corresponding open neighborhood in
the matrix-valued special-orthogonal carrier are homeomorphic. -/
noncomputable def specialOrthogonalSmoothIdentityZeroFiberCarrierHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalSmoothIdentityZeroFiber F hF hdet hchar ≃ₜ
      specialOrthogonalSmoothIdentityCarrierNeighborhood
        F hF hdet hchar where
  toFun g := ⟨⟨g, by
    refine ⟨?_,
      det_eq_one_of_mem_specialOrthogonalSmoothIdentityZeroFiber
        F hF hdet hchar g g.property⟩
    have hg := g.property.2
    rw [symmetricFormPreservingSmoothDetOneIdentityChart_fst] at hg
    exact congrArg Subtype.val hg⟩, g.property.1⟩
  invFun g := ⟨g, g.property, by
    rw [symmetricFormPreservingSmoothDetOneIdentityChart_fst]
    apply Subtype.ext
    exact g.1.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun g => by
      refine ⟨?_,
        det_eq_one_of_mem_specialOrthogonalSmoothIdentityZeroFiber
          F hF hdet hchar g g.property⟩
      have hg := g.property.2
      rw [symmetricFormPreservingSmoothDetOneIdentityChart_fst] at hg
      exact congrArg Subtype.val hg)) (fun g => g.property.1)
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun g =>
      ⟨g.property, by
        rw [symmetricFormPreservingSmoothDetOneIdentityChart_fst]
        apply Subtype.ext
        exact g.1.2.1⟩)

@[simp]
theorem coe_specialOrthogonalSmoothIdentityZeroFiberCarrierHomeomorph_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialOrthogonalSmoothIdentityZeroFiber F hF hdet hchar) :
    ((specialOrthogonalSmoothIdentityZeroFiberCarrierHomeomorph
      F hF hdet hchar g : specialOrthogonalMatrixSet F) :
        Matrix ι ι K) = g :=
  rfl

@[simp]
theorem coe_specialOrthogonalSmoothIdentityZeroFiberCarrierHomeomorph_symm_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialOrthogonalSmoothIdentityCarrierNeighborhood F hF hdet hchar) :
    ((specialOrthogonalSmoothIdentityZeroFiberCarrierHomeomorph
      F hF hdet hchar).symm g : Matrix ι ι K) = g :=
  rfl

/-- The common smooth matrix-valued special-orthogonal carrier neighborhood
in skew-adjoint coordinates. -/
noncomputable def specialOrthogonalSmoothIdentityCarrierSkewAdjointHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialOrthogonalSmoothIdentityCarrierNeighborhood F hF hdet hchar ≃ₜ
      specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar :=
  (specialOrthogonalSmoothIdentityZeroFiberCarrierHomeomorph
    F hF hdet hchar).symm.trans
      (specialOrthogonalSmoothIdentityZeroFiberSkewAdjointHomeomorph
        F hF hdet hchar)

@[simp]
theorem specialOrthogonalSmoothIdentityCarrierSkewAdjointHomeomorph_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialOrthogonalSmoothIdentityCarrierNeighborhood F hF hdet hchar) :
    (specialOrthogonalSmoothIdentityCarrierSkewAdjointHomeomorph
      F hF hdet hchar g :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) =
      symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
        (symmetricFormPreservingSmoothDetOneIdentityChart
          F hF hdet hchar (g : Matrix ι ι K)).snd :=
  rfl

@[simp]
theorem coe_specialOrthogonalSmoothIdentityCarrierSkewAdjointHomeomorph_symm_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (y : specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      F hF hdet hchar) :
    (((specialOrthogonalSmoothIdentityCarrierSkewAdjointHomeomorph
      F hF hdet hchar).symm y : specialOrthogonalMatrixSet F) :
        Matrix ι ι K) =
      (symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar).symm
          (0, (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
            F hF).symm y) :=
  rfl

/-- For each finite differentiability order, the real or complex identity
chart inverse is `ContDiffOn` on an open neighborhood of zero contained in the
chart target. -/
theorem exists_isOpen_contDiffOn_symmetricFormPreservingIdentityChart_symm_zero
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    ∃ u, IsOpen u ∧ (0, 0) ∈ u ∧
      u ⊆ (symmetricFormPreservingIdentityChart F hF hdet hchar).target ∧
      ContDiffOn K n
        (symmetricFormPreservingIdentityChart F hF hdet hchar).symm u := by
  have h := contDiffAt_symmetricFormPreservingIdentityChart_symm_zero
    F hF hdet hchar
  obtain ⟨u, hu, hzero, hcont⟩ :=
    h.contDiffOn' (m := (n : WithTop ℕ∞)) (by simp) (by simp)
  have hcont' : ContDiffOn K n
      (symmetricFormPreservingIdentityChart F hF hdet hchar).symm u := by
    simpa using hcont
  refine ⟨u ∩ (symmetricFormPreservingIdentityChart F hF hdet hchar).target,
    hu.inter (symmetricFormPreservingIdentityChart F hF hdet hchar).open_target,
    ⟨hzero, zero_mem_symmetricFormPreservingIdentityChart_target F hF hdet hchar⟩,
    Set.inter_subset_right, ?_⟩
  exact hcont'.mono Set.inter_subset_left

/-- A selected finite-order smooth target neighborhood for the real or
complex form-preserving identity chart. -/
noncomputable def symmetricFormPreservingIdentityChartContDiffTarget
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    Set (symmetricMatricesSubmodule (R := K) (ι := ι) ×
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  Classical.choose
    (exists_isOpen_contDiffOn_symmetricFormPreservingIdentityChart_symm_zero
      F hF hdet hchar n)

/-- The selected finite-order smooth target neighborhood is open. -/
theorem isOpen_symmetricFormPreservingIdentityChartContDiffTarget
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    IsOpen (symmetricFormPreservingIdentityChartContDiffTarget
      F hF hdet hchar n) :=
  (Classical.choose_spec
    (exists_isOpen_contDiffOn_symmetricFormPreservingIdentityChart_symm_zero
      F hF hdet hchar n)).1

/-- The central zero coordinate belongs to the selected target neighborhood. -/
theorem zero_mem_symmetricFormPreservingIdentityChartContDiffTarget
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    (0, 0) ∈ symmetricFormPreservingIdentityChartContDiffTarget
      F hF hdet hchar n :=
  (Classical.choose_spec
    (exists_isOpen_contDiffOn_symmetricFormPreservingIdentityChart_symm_zero
      F hF hdet hchar n)).2.1

/-- The selected neighborhood lies inside the original identity-chart target. -/
theorem symmetricFormPreservingIdentityChartContDiffTarget_subset
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    symmetricFormPreservingIdentityChartContDiffTarget F hF hdet hchar n ⊆
      (symmetricFormPreservingIdentityChart F hF hdet hchar).target :=
  (Classical.choose_spec
    (exists_isOpen_contDiffOn_symmetricFormPreservingIdentityChart_symm_zero
      F hF hdet hchar n)).2.2.1

/-- The original inverse chart is smooth to the supplied finite order on the
selected target neighborhood. -/
theorem contDiffOn_symmetricFormPreservingIdentityChart_symm_contDiffTarget
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    ContDiffOn K n (symmetricFormPreservingIdentityChart F hF hdet hchar).symm
      (symmetricFormPreservingIdentityChartContDiffTarget
        F hF hdet hchar n) :=
  (Classical.choose_spec
    (exists_isOpen_contDiffOn_symmetricFormPreservingIdentityChart_symm_zero
      F hF hdet hchar n)).2.2.2

/-- The identity chart restricted to a target neighborhood on which its
inverse is smooth to the supplied finite order. -/
noncomputable def symmetricFormPreservingContDiffIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    OpenPartialHomeomorph (Matrix ι ι K)
      (symmetricMatricesSubmodule (R := K) (ι := ι) ×
        (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  ((symmetricFormPreservingIdentityChart F hF hdet hchar).symm.restrOpen
    (symmetricFormPreservingIdentityChartContDiffTarget F hF hdet hchar n)
    (isOpen_symmetricFormPreservingIdentityChartContDiffTarget
      F hF hdet hchar n)).symm

/-- The restricted chart has exactly the selected smooth target. -/
@[simp]
theorem symmetricFormPreservingContDiffIdentityChart_target
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    (symmetricFormPreservingContDiffIdentityChart F hF hdet hchar n).target =
      symmetricFormPreservingIdentityChartContDiffTarget F hF hdet hchar n := by
  rw [symmetricFormPreservingContDiffIdentityChart,
    OpenPartialHomeomorph.symm_target, OpenPartialHomeomorph.restrOpen_source]
  exact Set.inter_eq_right.mpr
    (symmetricFormPreservingIdentityChartContDiffTarget_subset
      F hF hdet hchar n)

/-- The selected target of the restricted chart contains zero. -/
theorem zero_mem_symmetricFormPreservingContDiffIdentityChart_target
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    (0, 0) ∈
      (symmetricFormPreservingContDiffIdentityChart F hF hdet hchar n).target := by
  rw [symmetricFormPreservingContDiffIdentityChart_target]
  exact zero_mem_symmetricFormPreservingIdentityChartContDiffTarget
    F hF hdet hchar n

/-- The matrix identity belongs to the source of the restricted chart. -/
theorem one_mem_symmetricFormPreservingContDiffIdentityChart_source
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    (1 : Matrix ι ι K) ∈
      (symmetricFormPreservingContDiffIdentityChart F hF hdet hchar n).source := by
  let e := symmetricFormPreservingIdentityChart F hF hdet hchar
  let er := e.symm.restrOpen
    (symmetricFormPreservingIdentityChartContDiffTarget F hF hdet hchar n)
    (isOpen_symmetricFormPreservingIdentityChartContDiffTarget
      F hF hdet hchar n)
  have hz : (0, 0) ∈ er.source := by
    change (0, 0) ∈ e.target ∩
      symmetricFormPreservingIdentityChartContDiffTarget F hF hdet hchar n
    exact ⟨zero_mem_symmetricFormPreservingIdentityChart_target F hF hdet hchar,
      zero_mem_symmetricFormPreservingIdentityChartContDiffTarget
        F hF hdet hchar n⟩
  have hinv : e.symm (0, 0) = 1 := by
    rw [← symmetricFormPreservingIdentityChart_one F hF hdet hchar]
    exact e.left_inv
      (one_mem_symmetricFormPreservingIdentityChart_source F hF hdet hchar)
  have hm := er.map_source hz
  simpa [symmetricFormPreservingContDiffIdentityChart, er, e, hinv] using hm

/-- The restricted chart is smooth to the supplied finite order on its source. -/
theorem contDiffOn_symmetricFormPreservingContDiffIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    ContDiffOn K n (symmetricFormPreservingContDiffIdentityChart
      F hF hdet hchar n)
      (symmetricFormPreservingContDiffIdentityChart
        F hF hdet hchar n).source := by
  simpa [symmetricFormPreservingContDiffIdentityChart] using
    (contDiff_symmetricFormPreservingIdentityChart F hF hdet hchar).contDiffOn.of_le
      (show (n : WithTop ℕ∞) ≤ ⊤ by simp)

/-- The inverse restricted chart is smooth to the supplied finite order on
its target. -/
theorem contDiffOn_symmetricFormPreservingContDiffIdentityChart_symm
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    ContDiffOn K n (symmetricFormPreservingContDiffIdentityChart
      F hF hdet hchar n).symm
      (symmetricFormPreservingContDiffIdentityChart
        F hF hdet hchar n).target := by
  rw [symmetricFormPreservingContDiffIdentityChart_target]
  simpa [symmetricFormPreservingContDiffIdentityChart] using
    contDiffOn_symmetricFormPreservingIdentityChart_symm_contDiffTarget
      F hF hdet hchar n

/-- The finite-order smooth identity chart restricted to the determinant
identity neighborhood that selects the positive branch on its zero fiber. -/
noncomputable def symmetricFormPreservingContDiffDetOneIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    OpenPartialHomeomorph (Matrix ι ι K)
      (symmetricMatricesSubmodule (R := K) (ι := ι) ×
        (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  (symmetricFormPreservingContDiffIdentityChart F hF hdet hchar n).restrOpen
    determinantOneIdentityNeighborhood isOpen_determinantOneIdentityNeighborhood

@[simp]
theorem symmetricFormPreservingContDiffDetOneIdentityChart_source
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    (symmetricFormPreservingContDiffDetOneIdentityChart F hF hdet hchar n).source =
      (symmetricFormPreservingContDiffIdentityChart F hF hdet hchar n).source ∩
        determinantOneIdentityNeighborhood :=
  rfl

/-- The finite-order determinant-component chart source contains the matrix
identity. -/
theorem one_mem_symmetricFormPreservingContDiffDetOneIdentityChart_source
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    (1 : Matrix ι ι K) ∈
      (symmetricFormPreservingContDiffDetOneIdentityChart
        F hF hdet hchar n).source := by
  rw [symmetricFormPreservingContDiffDetOneIdentityChart_source]
  exact ⟨one_mem_symmetricFormPreservingContDiffIdentityChart_source
      F hF hdet hchar n,
    one_mem_determinantOneIdentityNeighborhood hchar⟩

@[simp]
theorem symmetricFormPreservingContDiffDetOneIdentityChart_one
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    symmetricFormPreservingContDiffDetOneIdentityChart F hF hdet hchar n 1 =
      (0, 0) := by
  simp [symmetricFormPreservingContDiffDetOneIdentityChart,
    symmetricFormPreservingContDiffIdentityChart]

/-- The finite-order determinant-component chart target contains zero. -/
theorem zero_mem_symmetricFormPreservingContDiffDetOneIdentityChart_target
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    (0, 0) ∈ (symmetricFormPreservingContDiffDetOneIdentityChart
      F hF hdet hchar n).target := by
  have h := (symmetricFormPreservingContDiffDetOneIdentityChart
    F hF hdet hchar n).map_source
      (one_mem_symmetricFormPreservingContDiffDetOneIdentityChart_source
        F hF hdet hchar n)
  simpa using h

/-- The determinant-component chart remains smooth to the selected finite
order on its source. -/
theorem contDiffOn_symmetricFormPreservingContDiffDetOneIdentityChart
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    ContDiffOn K n (symmetricFormPreservingContDiffDetOneIdentityChart
      F hF hdet hchar n)
      (symmetricFormPreservingContDiffDetOneIdentityChart
        F hF hdet hchar n).source := by
  exact (contDiffOn_symmetricFormPreservingContDiffIdentityChart
    F hF hdet hchar n).mono (fun _ hx ↦ hx.1)

/-- The inverse determinant-component chart remains smooth to the selected
finite order on its target. -/
theorem contDiffOn_symmetricFormPreservingContDiffDetOneIdentityChart_symm
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    ContDiffOn K n (symmetricFormPreservingContDiffDetOneIdentityChart
      F hF hdet hchar n).symm
      (symmetricFormPreservingContDiffDetOneIdentityChart
        F hF hdet hchar n).target := by
  apply (contDiffOn_symmetricFormPreservingContDiffIdentityChart_symm
    F hF hdet hchar n).mono
  intro y hy
  change y ∈ ((symmetricFormPreservingContDiffIdentityChart
    F hF hdet hchar n).toPartialEquiv.restr
      determinantOneIdentityNeighborhood).target at hy
  rw [PartialEquiv.restr_target] at hy
  exact hy.1

@[simp]
theorem symmetricFormPreservingContDiffDetOneIdentityChart_fst
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) (g : Matrix ι ι K) :
    (symmetricFormPreservingContDiffDetOneIdentityChart
      F hF hdet hchar n g).fst = symmetricFormPreservingConstraint F hF g := by
  simp [symmetricFormPreservingContDiffDetOneIdentityChart,
    symmetricFormPreservingContDiffIdentityChart]

/-- The zero-constraint fiber in the finite-order smooth determinant-component
chart. -/
def specialOrthogonalContDiffIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) : Set (Matrix ι ι K) :=
  {g | g ∈ (symmetricFormPreservingContDiffDetOneIdentityChart
      F hF hdet hchar n).source ∧
    (symmetricFormPreservingContDiffDetOneIdentityChart
      F hF hdet hchar n g).fst = 0}

/-- Kernel coordinates whose zero-constraint pair lies in the finite-order
smooth determinant-component chart target. -/
def specialOrthogonalContDiffIdentityKernelNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    Set (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker :=
  {y | (0, y) ∈ (symmetricFormPreservingContDiffDetOneIdentityChart
    F hF hdet hchar n).target}

/-- The finite-order smooth kernel-coordinate neighborhood is open. -/
theorem isOpen_specialOrthogonalContDiffIdentityKernelNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    IsOpen (specialOrthogonalContDiffIdentityKernelNeighborhood
      F hF hdet hchar n) := by
  exact (symmetricFormPreservingContDiffDetOneIdentityChart
    F hF hdet hchar n).open_target.preimage
      (continuous_const.prodMk continuous_id)

/-- Zero belongs to the finite-order smooth kernel-coordinate neighborhood. -/
theorem zero_mem_specialOrthogonalContDiffIdentityKernelNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    (0 : (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) ∈
      specialOrthogonalContDiffIdentityKernelNeighborhood
        F hF hdet hchar n :=
  zero_mem_symmetricFormPreservingContDiffDetOneIdentityChart_target
    F hF hdet hchar n

/-- The matrix identity belongs to the finite-order smooth zero fiber. -/
theorem one_mem_specialOrthogonalContDiffIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    (1 : Matrix ι ι K) ∈
      specialOrthogonalContDiffIdentityZeroFiber F hF hdet hchar n :=
  ⟨one_mem_symmetricFormPreservingContDiffDetOneIdentityChart_source
      F hF hdet hchar n,
    by simp⟩

/-- Every matrix in the finite-order smooth zero fiber has determinant one. -/
theorem det_eq_one_of_mem_specialOrthogonalContDiffIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) (g : Matrix ι ι K)
    (hg : g ∈ specialOrthogonalContDiffIdentityZeroFiber
      F hF hdet hchar n) :
    g.det = 1 := by
  apply det_eq_one_of_mem_determinantOneIdentityNeighborhood F g hdet
  · exact (symmetricFormPreservingContDiffDetOneIdentityChart_source
      F hF hdet hchar n ▸ hg.1).2
  · have hz := hg.2
    rw [symmetricFormPreservingContDiffDetOneIdentityChart_fst] at hz
    exact congrArg Subtype.val hz

private def specialOrthogonalContDiffIdentityProductZeroSlice
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    Set (symmetricMatricesSubmodule (R := K) (ι := ι) ×
      (symmetricSkewAdjointOperatorContinuousLinearMap F hF).ker) :=
  {p | p ∈ (symmetricFormPreservingContDiffDetOneIdentityChart
      F hF hdet hchar n).target ∧ p.1 = 0}

private theorem image_specialOrthogonalContDiffIdentityZeroFiber
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    symmetricFormPreservingContDiffDetOneIdentityChart F hF hdet hchar n ''
        specialOrthogonalContDiffIdentityZeroFiber F hF hdet hchar n =
      specialOrthogonalContDiffIdentityProductZeroSlice
        F hF hdet hchar n := by
  let e := symmetricFormPreservingContDiffDetOneIdentityChart
    F hF hdet hchar n
  ext p
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨e.mapsTo hg.1, hg.2⟩
  · rintro hp
    refine ⟨e.symm p, ?_, e.right_inv hp.1⟩
    exact ⟨e.map_target hp.1, by rw [e.right_inv hp.1]; exact hp.2⟩

private noncomputable def specialOrthogonalContDiffIdentityProductZeroSliceHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    specialOrthogonalContDiffIdentityProductZeroSlice F hF hdet hchar n ≃ₜ
      specialOrthogonalContDiffIdentityKernelNeighborhood
        F hF hdet hchar n where
  toFun p := ⟨p.1.2, by
    rw [specialOrthogonalContDiffIdentityKernelNeighborhood, ← p.2.2]
    exact p.2.1⟩
  invFun y := ⟨(0, y.1), y.2, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact p.2.2.symm
    · rfl
  right_inv y := rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_snd.comp continuous_subtype_val) (fun p => by
      rw [specialOrthogonalContDiffIdentityKernelNeighborhood, ← p.2.2]
      exact p.2.1)
  continuous_invFun := Continuous.subtype_mk
    (continuous_const.prodMk continuous_subtype_val) (fun y => ⟨y.2, rfl⟩)

/-- The finite-order smooth special-orthogonal zero fiber is homeomorphic to
its open derivative-kernel coordinate neighborhood. -/
noncomputable def specialOrthogonalContDiffIdentityZeroFiberHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    specialOrthogonalContDiffIdentityZeroFiber F hF hdet hchar n ≃ₜ
      specialOrthogonalContDiffIdentityKernelNeighborhood
        F hF hdet hchar n :=
  ((symmetricFormPreservingContDiffDetOneIdentityChart F hF hdet hchar n)
    |>.homeomorphOfImageSubsetSource (fun _ hg ↦ hg.1)
      (image_specialOrthogonalContDiffIdentityZeroFiber
        F hF hdet hchar n)).trans
    (specialOrthogonalContDiffIdentityProductZeroSliceHomeomorph
      F hF hdet hchar n)

/-- The finite-order smooth skew-adjoint coordinate neighborhood at the
identity. -/
def specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    Set ((skewAdjointMatricesLieSubalgebra F).toSubmodule) :=
  symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF ''
    specialOrthogonalContDiffIdentityKernelNeighborhood
      F hF hdet hchar n

/-- The finite-order smooth skew-adjoint coordinate neighborhood is open. -/
theorem isOpen_specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    IsOpen (specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
      F hF hdet hchar n) := by
  exact (symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF).toHomeomorph
    |>.isOpen_image.mpr
      (isOpen_specialOrthogonalContDiffIdentityKernelNeighborhood
        F hF hdet hchar n)

/-- Zero belongs to the finite-order smooth skew-adjoint neighborhood. -/
theorem zero_mem_specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    (0 : (skewAdjointMatricesLieSubalgebra F).toSubmodule) ∈
      specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar n := by
  refine ⟨0,
    zero_mem_specialOrthogonalContDiffIdentityKernelNeighborhood
      F hF hdet hchar n, ?_⟩
  exact map_zero (symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF)

/-- The finite-order smooth special-orthogonal zero fiber in skew-adjoint
coordinates. -/
noncomputable def specialOrthogonalContDiffIdentityZeroFiberSkewAdjointHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    specialOrthogonalContDiffIdentityZeroFiber F hF hdet hchar n ≃ₜ
      specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar n :=
  (specialOrthogonalContDiffIdentityZeroFiberHomeomorph
    F hF hdet hchar n).trans
    ((symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF).toHomeomorph.image
      (specialOrthogonalContDiffIdentityKernelNeighborhood
        F hF hdet hchar n))

@[simp]
theorem specialOrthogonalContDiffIdentityZeroFiberSkewAdjointHomeomorph_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ)
    (g : specialOrthogonalContDiffIdentityZeroFiber F hF hdet hchar n) :
    (specialOrthogonalContDiffIdentityZeroFiberSkewAdjointHomeomorph
      F hF hdet hchar n g :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) =
      symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
        (symmetricFormPreservingContDiffDetOneIdentityChart
          F hF hdet hchar n g).snd :=
  rfl

@[simp]
theorem coe_specialOrthogonalContDiffIdentityZeroFiberSkewAdjointHomeomorph_symm_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ)
    (y : specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
      F hF hdet hchar n) :
    ((specialOrthogonalContDiffIdentityZeroFiberSkewAdjointHomeomorph
      F hF hdet hchar n).symm y : Matrix ι ι K) =
        (symmetricFormPreservingContDiffDetOneIdentityChart
          F hF hdet hchar n).symm
            (0, (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
              F hF).symm y) :=
  rfl

/-- The ambient forward-coordinate formula of the finite-order smooth
zero-fiber chart is `C^n` on that fiber. -/
theorem contDiffOn_specialOrthogonalContDiffIdentityZeroFiberCoordinate
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    ContDiffOn K n (fun g ↦
      symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
        (symmetricFormPreservingContDiffDetOneIdentityChart
          F hF hdet hchar n g).snd)
      (specialOrthogonalContDiffIdentityZeroFiber F hF hdet hchar n) := by
  apply (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
    F hF).contDiff.comp_contDiffOn
  apply contDiff_snd.comp_contDiffOn
  exact (contDiffOn_symmetricFormPreservingContDiffDetOneIdentityChart
    F hF hdet hchar n).mono (fun _ hg ↦ hg.1)

/-- The ambient inverse-coordinate formula of the finite-order smooth
zero-fiber chart is `C^n` on the skew-adjoint neighborhood. -/
theorem contDiffOn_specialOrthogonalContDiffIdentityZeroFiberCoordinate_symm
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    ContDiffOn K n (fun y ↦
      (symmetricFormPreservingContDiffDetOneIdentityChart
        F hF hdet hchar n).symm
          (0, (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
            F hF).symm y))
      (specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar n) := by
  apply (contDiffOn_symmetricFormPreservingContDiffDetOneIdentityChart_symm
    F hF hdet hchar n).comp
  · exact (contDiff_const.prodMk
      (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
        F hF).symm.contDiff).contDiffOn
  · rintro y ⟨x, hx, rfl⟩
    simpa using hx

/-- The open identity neighborhood in the matrix-valued special-orthogonal
carrier cut out by the finite-order smooth zero-fiber chart source. -/
def specialOrthogonalContDiffIdentityCarrierNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    Set (specialOrthogonalMatrixSet F) :=
  {g | (g : Matrix ι ι K) ∈
    (symmetricFormPreservingContDiffDetOneIdentityChart
      F hF hdet hchar n).source}

/-- The finite-order smooth special-orthogonal carrier neighborhood is open. -/
theorem isOpen_specialOrthogonalContDiffIdentityCarrierNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    IsOpen (specialOrthogonalContDiffIdentityCarrierNeighborhood
      F hF hdet hchar n) := by
  exact (symmetricFormPreservingContDiffDetOneIdentityChart
    F hF hdet hchar n).open_source.preimage continuous_subtype_val

/-- The matrix identity belongs to the finite-order smooth carrier
neighborhood. -/
theorem specialOrthogonalMatrixIdentity_mem_contDiffIdentityCarrierNeighborhood
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    specialOrthogonalMatrixIdentity F ∈
      specialOrthogonalContDiffIdentityCarrierNeighborhood
        F hF hdet hchar n :=
  one_mem_symmetricFormPreservingContDiffDetOneIdentityChart_source
    F hF hdet hchar n

/-- The finite-order smooth zero fiber and its corresponding open neighborhood
in the matrix-valued special-orthogonal carrier are homeomorphic. -/
noncomputable def specialOrthogonalContDiffIdentityZeroFiberCarrierHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    specialOrthogonalContDiffIdentityZeroFiber F hF hdet hchar n ≃ₜ
      specialOrthogonalContDiffIdentityCarrierNeighborhood
        F hF hdet hchar n where
  toFun g := ⟨⟨g, by
    refine ⟨?_,
      det_eq_one_of_mem_specialOrthogonalContDiffIdentityZeroFiber
        F hF hdet hchar n g g.property⟩
    have hg := g.property.2
    rw [symmetricFormPreservingContDiffDetOneIdentityChart_fst] at hg
    exact congrArg Subtype.val hg⟩, g.property.1⟩
  invFun g := ⟨g, g.property, by
    rw [symmetricFormPreservingContDiffDetOneIdentityChart_fst]
    apply Subtype.ext
    exact g.1.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun g => by
      refine ⟨?_,
        det_eq_one_of_mem_specialOrthogonalContDiffIdentityZeroFiber
          F hF hdet hchar n g g.property⟩
      have hg := g.property.2
      rw [symmetricFormPreservingContDiffDetOneIdentityChart_fst] at hg
      exact congrArg Subtype.val hg)) (fun g => g.property.1)
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun g =>
      ⟨g.property, by
        rw [symmetricFormPreservingContDiffDetOneIdentityChart_fst]
        apply Subtype.ext
        exact g.1.2.1⟩)

@[simp]
theorem coe_specialOrthogonalContDiffIdentityZeroFiberCarrierHomeomorph_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ)
    (g : specialOrthogonalContDiffIdentityZeroFiber F hF hdet hchar n) :
    ((specialOrthogonalContDiffIdentityZeroFiberCarrierHomeomorph
      F hF hdet hchar n g : specialOrthogonalMatrixSet F) :
        Matrix ι ι K) = g :=
  rfl

@[simp]
theorem coe_specialOrthogonalContDiffIdentityZeroFiberCarrierHomeomorph_symm_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ)
    (g : specialOrthogonalContDiffIdentityCarrierNeighborhood
      F hF hdet hchar n) :
    ((specialOrthogonalContDiffIdentityZeroFiberCarrierHomeomorph
      F hF hdet hchar n).symm g : Matrix ι ι K) = g :=
  rfl

/-- The finite-order smooth matrix-valued special-orthogonal carrier
neighborhood in skew-adjoint coordinates. -/
noncomputable def specialOrthogonalContDiffIdentityCarrierSkewAdjointHomeomorph
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ) :
    specialOrthogonalContDiffIdentityCarrierNeighborhood F hF hdet hchar n ≃ₜ
      specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar n :=
  (specialOrthogonalContDiffIdentityZeroFiberCarrierHomeomorph
    F hF hdet hchar n).symm.trans
      (specialOrthogonalContDiffIdentityZeroFiberSkewAdjointHomeomorph
        F hF hdet hchar n)

@[simp]
theorem specialOrthogonalContDiffIdentityCarrierSkewAdjointHomeomorph_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ)
    (g : specialOrthogonalContDiffIdentityCarrierNeighborhood
      F hF hdet hchar n) :
    (specialOrthogonalContDiffIdentityCarrierSkewAdjointHomeomorph
      F hF hdet hchar n g :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) =
      symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
        (symmetricFormPreservingContDiffDetOneIdentityChart
          F hF hdet hchar n (g : Matrix ι ι K)).snd :=
  rfl

@[simp]
theorem coe_specialOrthogonalContDiffIdentityCarrierSkewAdjointHomeomorph_symm_apply
    (F : Matrix ι ι K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (n : ℕ)
    (y : specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
      F hF hdet hchar n) :
    (((specialOrthogonalContDiffIdentityCarrierSkewAdjointHomeomorph
      F hF hdet hchar n).symm y : specialOrthogonalMatrixSet F) :
        Matrix ι ι K) =
      (symmetricFormPreservingContDiffDetOneIdentityChart
        F hF hdet hchar n).symm
          (0, (symmetricSkewAdjointOperatorKerContinuousLinearEquiv
            F hF).symm y) :=
  rfl

end RCLikeRegularity

end Matrix
