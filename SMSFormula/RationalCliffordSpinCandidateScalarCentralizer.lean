import SMSFormula.RationalCliffordSpinCandidateKernelFiber
import SMSFormula.ExteriorAlgebraJointContractionKernel
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Scalar centralizers over arbitrary rational algebras

This file proves the algebraic input needed to identify the unit fiber of the
affine Clifford--Spin candidate with `mu_2`.  A finite rational linear map
records the grade-involution equation and every coordinate of commutation
with the standard Clifford vectors.  Its rational kernel consists exactly of
scalars.  Flat base change along an arbitrary commutative rational algebra
then shows that the common even vector centralizer remains scalar after base
change.

The proof is independent of the closure-generated field-point definition of
`spinGroup` and makes no statement about fppf surjectivity.
-/

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Coordinates for the rational linear equations defining the even vector
centralizer: involution coordinates, followed by commutator coordinates. -/
abbrev cliffordScalarConstraintIndex (n : ℕ) :=
  Finset (Fin n) ⊕ (Fin n × Finset (Fin n))

/-- The finite rational linear system whose kernel is the even centralizer of
the standard Clifford-vector range. -/
def cliffordScalarConstraintLinearMap :
    CliffordAlgebra V.quadraticForm →ₗ[ℚ]
      (cliffordScalarConstraintIndex n → ℚ) where
  toFun x z :=
    match z with
    | Sum.inl u => V.cliffordCoordinateBasis.repr
        (CliffordAlgebra.involute x - x) u
    | Sum.inr (i, u) => V.cliffordCoordinateBasis.repr
        (CliffordAlgebra.ι V.quadraticForm (Pi.single i 1) * x -
          x * CliffordAlgebra.ι V.quadraticForm (Pi.single i 1)) u
  map_add' x y := by
    ext z
    rcases z with u | ⟨i, u⟩
    · simp
      ring
    · simp [mul_add, add_mul]
      ring
  map_smul' q x := by
    ext z
    rcases z with u | ⟨i, u⟩
    · simp
      ring
    · simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      ring

/-- Vanishing of the rational constraint system forces a Clifford element to
be scalar. -/
theorem exists_eq_algebraMap_of_cliffordScalarConstraint_eq_zero
    (x : CliffordAlgebra V.quadraticForm)
    (hx : V.cliffordScalarConstraintLinearMap x = 0) :
    ∃ r : ℚ, x = algebraMap ℚ (CliffordAlgebra V.quadraticForm) r := by
  have hinvolute : CliffordAlgebra.involute x = x := by
    apply sub_eq_zero.mp
    apply V.cliffordCoordinateBasis.repr.injective
    rw [map_zero]
    ext u
    have hu := congrFun hx (Sum.inl u)
    exact hu
  have hcomm_basis (i : Fin n) :
      CliffordAlgebra.ι V.quadraticForm (Pi.single i 1) * x =
        x * CliffordAlgebra.ι V.quadraticForm (Pi.single i 1) := by
    apply sub_eq_zero.mp
    apply V.cliffordCoordinateBasis.repr.injective
    rw [map_zero]
    ext u
    have hu := congrFun hx (Sum.inr (i, u))
    exact hu
  have hcomm (m : Fin n → ℚ) :
      CliffordAlgebra.ι V.quadraticForm m * x =
        x * CliffordAlgebra.ι V.quadraticForm m := by
    rw [← (Pi.basisFun ℚ (Fin n)).sum_repr m, map_sum]
    simp_rw [map_smul, Finset.sum_mul, Finset.mul_sum,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa using congrArg
      (fun z => (Pi.basisFun ℚ (Fin n)).repr m i • z) (hcomm_basis i)
  have hcontract (d : Module.Dual ℚ (Fin n → ℚ)) :
      CliffordAlgebra.contractLeft d x = 0 := by
    let v : Fin n → ℚ :=
      (LinearMap.BilinForm.toDual V.quadraticForm.associated
        V.quadraticForm_associated_nondegenerate).symm d
    have hv : V.quadraticForm.associated v = d := by
      apply LinearMap.ext
      intro w
      exact LinearMap.BilinForm.apply_toDual_symm_apply d w
    rw [← hv]
    have hgraded :=
      CliffordAlgebra.ι_mul_sub_involute_mul_ι_eq_two_smul_contractLeft
        V.quadraticForm v x
    rw [hinvolute, hcomm v, sub_self] at hgraded
    exact (smul_eq_zero.mp hgraded.symm).resolve_left two_ne_zero
  have hcontractExterior (d : Module.Dual ℚ (Fin n → ℚ)) :
      CliffordAlgebra.contractLeft d
          (CliffordAlgebra.equivExterior V.quadraticForm x) = 0 := by
    rw [← CliffordAlgebra.equivExterior_contractLeft, hcontract d, map_zero]
  obtain ⟨r, hr⟩ :=
    ExteriorAlgebra.exists_eq_algebraMap_of_contractLeft_eq_zero
      (Pi.basisFun ℚ (Fin n))
      (CliffordAlgebra.equivExterior V.quadraticForm x) hcontractExterior
  refine ⟨r, ?_⟩
  apply (CliffordAlgebra.equivExterior V.quadraticForm).injective
  rw [hr]
  simp

section BaseChange

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The coordinate form, over a rational algebra, of the base-changed even
vector-centralizer equations. -/
def cliffordScalarConstraintBaseChangeEvaluation
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    cliffordScalarConstraintIndex n → A
  | Sum.inl u => (V.cliffordCoordinateBaseChangeBasis A).repr
      (V.cliffordCoordinateBaseChangeInvolute A x - x) u
  | Sum.inr (i, u) => (V.cliffordCoordinateBaseChangeBasis A).repr
      (V.cliffordCoordinateBaseChangeVector A i * x -
        x * V.cliffordCoordinateBaseChangeVector A i) u

/-- The abstract linear base change of the rational constraint map is
literally the finite coordinate system obtained from the base-changed
Clifford operations. -/
theorem piScalarRight_cliffordScalarConstraint_baseChange
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    TensorProduct.piScalarRight ℚ A A (cliffordScalarConstraintIndex n)
        ((V.cliffordScalarConstraintLinearMap).baseChange A x) =
      V.cliffordScalarConstraintBaseChangeEvaluation A x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      ext z
      rcases z with u | ⟨i, u⟩ <;>
        simp [cliffordScalarConstraintBaseChangeEvaluation]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      ext z
      rcases z with u | ⟨i, u⟩
      · simp [cliffordScalarConstraintBaseChangeEvaluation]
        ring
      · simp [cliffordScalarConstraintBaseChangeEvaluation, mul_add, add_mul]
        ring
  | tmul a x =>
      ext z
      rcases z with u | ⟨i, u⟩
      · simp [cliffordScalarConstraintBaseChangeEvaluation,
          cliffordCoordinateBaseChangeInvolute,
          cliffordCoordinateBaseChangeBasis,
          Module.Basis.baseChange_repr_tmul,
          cliffordScalarConstraintLinearMap, sub_smul]
      · simp [cliffordScalarConstraintBaseChangeEvaluation,
          cliffordCoordinateBaseChangeVector,
          cliffordCoordinateBaseChangeOfRational,
          cliffordCoordinateBaseChangeBasis,
          Module.Basis.baseChange_repr_tmul,
          Algebra.TensorProduct.tmul_mul_tmul,
          cliffordScalarConstraintLinearMap, sub_smul]

/-- Over every commutative rational algebra, an involution-fixed element of
the base-changed Clifford algebra which commutes with all standard vectors is
a scalar. -/
theorem exists_eq_algebraMap_of_baseChangeInvolute_eq_of_commute_vectors
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (hinvolute : V.cliffordCoordinateBaseChangeInvolute A x = x)
    (hcomm : ∀ i, V.cliffordCoordinateBaseChangeVector A i * x =
      x * V.cliffordCoordinateBaseChangeVector A i) :
    ∃ r : A, x = algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) r := by
  let f := V.cliffordScalarConstraintLinearMap
  have hevaluation :
      V.cliffordScalarConstraintBaseChangeEvaluation A x = 0 := by
    funext z
    rcases z with u | ⟨i, u⟩
    · simp [cliffordScalarConstraintBaseChangeEvaluation, hinvolute]
    · simp [cliffordScalarConstraintBaseChangeEvaluation, hcomm i]
  have hbaseChange : f.baseChange A x = 0 := by
    apply (TensorProduct.piScalarRight ℚ A A
      (cliffordScalarConstraintIndex n)).injective
    rw [V.piScalarRight_cliffordScalarConstraint_baseChange A,
      hevaluation, map_zero]
  let xker : LinearMap.ker (f.baseChange A) := ⟨x, hbaseChange⟩
  let y : A ⊗[ℚ] LinearMap.ker f :=
    (LinearMap.tensorKerEquiv A A f).symm xker
  have hy : LinearMap.lTensor A (LinearMap.ker f).subtype y = x := by
    have h := LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm A A f xker
    exact h
  have hyScalar : ∃ r : A,
      LinearMap.lTensor A (LinearMap.ker f).subtype y =
        algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) r := by
    induction y using TensorProduct.induction_on with
    | zero =>
        exact ⟨0, by simp⟩
    | add y z hy hz =>
        obtain ⟨r, hr⟩ := hy
        obtain ⟨s, hs⟩ := hz
        refine ⟨r + s, ?_⟩
        rw [map_add, hr, hs]
        exact (TensorProduct.add_tmul r s
          (1 : CliffordAlgebra V.quadraticForm)).symm
    | tmul a z =>
        obtain ⟨q, hq⟩ :=
          V.exists_eq_algebraMap_of_cliffordScalarConstraint_eq_zero
            z.1 z.2
        refine ⟨a * algebraMap ℚ A q, ?_⟩
        rw [LinearMap.lTensor_tmul]
        change a ⊗ₜ[ℚ] (z : CliffordAlgebra V.quadraticForm) =
          algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
            (a * algebraMap ℚ A q)
        rw [hq]
        calc
          a ⊗ₜ[ℚ] algebraMap ℚ (CliffordAlgebra V.quadraticForm) q =
              a ⊗ₜ[ℚ] (q • (1 : CliffordAlgebra V.quadraticForm)) := by
                rw [Algebra.smul_def, mul_one]
          _ = (q • a) ⊗ₜ[ℚ]
              (1 : CliffordAlgebra V.quadraticForm) :=
                TensorProduct.tmul_smul _ _ _
          _ = (a * algebraMap ℚ A q) ⊗ₜ[ℚ]
              (1 : CliffordAlgebra V.quadraticForm) := by
                rw [Algebra.smul_def, mul_comm]
          _ = algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
              (a * algebraMap ℚ A q) := by
                rw [Algebra.TensorProduct.algebraMap_apply]
                simp
  obtain ⟨r, hr⟩ := hyScalar
  exact ⟨r, hy.symm.trans hr⟩

/-- Scalar inclusion into the finite Clifford base change is injective over
every commutative rational algebra. -/
theorem cliffordCoordinateBaseChange_algebraMap_injective :
    Function.Injective
      (algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)) := by
  exact Algebra.TensorProduct.includeLeft_injective
    (R := ℚ) (S := A) (A := A)
    (B := CliffordAlgebra V.quadraticForm)
    (algebraMap ℚ (CliffordAlgebra V.quadraticForm)).injective

@[simp]
theorem cliffordCoordinateBaseChangeReverse_algebraMap (r : A) :
    V.cliffordCoordinateBaseChangeReverse A
        (algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) r) =
      algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) r := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp

@[simp]
theorem cliffordCoordinateBaseChangeInvolute_algebraMap (r : A) :
    V.cliffordCoordinateBaseChangeInvolute A
        (algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) r) =
      algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) r := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp

/-- A candidate point whose extracted matrix is one has scalar Clifford
coordinate, and that scalar is a square root of one. -/
theorem CliffordSpinCandidatePointData.exists_rootOfUnity_eq_clifford_of_matrix_eq_one
    (d : V.CliffordSpinCandidatePointData A)
    (hmatrix : d.matrixPoint.1 = 1) :
    ∃ z : rootsOfUnity 2 A,
      d.clifford = algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
        ((z : Aˣ) : A) := by
  have hcomm (i : Fin n) :
      V.cliffordCoordinateBaseChangeVector A i * d.clifford =
        d.clifford * V.cliffordCoordinateBaseChangeVector A i := by
    have hgraph :
        d.clifford * V.cliffordCoordinateBaseChangeVector A i *
            V.cliffordCoordinateBaseChangeReverse A d.clifford =
          V.cliffordCoordinateBaseChangeVector A i := by
      rw [d.vectorGraph, hmatrix]
      simp [Matrix.one_apply]
    have hreverse_mul :
        V.cliffordCoordinateBaseChangeReverse A d.clifford * d.clifford = 1 :=
      V.cliffordCoordinateBaseChange_reverse_mul_eq_one_of_mul_reverse_eq_one
        A d.clifford d.mul_reverse_eq_one
    calc
      V.cliffordCoordinateBaseChangeVector A i * d.clifford =
          (d.clifford * V.cliffordCoordinateBaseChangeVector A i *
            V.cliffordCoordinateBaseChangeReverse A d.clifford) *
              d.clifford := by rw [hgraph]
      _ = d.clifford * V.cliffordCoordinateBaseChangeVector A i *
            (V.cliffordCoordinateBaseChangeReverse A d.clifford *
              d.clifford) := by simp only [mul_assoc]
      _ = d.clifford * V.cliffordCoordinateBaseChangeVector A i := by
        rw [hreverse_mul, mul_one]
  obtain ⟨r, hr⟩ :=
    V.exists_eq_algebraMap_of_baseChangeInvolute_eq_of_commute_vectors A
      d.clifford d.involute_eq hcomm
  have hreverse :
      V.cliffordCoordinateBaseChangeReverse A d.clifford = d.clifford := by
    rw [hr, V.cliffordCoordinateBaseChangeReverse_algebraMap]
  have hnorm : d.clifford * d.clifford = 1 := by
    calc
      d.clifford * d.clifford = d.clifford *
          V.cliffordCoordinateBaseChangeReverse A d.clifford := by
            rw [hreverse]
      _ = 1 := d.mul_reverse_eq_one
  have hr_sq : r * r = 1 := by
    apply V.cliffordCoordinateBaseChange_algebraMap_injective A
    rw [map_mul, map_one, ← hr]
    exact hnorm
  let u : Aˣ :=
    { val := r
      inv := r
      val_inv := hr_sq
      inv_val := hr_sq }
  have hu : u ^ 2 = 1 := by
    apply Units.ext
    simpa [pow_two, u] using hr_sq
  exact ⟨⟨u, hu⟩, hr⟩

/-- A square root of one gives the scalar candidate point above the identity
special-orthogonal matrix. -/
def cliffordSpinCandidatePointDataOfRootOfUnity
    (z : rootsOfUnity 2 A) : V.CliffordSpinCandidatePointData A where
  clifford := algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
    ((z : Aˣ) : A)
  matrixPoint := V.cliffordSpinCandidateMatrixPointOne A
  involute_eq := V.cliffordCoordinateBaseChangeInvolute_algebraMap A _
  mul_reverse_eq_one := by
    rw [V.cliffordCoordinateBaseChangeReverse_algebraMap, ← map_mul]
    have hz : ((z : Aˣ) : A) * (z : Aˣ) = 1 := by
      simpa [pow_two] using congrArg Units.val z.property
    rw [hz, map_one]
  vectorGraph := by
    intro i
    have hz : ((z : Aˣ) : A) * (z : Aˣ) = 1 := by
      simpa [pow_two] using congrArg Units.val z.property
    calc
      algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) ((z : Aˣ) : A) *
            V.cliffordCoordinateBaseChangeVector A i *
          V.cliffordCoordinateBaseChangeReverse A
            (algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
              ((z : Aˣ) : A)) =
          algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) ((z : Aˣ) : A) *
            V.cliffordCoordinateBaseChangeVector A i *
              algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
                ((z : Aˣ) : A) := by
                  rw [V.cliffordCoordinateBaseChangeReverse_algebraMap]
      _ = algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
              (((z : Aˣ) : A) * (z : Aˣ)) *
            V.cliffordCoordinateBaseChangeVector A i := by
              rw [mul_assoc, ← (Algebra.commutes ((z : Aˣ) : A)
                (V.cliffordCoordinateBaseChangeVector A i)),
                ← mul_assoc, ← map_mul]
      _ = V.cliffordCoordinateBaseChangeVector A i := by
            rw [hz, map_one, one_mul]
      _ = ∑ j, (V.cliffordSpinCandidateMatrixPointOne A).1 j i •
            V.cliffordCoordinateBaseChangeVector A j := by
              simp [Matrix.one_apply]

/-- The extracted special-orthogonal matrix of a scalar root point is one. -/
@[simp]
theorem cliffordSpinCandidatePointDataOfRootOfUnity_matrixGroup
    (z : rootsOfUnity 2 A) :
    (V.cliffordSpinCandidatePointDataOfRootOfUnity A z).matrixGroup = 1 := by
  exact (V.specialOrthogonalMatrixPointEquivGroup A).apply_symm_apply 1

/-- Scalar roots of unity form a multiplicative family of candidate points. -/
def rootsOfUnityToCliffordSpinCandidatePointDataHom :
    rootsOfUnity 2 A →* V.CliffordSpinCandidatePointData A where
  toFun := V.cliffordSpinCandidatePointDataOfRootOfUnity A
  map_one' := by
    apply CliffordSpinCandidatePointData.ext
    · change (1 : A) ⊗ₜ[ℚ]
          (1 : CliffordAlgebra V.quadraticForm) = 1
      rfl
    · apply (V.specialOrthogonalMatrixPointEquivGroup A).injective
      change
        (V.cliffordSpinCandidatePointDataOfRootOfUnity A 1).matrixGroup =
          (1 : V.CliffordSpinCandidatePointData A).matrixGroup
      simp
  map_mul' z w := by
    apply CliffordSpinCandidatePointData.ext
    · simp [cliffordSpinCandidatePointDataOfRootOfUnity]
    · apply (V.specialOrthogonalMatrixPointEquivGroup A).injective
      change
        (V.cliffordSpinCandidatePointDataOfRootOfUnity A (z * w)).matrixGroup =
          ((V.cliffordSpinCandidatePointDataOfRootOfUnity A z) *
            V.cliffordSpinCandidatePointDataOfRootOfUnity A w).matrixGroup
      simp

/-- The matrix component as a group homomorphism on candidate point data. -/
def cliffordSpinCandidatePointDataMatrixHom :
    V.CliffordSpinCandidatePointData A →*
      V.specialOrthogonalMatrixGroup A where
  toFun := fun d => d.matrixGroup
  map_one' := CliffordSpinCandidatePointData.one_matrixGroup V A
  map_mul' := CliffordSpinCandidatePointData.mul_matrixGroup V A

/-- Scalar roots map into the pointwise kernel of the candidate action. -/
def rootsOfUnityToCliffordSpinCandidatePointDataKernelHom :
    rootsOfUnity 2 A →*
      (V.cliffordSpinCandidatePointDataMatrixHom A).ker :=
  (V.rootsOfUnityToCliffordSpinCandidatePointDataHom A).codRestrict
    (V.cliffordSpinCandidatePointDataMatrixHom A).ker
    (fun z => V.cliffordSpinCandidatePointDataOfRootOfUnity_matrixGroup A z)

/-- The arbitrary-algebra pointwise kernel of the affine Clifford--Spin
candidate is exactly `mu_2(A)`. -/
def rootsOfUnityMulEquivCliffordSpinCandidatePointDataKernel :
    rootsOfUnity 2 A ≃*
      (V.cliffordSpinCandidatePointDataMatrixHom A).ker :=
  MulEquiv.ofBijective
    (V.rootsOfUnityToCliffordSpinCandidatePointDataKernelHom A)
    ⟨by
      intro z w hzw
      have hcliff := congrArg
        (fun d : (V.cliffordSpinCandidatePointDataMatrixHom A).ker =>
          d.1.clifford) hzw
      change algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
          ((z : Aˣ) : A) =
        algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
          ((w : Aˣ) : A) at hcliff
      have hscalar : ((z : Aˣ) : A) = (w : Aˣ) :=
        V.cliffordCoordinateBaseChange_algebraMap_injective A hcliff
      apply Subtype.ext
      apply Units.ext
      exact hscalar,
    by
      intro d
      have hdgroup : d.1.matrixGroup = 1 := d.2
      have hmatrix : d.1.matrixPoint.1 = 1 := by
        rw [← d.1.matrixGroup_coe, hdgroup]
        rfl
      obtain ⟨z, hz⟩ :=
        CliffordSpinCandidatePointData.exists_rootOfUnity_eq_clifford_of_matrix_eq_one
          (V := V) (A := A) d.1 hmatrix
      refine ⟨z, ?_⟩
      apply Subtype.ext
      apply CliffordSpinCandidatePointData.ext
      · exact hz.symm
      · apply Subtype.ext
        rw [hmatrix]
        ext i j
        exact V.cliffordSpinCandidateMatrixPointOne_apply A i j
    ⟩

/-- The literal coordinate-point kernel and the point-data kernel are the
same group under the completed coordinate/point-data equivalence. -/
def cliffordSpinCandidateCoordinateKernelMulEquivPointDataKernel :
    (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup A).ker ≃*
      (V.cliffordSpinCandidatePointDataMatrixHom A).ker where
  toFun F := ⟨V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A F.1,
    F.2⟩
  invFun d :=
    ⟨(V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).symm d.1, by
      change (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A
        ((V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).symm d.1)).matrixGroup = 1
      rw [(V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).apply_symm_apply]
      exact d.2⟩
  left_inv F := by
    apply Subtype.ext
    exact (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).symm_apply_apply F.1
  right_inv d := by
    apply Subtype.ext
    exact (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).apply_symm_apply d.1
  map_mul' F G := by
    apply Subtype.ext
    exact map_mul (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A) F.1 G.1

/-- Literal affine candidate coordinate points above the identity matrix are
multiplicatively equivalent to `mu_2(A)` for every commutative rational
algebra. -/
def rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint :
    rootsOfUnity 2 A ≃*
      (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup A).ker :=
  (V.rootsOfUnityMulEquivCliffordSpinCandidatePointDataKernel A).trans
    (V.cliffordSpinCandidateCoordinateKernelMulEquivPointDataKernel A).symm

end BaseChange

end RationalQuadraticSpaceMatrix
