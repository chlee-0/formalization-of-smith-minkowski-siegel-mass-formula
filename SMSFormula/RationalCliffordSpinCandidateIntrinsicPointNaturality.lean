import SMSFormula.RationalCliffordSpinCandidateIntrinsicPoint

/-!
# Naturality of intrinsic Clifford--Spin points over rational algebras

The intrinsic matrix-free carrier is functorial for every homomorphism of
commutative rational algebras.  The underlying Clifford element is mapped by
applying the algebra homomorphism to the coefficient factor of

```text
A tensor[ℚ] CliffordAlgebra V.quadraticForm.
```

This file proves that the intrinsic map agrees with the represented
candidate point map under the all-algebra multiplicative equivalence.  It
also records identity and composition, so the comparison is natural on all
commutative rational test algebras, including nonreduced ones.

This does not identify the intrinsic functor with a separately represented
standard Spin group scheme.  That classical recognition theorem
is not proved here.
-/

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable {A B C : Type*}
variable [CommRing A] [Algebra ℚ A]
variable [CommRing B] [Algebra ℚ B]
variable [CommRing C] [Algebra ℚ C]

/-- Coefficientwise scalar extension on the fixed rational Clifford base
change. -/
def cliffordCoordinateBaseChangeMap (f : A →ₐ[ℚ] B) :
    V.cliffordCoordinateBaseChangeAlgebra A →ₐ[ℚ]
      V.cliffordCoordinateBaseChangeAlgebra B :=
  Algebra.TensorProduct.map f
    (AlgHom.id ℚ (CliffordAlgebra V.quadraticForm))

/-- The same scalar-extension map transported to the actual Clifford
algebras of the scalar-extended quadratic forms. -/
def commutativeCliffordAlgebraBaseChangeHom (f : A →ₐ[ℚ] B) :
    CliffordAlgebra (V.commutativeScalarExtensionQuadraticForm A) →ₐ[ℚ]
      CliffordAlgebra (V.commutativeScalarExtensionQuadraticForm B) :=
  ((V.commutativeTensorCliffordEquiv B).toAlgHom.restrictScalars ℚ).comp
    ((V.cliffordCoordinateBaseChangeMap f).comp
      ((V.commutativeTensorCliffordEquiv A).symm.toAlgHom.restrictScalars ℚ))

@[simp]
theorem commutativeCliffordAlgebraBaseChangeHom_apply_tensorEquiv
    (f : A →ₐ[ℚ] B)
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.commutativeCliffordAlgebraBaseChangeHom f
        (V.commutativeTensorCliffordEquiv A x) =
      V.commutativeTensorCliffordEquiv B
        (V.cliffordCoordinateBaseChangeMap f x) := by
  simp [commutativeCliffordAlgebraBaseChangeHom]

@[simp]
theorem cliffordCoordinateBaseChangeMap_tmul
    (f : A →ₐ[ℚ] B) (a : A) (x : CliffordAlgebra V.quadraticForm) :
    V.cliffordCoordinateBaseChangeMap f (a ⊗ₜ[ℚ] x) =
      f a ⊗ₜ[ℚ] x := by
  simp [cliffordCoordinateBaseChangeMap]

@[simp]
theorem cliffordCoordinateBaseChangeMap_basis
    (f : A →ₐ[ℚ] B) (s : Finset (Fin n)) :
    V.cliffordCoordinateBaseChangeMap f
        (V.cliffordCoordinateBaseChangeBasis A s) =
      V.cliffordCoordinateBaseChangeBasis B s := by
  rw [V.cliffordCoordinateBaseChangeBasis_apply,
    V.cliffordCoordinateBaseChangeBasis_apply]
  simp

@[simp]
theorem cliffordCoordinateBaseChangeMap_vector
    (f : A →ₐ[ℚ] B) (i : Fin n) :
    V.cliffordCoordinateBaseChangeMap f
        (V.cliffordCoordinateBaseChangeVector A i) =
      V.cliffordCoordinateBaseChangeVector B i := by
  change V.cliffordCoordinateBaseChangeMap f
      (1 ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm
        (Pi.single i (1 : ℚ))) = _
  simp [cliffordCoordinateBaseChangeVector,
    cliffordCoordinateBaseChangeOfRational]

@[simp]
theorem cliffordCoordinateBaseChangeMap_vectorOfCoordinates
    (f : A →ₐ[ℚ] B) (v : Fin n → A) :
    V.cliffordCoordinateBaseChangeMap f
        (V.cliffordCoordinateBaseChangeVectorOfCoordinates A v) =
      V.cliffordCoordinateBaseChangeVectorOfCoordinates B (fun i => f (v i)) := by
  rw [cliffordCoordinateBaseChangeVectorOfCoordinates,
    cliffordCoordinateBaseChangeVectorOfCoordinates, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change V.cliffordCoordinateBaseChangeMap f
      (v i • V.cliffordCoordinateBaseChangeVector A i) =
    f (v i) • V.cliffordCoordinateBaseChangeVector B i
  change V.cliffordCoordinateBaseChangeMap f
      (v i • (1 ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm
        (Pi.single i (1 : ℚ)))) =
    f (v i) • (1 ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm
      (Pi.single i (1 : ℚ)))
  simp_rw [TensorProduct.smul_tmul']
  simp [cliffordCoordinateBaseChangeMap]

/-- Ordinary Clifford generators are transported by applying the algebra
homomorphism to their vector coordinates. -/
@[simp]
theorem commutativeCliffordAlgebraBaseChangeHom_ι
    (f : A →ₐ[ℚ] B) (v : Fin n → A) :
    V.commutativeCliffordAlgebraBaseChangeHom f
        (CliffordAlgebra.ι
          (V.commutativeScalarExtensionQuadraticForm A) v) =
      CliffordAlgebra.ι
        (V.commutativeScalarExtensionQuadraticForm B) (fun i => f (v i)) := by
  rw [← V.commutativeTensorCliffordEquiv_vectorOfCoordinates A v,
    V.commutativeCliffordAlgebraBaseChangeHom_apply_tensorEquiv,
    V.cliffordCoordinateBaseChangeMap_vectorOfCoordinates,
    V.commutativeTensorCliffordEquiv_vectorOfCoordinates]

@[simp]
theorem cliffordCoordinateBaseChangeMap_involute
    (f : A →ₐ[ℚ] B) (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.cliffordCoordinateBaseChangeMap f
        (V.cliffordCoordinateBaseChangeInvolute A x) =
      V.cliffordCoordinateBaseChangeInvolute B
        (V.cliffordCoordinateBaseChangeMap f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      rw [V.cliffordCoordinateBaseChangeInvolute_tmul,
        V.cliffordCoordinateBaseChangeMap_tmul,
        V.cliffordCoordinateBaseChangeMap_tmul,
        V.cliffordCoordinateBaseChangeInvolute_tmul]

@[simp]
theorem cliffordCoordinateBaseChangeMap_reverse
    (f : A →ₐ[ℚ] B) (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.cliffordCoordinateBaseChangeMap f
        (V.cliffordCoordinateBaseChangeReverse A x) =
      V.cliffordCoordinateBaseChangeReverse B
        (V.cliffordCoordinateBaseChangeMap f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      rw [V.cliffordCoordinateBaseChangeReverse_tmul,
        V.cliffordCoordinateBaseChangeMap_tmul,
        V.cliffordCoordinateBaseChangeMap_tmul,
        V.cliffordCoordinateBaseChangeReverse_tmul]

/-- Candidate Clifford-coordinate evaluation commutes with every
commutative-rational-algebra homomorphism. -/
@[simp]
theorem cliffordCoordinateBaseChangeMap_cliffordSpinCandidateElement
    (f : A →ₐ[ℚ] B)
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    V.cliffordCoordinateBaseChangeMap f
        (V.cliffordSpinCandidateElementOfCoordinateAlgHom A F) =
      V.cliffordSpinCandidateElementOfCoordinateAlgHom B (f.comp F) := by
  rw [cliffordSpinCandidateElementOfCoordinateAlgHom,
    cliffordSpinCandidateElementOfCoordinateAlgHom, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [V.cliffordCoordinateBaseChangeBasis_apply,
    V.cliffordCoordinateBaseChangeBasis_apply]
  simp_rw [TensorProduct.smul_tmul']
  simp only [cliffordCoordinateBaseChangeMap, smul_eq_mul, mul_one,
    AlgHom.comp_apply]
  rw [Algebra.TensorProduct.map_tmul]
  rfl

@[simp]
theorem cliffordCoordinateBaseChangeMap_id_apply
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.cliffordCoordinateBaseChangeMap (AlgHom.id ℚ A) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => simp

@[simp]
theorem cliffordCoordinateBaseChangeMap_comp_apply
    (f : A →ₐ[ℚ] B) (g : B →ₐ[ℚ] C)
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.cliffordCoordinateBaseChangeMap g
        (V.cliffordCoordinateBaseChangeMap f x) =
      V.cliffordCoordinateBaseChangeMap (g.comp f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => simp

/-- The intrinsic Spin map on arbitrary rational algebras, transported from
the represented candidate point map. -/
def cliffordSpinIntrinsicPointMap (f : A →ₐ[ℚ] B) :
    V.CliffordSpinIntrinsicPoint A →*
      V.CliffordSpinIntrinsicPoint B :=
  (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint B).toMonoidHom.comp
    ((V.cliffordSpinCandidateCoordinateAlgHomMap A f).comp
      (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A).symm.toMonoidHom)

/-- Scalar extension of an intrinsic point is coefficientwise scalar
extension of its underlying Clifford element. -/
@[simp]
theorem cliffordSpinIntrinsicPointMap_coe
    (f : A →ₐ[ℚ] B) (x : V.CliffordSpinIntrinsicPoint A) :
    (V.cliffordSpinIntrinsicPointMap f x).1 =
      V.cliffordCoordinateBaseChangeMap f x.1 := by
  let F :=
    (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A).symm x
  change V.cliffordSpinCandidateElementOfCoordinateAlgHom B (f.comp F) =
    V.cliffordCoordinateBaseChangeMap f x.1
  rw [← V.cliffordCoordinateBaseChangeMap_cliffordSpinCandidateElement]
  congr 1
  change
    (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A F).1 = x.1
  rw [MulEquiv.apply_symm_apply]

/-- The actual scalar-extended Clifford unit is natural under arbitrary
rational-algebra homomorphisms. -/
@[simp]
theorem commutativeCliffordUnit_naturality
    (f : A →ₐ[ℚ] B) (x : V.CliffordSpinIntrinsicPoint A) :
    Units.map (V.commutativeCliffordAlgebraBaseChangeHom f).toMonoidHom
        (CliffordSpinIntrinsicPoint.commutativeCliffordUnit V A x) =
      CliffordSpinIntrinsicPoint.commutativeCliffordUnit V B
        (V.cliffordSpinIntrinsicPointMap f x) := by
  apply Units.ext
  change V.commutativeCliffordAlgebraBaseChangeHom f
      (V.commutativeTensorCliffordEquiv A x.1) =
    V.commutativeTensorCliffordEquiv B
      (V.cliffordSpinIntrinsicPointMap f x).1
  rw [V.commutativeCliffordAlgebraBaseChangeHom_apply_tensorEquiv,
    V.cliffordSpinIntrinsicPointMap_coe]

/-- Entrywise scalar extension of a special-orthogonal matrix point. -/
def specialOrthogonalMatrixPointMap
    (f : A →ₐ[ℚ] B) (M : V.specialOrthogonalMatrixPoint A) :
    V.specialOrthogonalMatrixPoint B :=
  V.specialOrthogonalMatrixPointOfGroup B
    (V.specialOrthogonalMatrixGroupMap f
      (V.specialOrthogonalMatrixPointToGroup A M))

@[simp]
theorem specialOrthogonalMatrixPointMap_apply
    (f : A →ₐ[ℚ] B) (M : V.specialOrthogonalMatrixPoint A)
    (i j : Fin n) :
    (V.specialOrthogonalMatrixPointMap f M).1 i j = f (M.1 i j) := by
  change
    ((V.specialOrthogonalMatrixGroupMap f
      (V.specialOrthogonalMatrixPointToGroup A M)).1.1.1) i j = _
  rw [V.specialOrthogonalMatrixGroupMap_apply_matrix]
  simp [specialOrthogonalMatrixPointToGroup]

/-- The uniquely induced orthogonal matrix is itself natural under arbitrary
rational algebra maps. -/
@[simp]
theorem cliffordSpinIntrinsicPointMap_matrixPoint
    (f : A →ₐ[ℚ] B) (x : V.CliffordSpinIntrinsicPoint A) :
    (V.cliffordSpinIntrinsicPointMap f x).matrixPoint =
      V.specialOrthogonalMatrixPointMap f x.matrixPoint := by
  apply CliffordSpinIntrinsicPoint.matrixPoint_eq
  intro i
  calc
    (V.cliffordSpinIntrinsicPointMap f x).1 *
          V.cliffordCoordinateBaseChangeVector B i *
        V.cliffordCoordinateBaseChangeReverse B
          (V.cliffordSpinIntrinsicPointMap f x).1 =
        V.cliffordCoordinateBaseChangeMap f
          (x.1 * V.cliffordCoordinateBaseChangeVector A i *
            V.cliffordCoordinateBaseChangeReverse A x.1) := by
              rw [map_mul, map_mul,
                V.cliffordCoordinateBaseChangeMap_vector,
                V.cliffordCoordinateBaseChangeMap_reverse,
                V.cliffordSpinIntrinsicPointMap_coe]
    _ = V.cliffordCoordinateBaseChangeMap f
          (V.cliffordCoordinateBaseChangeVectorOfCoordinates A
            (fun j => x.matrixPoint.1 j i)) := by
              rw [x.vectorGraph]
              rfl
    _ = V.cliffordCoordinateBaseChangeVectorOfCoordinates B
          (fun j => f (x.matrixPoint.1 j i)) := by
              rw [V.cliffordCoordinateBaseChangeMap_vectorOfCoordinates]
    _ = ∑ j, (V.specialOrthogonalMatrixPointMap f x.matrixPoint).1 j i •
          V.cliffordCoordinateBaseChangeVector B j := by
              rw [cliffordCoordinateBaseChangeVectorOfCoordinates]
              simp

/-- Pointwise naturality of the all-algebra intrinsic recognition. -/
@[simp]
theorem cliffordSpinCandidateIntrinsicRecognition_naturality
    (f : A →ₐ[ℚ] B)
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint B
        (V.cliffordSpinCandidateCoordinateAlgHomMap A f F) =
      V.cliffordSpinIntrinsicPointMap f
        (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A F) := by
  change V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint B
      (f.comp F) =
    V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint B
      (f.comp
        ((V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A).symm
          (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A F)))
  rw [MulEquiv.symm_apply_apply]

/-- Naturality as an equality of group homomorphisms. -/
theorem cliffordSpinCandidateIntrinsicRecognition_naturality_hom
    (f : A →ₐ[ℚ] B) :
    (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint B).toMonoidHom.comp
        (V.cliffordSpinCandidateCoordinateAlgHomMap A f) =
      (V.cliffordSpinIntrinsicPointMap f).comp
        (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A).toMonoidHom := by
  apply MonoidHom.ext
  intro F
  exact V.cliffordSpinCandidateIntrinsicRecognition_naturality f F

/-- The intrinsic recognition is natural as a cover of `SO`, not merely as
an abstract group equivalence. -/
theorem cliffordSpinIntrinsicPointToSpecialOrthogonalGroup_naturality
    (f : A →ₐ[ℚ] B) :
    (V.cliffordSpinIntrinsicPointToSpecialOrthogonalGroup B).comp
        (V.cliffordSpinIntrinsicPointMap f) =
      (V.specialOrthogonalMatrixGroupMap f).comp
        (V.cliffordSpinIntrinsicPointToSpecialOrthogonalGroup A) := by
  apply MonoidHom.ext
  intro x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    V.cliffordSpinIntrinsicPointToSpecialOrthogonalGroup_apply,
    V.cliffordSpinIntrinsicPointToSpecialOrthogonalGroup_apply,
    V.cliffordSpinIntrinsicPointMap_matrixPoint]
  exact (V.specialOrthogonalMatrixPointEquivGroup B).apply_symm_apply
    (V.specialOrthogonalMatrixGroupMap f
      (V.specialOrthogonalMatrixPointToGroup A x.matrixPoint))

/-- Scalar extension on the literal intrinsic subgroup of Clifford units. -/
def cliffordSpinIntrinsicCliffordUnitSubgroupMap (f : A →ₐ[ℚ] B) :
    V.cliffordSpinIntrinsicCliffordUnitSubgroup A →*
      V.cliffordSpinIntrinsicCliffordUnitSubgroup B :=
  (V.cliffordSpinIntrinsicPointMulEquivCliffordUnitSubgroup B).toMonoidHom.comp
    ((V.cliffordSpinIntrinsicPointMap f).comp
      (V.cliffordSpinIntrinsicPointMulEquivCliffordUnitSubgroup A).symm.toMonoidHom)

/-- On literal Clifford units, intrinsic scalar extension is the
coefficientwise tensor map. -/
@[simp]
theorem cliffordSpinIntrinsicCliffordUnitSubgroupMap_coe
    (f : A →ₐ[ℚ] B)
    (u : V.cliffordSpinIntrinsicCliffordUnitSubgroup A) :
    ((V.cliffordSpinIntrinsicCliffordUnitSubgroupMap f u).1 :
        V.cliffordCoordinateBaseChangeAlgebra B) =
      V.cliffordCoordinateBaseChangeMap f
        (u.1 : V.cliffordCoordinateBaseChangeAlgebra A) := by
  let x :=
    (V.cliffordSpinIntrinsicPointMulEquivCliffordUnitSubgroup A).symm u
  change
    ((CliffordSpinIntrinsicPoint.cliffordUnit V B
      (V.cliffordSpinIntrinsicPointMap f x)) :
        V.cliffordCoordinateBaseChangeAlgebra B) =
      V.cliffordCoordinateBaseChangeMap f
        (u.1 : V.cliffordCoordinateBaseChangeAlgebra A)
  rw [CliffordSpinIntrinsicPoint.coe_cliffordUnit,
    V.cliffordSpinIntrinsicPointMap_coe]
  congr 1
  change
    (((V.cliffordSpinIntrinsicPointMulEquivCliffordUnitSubgroup A x).1 :
        (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
      V.cliffordCoordinateBaseChangeAlgebra A) =
        (u.1 : V.cliffordCoordinateBaseChangeAlgebra A)
  rw [MulEquiv.apply_symm_apply]

/-- The represented candidate and the literal intrinsic Clifford-unit
subgroup form a natural all-algebra equivalence. -/
theorem cliffordSpinCandidateIntrinsicCliffordUnitRecognition_naturality
    (f : A →ₐ[ℚ] B) :
    (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicCliffordUnitSubgroup B).toMonoidHom.comp
        (V.cliffordSpinCandidateCoordinateAlgHomMap A f) =
      (V.cliffordSpinIntrinsicCliffordUnitSubgroupMap f).comp
        (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicCliffordUnitSubgroup A).toMonoidHom := by
  apply MonoidHom.ext
  intro F
  apply
    (V.cliffordSpinIntrinsicPointMulEquivCliffordUnitSubgroup B).symm.injective
  simp [cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicCliffordUnitSubgroup,
    cliffordSpinIntrinsicCliffordUnitSubgroupMap]

@[simp]
theorem cliffordSpinIntrinsicPointMap_id :
    V.cliffordSpinIntrinsicPointMap (AlgHom.id ℚ A) =
      MonoidHom.id (V.CliffordSpinIntrinsicPoint A) := by
  apply MonoidHom.ext
  intro x
  apply CliffordSpinIntrinsicPoint.ext
  simp

@[simp]
theorem cliffordSpinIntrinsicPointMap_comp
    (f : A →ₐ[ℚ] B) (g : B →ₐ[ℚ] C) :
    (V.cliffordSpinIntrinsicPointMap g).comp
        (V.cliffordSpinIntrinsicPointMap f) =
      V.cliffordSpinIntrinsicPointMap (g.comp f) := by
  apply MonoidHom.ext
  intro x
  apply CliffordSpinIntrinsicPoint.ext
  simp

@[simp]
theorem cliffordSpinIntrinsicCliffordUnitSubgroupMap_id :
    V.cliffordSpinIntrinsicCliffordUnitSubgroupMap (AlgHom.id ℚ A) =
      MonoidHom.id (V.cliffordSpinIntrinsicCliffordUnitSubgroup A) := by
  apply MonoidHom.ext
  intro u
  apply Subtype.ext
  apply Units.ext
  simp

@[simp]
theorem cliffordSpinIntrinsicCliffordUnitSubgroupMap_comp
    (f : A →ₐ[ℚ] B) (g : B →ₐ[ℚ] C) :
    (V.cliffordSpinIntrinsicCliffordUnitSubgroupMap g).comp
        (V.cliffordSpinIntrinsicCliffordUnitSubgroupMap f) =
      V.cliffordSpinIntrinsicCliffordUnitSubgroupMap (g.comp f) := by
  apply MonoidHom.ext
  intro u
  apply Subtype.ext
  apply Units.ext
  simp

end RationalQuadraticSpaceMatrix
