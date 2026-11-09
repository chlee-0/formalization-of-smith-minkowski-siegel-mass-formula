import SMSFormula.RationalCliffordReflectionPairArbitraryBase
import SMSFormula.RationalCliffordSpinCandidatePointGroup
import SMSFormula.CliffordAlgebraEvenInvolute

/-!
# Intrinsic arbitrary-algebra points of the Clifford--Spin candidate

For every commutative rational algebra, this file removes the redundant
matrix coordinate from the finite-coordinate Clifford--Spin candidate.  An
intrinsic point is a Clifford element which

* is fixed by the grade involution;
* has reverse norm one; and
* conjugates the vector module through some determinant-one orthogonal
  matrix.

The inducing matrix is unique over every commutative rational algebra.  The
proof uses the scalar-extended Clifford embedding and the fact that `2` is
invertible in any rational algebra.  Consequently the intrinsic carrier is
multiplicatively equivalent to the already represented candidate point
functor over arbitrary algebras, not merely over fields.

This is an intrinsic functor-of-points description of the implemented
candidate.  It does not identify the functor with a separately represented
standard Spin group scheme or prove geometric connectedness.
-/

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

local notation "QA" => V.commutativeScalarExtensionQuadraticForm A

/-- The coordinate-vector copy inside the rational Clifford base change is
faithful over every commutative rational algebra. -/
theorem cliffordCoordinateBaseChangeVectorOfCoordinates_injective :
    Function.Injective
      (V.cliffordCoordinateBaseChangeVectorOfCoordinates A) := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  intro x y hxy
  have hiota : CliffordAlgebra.ι QA x = CliffordAlgebra.ι QA y := by
    simpa only [V.commutativeTensorCliffordEquiv_vectorOfCoordinates] using
      congrArg (V.commutativeTensorCliffordEquiv A) hxy
  exact CliffordAlgebra.ι_injective_of_invertible_two QA hiota

set_option backward.isDefEq.respectTransparency false in
/-- The tensor-model grade involution becomes the ordinary grade involution
under the scalar-extension Clifford equivalence. -/
theorem commutativeTensorCliffordEquiv_involute
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.commutativeTensorCliffordEquiv A
        (V.cliffordCoordinateBaseChangeInvolute A x) =
      CliffordAlgebra.involute
        (V.commutativeTensorCliffordEquiv A x) := by
  have hOf (z : V.cliffordCoordinateBaseChangeAlgebra A) :
      CliffordAlgebra.ofBaseChange A V.quadraticForm
          (V.cliffordCoordinateBaseChangeInvolute A z) =
        CliffordAlgebra.involute
          (CliffordAlgebra.ofBaseChange A V.quadraticForm z) := by
    apply (CliffordAlgebra.equivBaseChange A V.quadraticForm).injective
    change CliffordAlgebra.toBaseChange A V.quadraticForm
          (CliffordAlgebra.ofBaseChange A V.quadraticForm
            (V.cliffordCoordinateBaseChangeInvolute A z)) =
      CliffordAlgebra.toBaseChange A V.quadraticForm
        (CliffordAlgebra.involute
          (CliffordAlgebra.ofBaseChange A V.quadraticForm z))
    rw [CliffordAlgebra.toBaseChange_ofBaseChange,
      CliffordAlgebra.toBaseChange_involute,
      CliffordAlgebra.toBaseChange_ofBaseChange]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a z => simp [V.cliffordCoordinateBaseChangeInvolute_tmul]
  have hIso
      (z : CliffordAlgebra (V.quadraticForm.baseChange A)) :
      V.commutativeScalarExtensionCliffordAlgEquiv A
          (CliffordAlgebra.involute z) =
        CliffordAlgebra.involute
          (V.commutativeScalarExtensionCliffordAlgEquiv A z) := by
    induction z using CliffordAlgebra.induction with
    | algebraMap r => simp
    | ι v =>
        simp [commutativeScalarExtensionCliffordAlgEquiv,
          CliffordAlgebra.equivOfIsometry_apply]
    | mul x y hx hy => simp_all
    | add x y hx hy => simp_all
  rw [commutativeTensorCliffordEquiv, AlgEquiv.trans_apply]
  change V.commutativeScalarExtensionCliffordAlgEquiv A
      (CliffordAlgebra.ofBaseChange A V.quadraticForm
        (V.cliffordCoordinateBaseChangeInvolute A x)) =
    CliffordAlgebra.involute
      (V.commutativeScalarExtensionCliffordAlgEquiv A
        (CliffordAlgebra.ofBaseChange A V.quadraticForm x))
  rw [hOf, hIso]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor-model reverse becomes the ordinary Clifford reverse under
the scalar-extension equivalence. -/
theorem commutativeTensorCliffordEquiv_reverse
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.commutativeTensorCliffordEquiv A
        (V.cliffordCoordinateBaseChangeReverse A x) =
      CliffordAlgebra.reverse
        (V.commutativeTensorCliffordEquiv A x) := by
  have hOf (z : V.cliffordCoordinateBaseChangeAlgebra A) :
      CliffordAlgebra.ofBaseChange A V.quadraticForm
          (V.cliffordCoordinateBaseChangeReverse A z) =
        CliffordAlgebra.reverse
          (CliffordAlgebra.ofBaseChange A V.quadraticForm z) := by
    apply (CliffordAlgebra.equivBaseChange A V.quadraticForm).injective
    change CliffordAlgebra.toBaseChange A V.quadraticForm
          (CliffordAlgebra.ofBaseChange A V.quadraticForm
            (V.cliffordCoordinateBaseChangeReverse A z)) =
      CliffordAlgebra.toBaseChange A V.quadraticForm
        (CliffordAlgebra.reverse
          (CliffordAlgebra.ofBaseChange A V.quadraticForm z))
    rw [CliffordAlgebra.toBaseChange_ofBaseChange,
      CliffordAlgebra.toBaseChange_reverse,
      CliffordAlgebra.toBaseChange_ofBaseChange]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a z => simp [V.cliffordCoordinateBaseChangeReverse_tmul]
  have hIso
      (z : CliffordAlgebra (V.quadraticForm.baseChange A)) :
      V.commutativeScalarExtensionCliffordAlgEquiv A
          (CliffordAlgebra.reverse z) =
        CliffordAlgebra.reverse
          (V.commutativeScalarExtensionCliffordAlgEquiv A z) := by
    induction z using CliffordAlgebra.induction with
    | algebraMap r => simp
    | ι v =>
        simp [commutativeScalarExtensionCliffordAlgEquiv,
          CliffordAlgebra.equivOfIsometry_apply]
    | mul x y hx hy =>
        simp only [CliffordAlgebra.reverse.map_mul, map_mul, hx, hy]
    | add x y hx hy => simp_all
  rw [commutativeTensorCliffordEquiv, AlgEquiv.trans_apply]
  change V.commutativeScalarExtensionCliffordAlgEquiv A
      (CliffordAlgebra.ofBaseChange A V.quadraticForm
        (V.cliffordCoordinateBaseChangeReverse A x)) =
    CliffordAlgebra.reverse
      (V.commutativeScalarExtensionCliffordAlgEquiv A
        (CliffordAlgebra.ofBaseChange A V.quadraticForm x))
  rw [hOf, hIso]

/-- In the tensor coordinates used by the represented candidate, the fixed
grade-involution equation is exactly literal membership in the even part of
the scalar-extended Clifford algebra. -/
theorem commutativeTensorCliffordEquiv_mem_even_iff
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.commutativeTensorCliffordEquiv A x ∈ CliffordAlgebra.even QA ↔
      V.cliffordCoordinateBaseChangeInvolute A x = x := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  rw [CliffordAlgebra.mem_even_iff_involute_eq_of_invertible_two,
    ← V.commutativeTensorCliffordEquiv_involute A]
  exact (V.commutativeTensorCliffordEquiv A).injective.eq_iff

/-- A Clifford element determines at most one special-orthogonal matrix
through its conjugation action on the coordinate vectors. -/
theorem cliffordSpinIntrinsicMatrixPoint_unique
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (M N : V.specialOrthogonalMatrixPoint A)
    (hM : ∀ i,
      x * V.cliffordCoordinateBaseChangeVector A i *
          V.cliffordCoordinateBaseChangeReverse A x =
        ∑ j, M.1 j i • V.cliffordCoordinateBaseChangeVector A j)
    (hN : ∀ i,
      x * V.cliffordCoordinateBaseChangeVector A i *
          V.cliffordCoordinateBaseChangeReverse A x =
        ∑ j, N.1 j i • V.cliffordCoordinateBaseChangeVector A j) :
    M = N := by
  apply Subtype.ext
  ext j i
  have hgraph :
      (∑ k, M.1 k i • V.cliffordCoordinateBaseChangeVector A k) =
        ∑ k, N.1 k i • V.cliffordCoordinateBaseChangeVector A k := by
    rw [← hM i, ← hN i]
  have hcoords :
      V.cliffordCoordinateBaseChangeVectorOfCoordinates A (fun k => M.1 k i) =
        V.cliffordCoordinateBaseChangeVectorOfCoordinates A
          (fun k => N.1 k i) := by
    simpa [cliffordCoordinateBaseChangeVectorOfCoordinates] using hgraph
  exact congrFun
    (V.cliffordCoordinateBaseChangeVectorOfCoordinates_injective A hcoords) j

/-- Arbitrary-algebra candidate point data are determined by their Clifford
coordinate alone. -/
theorem CliffordSpinCandidatePointData.matrixPoint_eq_of_clifford_eq_arbitrary
    (d e : V.CliffordSpinCandidatePointData A)
    (h : d.clifford = e.clifford) :
    d.matrixPoint = e.matrixPoint := by
  exact V.cliffordSpinIntrinsicMatrixPoint_unique A d.clifford
    d.matrixPoint e.matrixPoint d.vectorGraph (fun i => by
      simpa [h] using e.vectorGraph i)

/-- Extensionality of arbitrary-algebra candidate points by the Clifford
coordinate. -/
theorem CliffordSpinCandidatePointData.ext_clifford
    (d e : V.CliffordSpinCandidatePointData A)
    (h : d.clifford = e.clifford) :
    d = e := by
  apply CliffordSpinCandidatePointData.ext
  · exact h
  · exact d.matrixPoint_eq_of_clifford_eq_arbitrary V A e h

/-- The intrinsic Clifford conditions defining the implemented Spin
candidate on an arbitrary commutative rational algebra.  The matrix is only
asserted to exist; its uniqueness is proved separately. -/
def IsCliffordSpinIntrinsicPoint
    (x : V.cliffordCoordinateBaseChangeAlgebra A) : Prop :=
  V.cliffordCoordinateBaseChangeInvolute A x = x ∧
    x * V.cliffordCoordinateBaseChangeReverse A x = 1 ∧
      ∃ M : V.specialOrthogonalMatrixPoint A, ∀ i,
        x * V.cliffordCoordinateBaseChangeVector A i *
            V.cliffordCoordinateBaseChangeReverse A x =
          ∑ j, M.1 j i • V.cliffordCoordinateBaseChangeVector A j

/-- Matrix-free intrinsic points of the implemented Clifford--Spin
candidate. -/
abbrev CliffordSpinIntrinsicPoint :=
  {x : V.cliffordCoordinateBaseChangeAlgebra A //
    V.IsCliffordSpinIntrinsicPoint A x}

namespace CliffordSpinIntrinsicPoint

@[ext]
theorem ext
    {x y : V.CliffordSpinIntrinsicPoint A}
    (h : x.1 = y.1) : x = y :=
  Subtype.ext h

@[simp]
theorem involute_eq (x : V.CliffordSpinIntrinsicPoint A) :
    V.cliffordCoordinateBaseChangeInvolute A x.1 = x.1 :=
  x.2.1

/-- Every intrinsic point is literally even after transport to the
scalar-extended Clifford algebra. -/
theorem commutativeClifford_mem_even
    (x : V.CliffordSpinIntrinsicPoint A) :
    V.commutativeTensorCliffordEquiv A x.1 ∈ CliffordAlgebra.even QA :=
  (V.commutativeTensorCliffordEquiv_mem_even_iff A x.1).2 x.involute_eq

@[simp]
theorem mul_reverse_eq_one (x : V.CliffordSpinIntrinsicPoint A) :
    x.1 * V.cliffordCoordinateBaseChangeReverse A x.1 = 1 :=
  x.2.2.1

/-- Reverse norm one makes the intrinsic Clifford element a genuine unit
over every commutative rational algebra. -/
def cliffordUnit (x : V.CliffordSpinIntrinsicPoint A) :
    (V.cliffordCoordinateBaseChangeAlgebra A)ˣ :=
  V.cliffordCoordinateBaseChangeUnitOfMulReverseEqOne A
    x.1 x.mul_reverse_eq_one

@[simp]
theorem coe_cliffordUnit (x : V.CliffordSpinIntrinsicPoint A) :
    (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) = x.1 :=
  rfl

/-- The actual scalar-extended Clifford unit represented by an intrinsic
point. -/
def commutativeCliffordUnit (x : V.CliffordSpinIntrinsicPoint A) :
    (CliffordAlgebra QA)ˣ :=
  Units.map (V.commutativeTensorCliffordEquiv A).toMonoidHom x.cliffordUnit

@[simp]
theorem coe_commutativeCliffordUnit
    (x : V.CliffordSpinIntrinsicPoint A) :
    (x.commutativeCliffordUnit : CliffordAlgebra QA) =
      V.commutativeTensorCliffordEquiv A x.1 :=
  rfl

/-- The transported Clifford element has ordinary reverse norm one. -/
theorem commutativeClifford_mul_reverse_eq_one
    (x : V.CliffordSpinIntrinsicPoint A) :
    V.commutativeTensorCliffordEquiv A x.1 *
        CliffordAlgebra.reverse
          (V.commutativeTensorCliffordEquiv A x.1) = 1 := by
  rw [← V.commutativeTensorCliffordEquiv_reverse A, ← map_mul,
    x.mul_reverse_eq_one, map_one]

/-- The uniquely determined special-orthogonal action of an intrinsic
point. -/
def matrixPoint (x : V.CliffordSpinIntrinsicPoint A) :
    V.specialOrthogonalMatrixPoint A :=
  Classical.choose x.2.2.2

@[simp]
theorem vectorGraph (x : V.CliffordSpinIntrinsicPoint A) (i : Fin n) :
    x.1 * V.cliffordCoordinateBaseChangeVector A i *
          V.cliffordCoordinateBaseChangeReverse A x.1 =
      ∑ j, x.matrixPoint.1 j i •
        V.cliffordCoordinateBaseChangeVector A j :=
  Classical.choose_spec x.2.2.2 i

/-- The intrinsic Clifford unit normalizes the whole vector module, not only
its coordinate basis. -/
theorem vectorGraph_coordinates
    (x : V.CliffordSpinIntrinsicPoint A) (v : Fin n → A) :
    x.1 * V.cliffordCoordinateBaseChangeVectorOfCoordinates A v *
          V.cliffordCoordinateBaseChangeReverse A x.1 =
      V.cliffordCoordinateBaseChangeVectorOfCoordinates A
        (Matrix.mulVec x.matrixPoint.1 v) := by
  rw [cliffordCoordinateBaseChangeVectorOfCoordinates,
    V.cliffordCoordinateBaseChange_mul_sum_mul]
  simp_rw [x.vectorGraph, Finset.smul_sum, smul_smul]
  rw [cliffordCoordinateBaseChangeVectorOfCoordinates, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem matrixPoint_eq
    (x : V.CliffordSpinIntrinsicPoint A)
    (M : V.specialOrthogonalMatrixPoint A)
    (hM : ∀ i,
      x.1 * V.cliffordCoordinateBaseChangeVector A i *
          V.cliffordCoordinateBaseChangeReverse A x.1 =
        ∑ j, M.1 j i • V.cliffordCoordinateBaseChangeVector A j) :
    x.matrixPoint = M :=
  V.cliffordSpinIntrinsicMatrixPoint_unique A x.1 x.matrixPoint M
    x.vectorGraph hM

/-- Restore the uniquely determined matrix coordinate. -/
def toCandidatePointData (x : V.CliffordSpinIntrinsicPoint A) :
    V.CliffordSpinCandidatePointData A where
  clifford := x.1
  matrixPoint := x.matrixPoint
  involute_eq := x.involute_eq
  mul_reverse_eq_one := x.mul_reverse_eq_one
  vectorGraph := x.vectorGraph

/-- Forget the redundant stored matrix coordinate. -/
def ofCandidatePointData (d : V.CliffordSpinCandidatePointData A) :
    V.CliffordSpinIntrinsicPoint A :=
  ⟨d.clifford, d.involute_eq, d.mul_reverse_eq_one,
    ⟨d.matrixPoint, d.vectorGraph⟩⟩

@[simp]
theorem coe_ofCandidatePointData
    (d : V.CliffordSpinCandidatePointData A) :
    (ofCandidatePointData V A d).1 = d.clifford :=
  rfl

@[simp]
theorem toCandidatePointData_clifford
    (x : V.CliffordSpinIntrinsicPoint A) :
    (toCandidatePointData V A x).clifford = x.1 :=
  rfl

end CliffordSpinIntrinsicPoint

/-- Candidate point data and intrinsic Clifford points are equivalent over
every commutative rational algebra. -/
def cliffordSpinCandidatePointDataEquivIntrinsicPoint :
    V.CliffordSpinCandidatePointData A ≃
      V.CliffordSpinIntrinsicPoint A where
  toFun := CliffordSpinIntrinsicPoint.ofCandidatePointData V A
  invFun := CliffordSpinIntrinsicPoint.toCandidatePointData V A
  left_inv d := by
    apply CliffordSpinCandidatePointData.ext
    · rfl
    · exact CliffordSpinIntrinsicPoint.matrixPoint_eq V A
        (CliffordSpinIntrinsicPoint.ofCandidatePointData V A d)
        d.matrixPoint d.vectorGraph
  right_inv x := by
    apply CliffordSpinIntrinsicPoint.ext
    rfl

/-- The group structure on intrinsic points transported from the already
verified candidate point group. -/
noncomputable instance cliffordSpinIntrinsicPointGroup :
    Group (V.CliffordSpinIntrinsicPoint A) :=
  Equiv.group (V.cliffordSpinCandidatePointDataEquivIntrinsicPoint A).symm

@[simp]
theorem CliffordSpinIntrinsicPoint.one_coe :
    ((1 : V.CliffordSpinIntrinsicPoint A).1) = 1 := by
  change
    (CliffordSpinIntrinsicPoint.ofCandidatePointData V A
      (1 : V.CliffordSpinCandidatePointData A)).1 = 1
  rfl

@[simp]
theorem CliffordSpinIntrinsicPoint.mul_coe
    (x y : V.CliffordSpinIntrinsicPoint A) :
    (x * y).1 = x.1 * y.1 := by
  change
    (CliffordSpinIntrinsicPoint.ofCandidatePointData V A
      (CliffordSpinIntrinsicPoint.toCandidatePointData V A x *
        CliffordSpinIntrinsicPoint.toCandidatePointData V A y)).1 = _
  rfl

@[simp]
theorem CliffordSpinIntrinsicPoint.inv_coe
    (x : V.CliffordSpinIntrinsicPoint A) :
    x⁻¹.1 = V.cliffordCoordinateBaseChangeReverse A x.1 := by
  change
    (CliffordSpinIntrinsicPoint.ofCandidatePointData V A
      (CliffordSpinIntrinsicPoint.toCandidatePointData V A x)⁻¹).1 = _
  rfl

/-- Intrinsic points embed multiplicatively into the units of the Clifford
base change. -/
def cliffordSpinIntrinsicPointCliffordUnitHom :
    V.CliffordSpinIntrinsicPoint A →*
      (V.cliffordCoordinateBaseChangeAlgebra A)ˣ where
  toFun := CliffordSpinIntrinsicPoint.cliffordUnit V A
  map_one' := by
    apply Units.ext
    simp
  map_mul' x y := by
    apply Units.ext
    simp

theorem cliffordSpinIntrinsicPointCliffordUnitHom_injective :
    Function.Injective (V.cliffordSpinIntrinsicPointCliffordUnitHom A) := by
  intro x y hxy
  apply CliffordSpinIntrinsicPoint.ext
  exact congrArg
    (fun u : (V.cliffordCoordinateBaseChangeAlgebra A)ˣ =>
      (u : V.cliffordCoordinateBaseChangeAlgebra A)) hxy

/-- The literal subgroup of Clifford units represented by the intrinsic
conditions. -/
def cliffordSpinIntrinsicCliffordUnitSubgroup :
    Subgroup (V.cliffordCoordinateBaseChangeAlgebra A)ˣ :=
  (V.cliffordSpinIntrinsicPointCliffordUnitHom A).range

/-- Membership in the intrinsic Clifford-unit subgroup is exactly the
matrix-free intrinsic predicate on the underlying Clifford element. -/
theorem mem_cliffordSpinIntrinsicCliffordUnitSubgroup_iff
    (u : (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
    u ∈ V.cliffordSpinIntrinsicCliffordUnitSubgroup A ↔
      V.IsCliffordSpinIntrinsicPoint A
        (u : V.cliffordCoordinateBaseChangeAlgebra A) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hu
    let x : V.CliffordSpinIntrinsicPoint A := ⟨(u : _), hu⟩
    refine ⟨x, ?_⟩
    apply Units.ext
    rfl

/-- Matrix-free intrinsic points are exactly their literal subgroup of
Clifford units. -/
def cliffordSpinIntrinsicPointMulEquivCliffordUnitSubgroup :
    V.CliffordSpinIntrinsicPoint A ≃*
      V.cliffordSpinIntrinsicCliffordUnitSubgroup A :=
  MulEquiv.ofBijective
    (V.cliffordSpinIntrinsicPointCliffordUnitHom A).rangeRestrict
    ⟨by
      intro x y hxy
      exact V.cliffordSpinIntrinsicPointCliffordUnitHom_injective A
        (congrArg Subtype.val hxy),
    by
      intro y
      rcases y.2 with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx⟩

/-- The matrix-free intrinsic carrier is multiplicatively equivalent to the
represented candidate's point data. -/
def cliffordSpinCandidatePointDataMulEquivIntrinsicPoint :
    V.CliffordSpinCandidatePointData A ≃*
      V.CliffordSpinIntrinsicPoint A :=
  (Equiv.mulEquiv
    (V.cliffordSpinCandidatePointDataEquivIntrinsicPoint A).symm).symm

@[simp]
theorem cliffordSpinCandidatePointDataMulEquivIntrinsicPoint_apply_coe
    (d : V.CliffordSpinCandidatePointData A) :
    (V.cliffordSpinCandidatePointDataMulEquivIntrinsicPoint A d).1 =
      d.clifford :=
  by
    change (CliffordSpinIntrinsicPoint.ofCandidatePointData V A d).1 = _
    rfl

@[simp]
theorem cliffordSpinCandidatePointDataMulEquivIntrinsicPoint_symm_apply_clifford
    (x : V.CliffordSpinIntrinsicPoint A) :
    ((V.cliffordSpinCandidatePointDataMulEquivIntrinsicPoint A).symm x).clifford =
      x.1 :=
  by
    change (CliffordSpinIntrinsicPoint.toCandidatePointData V A x).clifford = _
    rfl

/-- The finite coordinate ring represents the intrinsic Clifford carrier on
every commutative rational algebra. -/
def cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint :
    (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) ≃*
      V.CliffordSpinIntrinsicPoint A :=
  (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).trans
    (V.cliffordSpinCandidatePointDataMulEquivIntrinsicPoint A)

@[simp]
theorem cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint_apply_coe
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A F).1 =
      V.cliffordSpinCandidateElementOfCoordinateAlgHom A F :=
  by
    change
      (CliffordSpinIntrinsicPoint.ofCandidatePointData V A
        (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F)).1 = _
    rfl

/-- The finite coordinate ring represents the literal intrinsic subgroup of
Clifford units on every commutative rational algebra. -/
def cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicCliffordUnitSubgroup :
    (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) ≃*
      V.cliffordSpinIntrinsicCliffordUnitSubgroup A :=
  (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A).trans
    (V.cliffordSpinIntrinsicPointMulEquivCliffordUnitSubgroup A)

/-- The stored special-orthogonal action is a homomorphism on candidate
point data. -/
def cliffordSpinCandidatePointDataToSpecialOrthogonalGroup :
    V.CliffordSpinCandidatePointData A →*
      V.specialOrthogonalMatrixGroup A where
  toFun d := d.matrixGroup
  map_one' := CliffordSpinCandidatePointData.one_matrixGroup V A
  map_mul' d e := CliffordSpinCandidatePointData.mul_matrixGroup V A d e

/-- The uniquely induced determinant-one orthogonal action of an intrinsic
Clifford point, as an element of the special orthogonal group. -/
def cliffordSpinIntrinsicPointToSpecialOrthogonalGroup :
    V.CliffordSpinIntrinsicPoint A →*
      V.specialOrthogonalMatrixGroup A :=
  (V.cliffordSpinCandidatePointDataToSpecialOrthogonalGroup A).comp
    (V.cliffordSpinCandidatePointDataMulEquivIntrinsicPoint A).symm.toMonoidHom

@[simp]
theorem cliffordSpinIntrinsicPointToSpecialOrthogonalGroup_apply
    (x : V.CliffordSpinIntrinsicPoint A) :
    V.cliffordSpinIntrinsicPointToSpecialOrthogonalGroup A x =
      V.specialOrthogonalMatrixPointToGroup A x.matrixPoint :=
  rfl

end RationalQuadraticSpaceMatrix
