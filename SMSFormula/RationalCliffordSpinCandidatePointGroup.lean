import SMSFormula.RationalCliffordSpinCandidatePointData
import SMSFormula.RationalSpecialOrthogonalGroupScheme

/-!
# Group structure on arbitrary-algebra Clifford--Spin candidate points

The coordinate solution data from
`RationalCliffordSpinCandidatePointData.lean` are closed under Clifford
multiplication and reverse.  The matrix component uses the already completed
special-orthogonal matrix group.  This gives a genuine group-valued point
functor over every commutative rational algebra, without identifying its
field points with mathlib's closure-generated `spinGroup`.
-/

noncomputable section

open CliffordAlgebra CategoryTheory Limits Opposite AlgebraicGeometry
open scoped Matrix TensorProduct CategoryTheory.MonObj MonoidalCategory

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

def CliffordSpinCandidatePointData.matrixGroup
    (d : V.CliffordSpinCandidatePointData A) :
    V.specialOrthogonalMatrixGroup A :=
  V.specialOrthogonalMatrixPointToGroup A d.matrixPoint

@[simp]
theorem CliffordSpinCandidatePointData.matrixGroup_coe
    (d : V.CliffordSpinCandidatePointData A) :
    d.matrixGroup.1.1.1 = d.matrixPoint.1 := by
  ext i j
  simp [CliffordSpinCandidatePointData.matrixGroup,
    specialOrthogonalMatrixPointToGroup]

def cliffordSpinCandidateMatrixPointOne :
    V.specialOrthogonalMatrixPoint A :=
  V.specialOrthogonalMatrixPointOfGroup A 1

@[simp]
theorem cliffordSpinCandidateMatrixPointOne_apply (i j : Fin n) :
    (V.cliffordSpinCandidateMatrixPointOne A).1 i j =
      (1 : Matrix (Fin n) (Fin n) A) i j := by
  simp [cliffordSpinCandidateMatrixPointOne,
    specialOrthogonalMatrixPointOfGroup]

def cliffordSpinCandidateMatrixPointMul
    (d e : V.CliffordSpinCandidatePointData A) :
    V.specialOrthogonalMatrixPoint A :=
  V.specialOrthogonalMatrixPointOfGroup A (d.matrixGroup * e.matrixGroup)

@[simp]
theorem cliffordSpinCandidateMatrixPointMul_apply
    (d e : V.CliffordSpinCandidatePointData A) (i j : Fin n) :
    (V.cliffordSpinCandidateMatrixPointMul A d e).1 i j =
      ∑ k, d.matrixPoint.1 i k * e.matrixPoint.1 k j := by
  simp [cliffordSpinCandidateMatrixPointMul,
    specialOrthogonalMatrixPointOfGroup, Matrix.mul_apply]

def cliffordSpinCandidateMatrixPointInv
    (d : V.CliffordSpinCandidatePointData A) :
    V.specialOrthogonalMatrixPoint A :=
  V.specialOrthogonalMatrixPointOfGroup A d.matrixGroup⁻¹

@[simp]
theorem cliffordSpinCandidateMatrixPointInv_apply
    (d : V.CliffordSpinCandidatePointData A) (i j : Fin n) :
    (V.cliffordSpinCandidateMatrixPointInv A d).1 i j =
      (d.matrixGroup⁻¹).1.1.1 i j := by
  rfl

theorem cliffordSpinCandidateMatrix_mul_inv_apply
    (d : V.CliffordSpinCandidatePointData A) (i k : Fin n) :
    ∑ j, d.matrixPoint.1 i j *
        (V.cliffordSpinCandidateMatrixPointInv A d).1 j k =
      (1 : Matrix (Fin n) (Fin n) A) i k := by
  rw [← Matrix.mul_apply]
  change (d.matrixPoint.1 * (d.matrixGroup⁻¹).1.1.1) i k = _
  rw [← d.matrixGroup_coe]
  rw [← Matrix.GeneralLinearGroup.coe_mul]
  change ((d.matrixGroup * d.matrixGroup⁻¹).1.1.1) i k = _
  rw [mul_inv_cancel]
  rfl

theorem cliffordCoordinateBaseChange_mul_sum_mul
    (x r : V.cliffordCoordinateBaseChangeAlgebra A)
    (a : Fin n → A) :
    x * (∑ j, a j • V.cliffordCoordinateBaseChangeVector A j) * r =
      ∑ j, a j •
        (x * V.cliffordCoordinateBaseChangeVector A j * r) := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Algebra.mul_smul_comm (R := A) (a j) x
      (V.cliffordCoordinateBaseChangeVector A j),
    Algebra.smul_mul_assoc (R := A)]

def cliffordSpinCandidatePointDataOne :
    V.CliffordSpinCandidatePointData A where
  clifford := 1
  matrixPoint := V.cliffordSpinCandidateMatrixPointOne A
  involute_eq := map_one _
  mul_reverse_eq_one := by simp
  vectorGraph := by
    intro i
    simp [Matrix.one_apply]

def cliffordSpinCandidatePointDataMul
    (d e : V.CliffordSpinCandidatePointData A) :
    V.CliffordSpinCandidatePointData A where
  clifford := d.clifford * e.clifford
  matrixPoint := V.cliffordSpinCandidateMatrixPointMul A d e
  involute_eq := by
    rw [map_mul, d.involute_eq, e.involute_eq]
  mul_reverse_eq_one := by
    rw [V.cliffordCoordinateBaseChangeReverse_mul]
    calc
      (d.clifford * e.clifford) *
          (V.cliffordCoordinateBaseChangeReverse A e.clifford *
            V.cliffordCoordinateBaseChangeReverse A d.clifford) =
        d.clifford *
          (e.clifford * V.cliffordCoordinateBaseChangeReverse A e.clifford) *
            V.cliffordCoordinateBaseChangeReverse A d.clifford := by
              simp only [mul_assoc]
      _ = d.clifford * V.cliffordCoordinateBaseChangeReverse A d.clifford := by
        rw [e.mul_reverse_eq_one, mul_one]
      _ = 1 := d.mul_reverse_eq_one
  vectorGraph := by
    intro i
    rw [V.cliffordCoordinateBaseChangeReverse_mul]
    calc
      (d.clifford * e.clifford) *
            V.cliffordCoordinateBaseChangeVector A i *
          (V.cliffordCoordinateBaseChangeReverse A e.clifford *
            V.cliffordCoordinateBaseChangeReverse A d.clifford) =
        d.clifford *
            (e.clifford * V.cliffordCoordinateBaseChangeVector A i *
              V.cliffordCoordinateBaseChangeReverse A e.clifford) *
          V.cliffordCoordinateBaseChangeReverse A d.clifford := by
            simp only [mul_assoc]
      _ = d.clifford *
            (∑ j, e.matrixPoint.1 j i •
              V.cliffordCoordinateBaseChangeVector A j) *
          V.cliffordCoordinateBaseChangeReverse A d.clifford := by
            rw [e.vectorGraph]
      _ = ∑ j, e.matrixPoint.1 j i •
          (d.clifford * V.cliffordCoordinateBaseChangeVector A j *
            V.cliffordCoordinateBaseChangeReverse A d.clifford) :=
        V.cliffordCoordinateBaseChange_mul_sum_mul A _ _ _
      _ = ∑ j, e.matrixPoint.1 j i •
          (∑ k, d.matrixPoint.1 k j •
            V.cliffordCoordinateBaseChangeVector A k) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [d.vectorGraph]
      _ = ∑ k, (∑ j, d.matrixPoint.1 k j * e.matrixPoint.1 j i) •
          V.cliffordCoordinateBaseChangeVector A k := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_comm]
      _ = ∑ k, (V.cliffordSpinCandidateMatrixPointMul A d e).1 k i •
          V.cliffordCoordinateBaseChangeVector A k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [V.cliffordSpinCandidateMatrixPointMul_apply]

def cliffordSpinCandidatePointDataInv
    (d : V.CliffordSpinCandidatePointData A) :
    V.CliffordSpinCandidatePointData A where
  clifford := V.cliffordCoordinateBaseChangeReverse A d.clifford
  matrixPoint := V.cliffordSpinCandidateMatrixPointInv A d
  involute_eq := by
    rw [← V.cliffordCoordinateBaseChangeReverse_involute,
      d.involute_eq]
  mul_reverse_eq_one := by
    rw [V.cliffordCoordinateBaseChangeReverse_reverse]
    exact V.cliffordCoordinateBaseChange_reverse_mul_eq_one_of_mul_reverse_eq_one
      A d.clifford d.mul_reverse_eq_one
  vectorGraph := by
    intro i
    have hx : IsUnit d.clifford :=
      V.cliffordCoordinateBaseChange_isUnit_of_mul_reverse_eq_one A
        d.clifford d.mul_reverse_eq_one
    have hr : IsUnit (V.cliffordCoordinateBaseChangeReverse A d.clifford) := by
      exact ⟨d.cliffordUnit⁻¹, rfl⟩
    apply hx.mul_left_cancel
    apply hr.mul_right_cancel
    rw [V.cliffordCoordinateBaseChangeReverse_reverse]
    calc
      d.clifford *
            (V.cliffordCoordinateBaseChangeReverse A d.clifford *
              V.cliffordCoordinateBaseChangeVector A i * d.clifford) *
          V.cliffordCoordinateBaseChangeReverse A d.clifford =
        V.cliffordCoordinateBaseChangeVector A i := by
          simp only [mul_assoc, d.mul_reverse_eq_one, mul_one]
          rw [← mul_assoc, d.mul_reverse_eq_one, one_mul]
      _ = ∑ k, (1 : Matrix (Fin n) (Fin n) A) k i •
          V.cliffordCoordinateBaseChangeVector A k := by
        simp [Matrix.one_apply]
      _ = ∑ k, (∑ j, d.matrixPoint.1 k j *
            (V.cliffordSpinCandidateMatrixPointInv A d).1 j i) •
          V.cliffordCoordinateBaseChangeVector A k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [V.cliffordSpinCandidateMatrix_mul_inv_apply]
      _ = ∑ j, (V.cliffordSpinCandidateMatrixPointInv A d).1 j i •
          (∑ k, d.matrixPoint.1 k j •
            V.cliffordCoordinateBaseChangeVector A k) := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_comm]
      _ = ∑ j, (V.cliffordSpinCandidateMatrixPointInv A d).1 j i •
          (d.clifford * V.cliffordCoordinateBaseChangeVector A j *
            V.cliffordCoordinateBaseChangeReverse A d.clifford) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [d.vectorGraph]
      _ = d.clifford *
            (∑ j, (V.cliffordSpinCandidateMatrixPointInv A d).1 j i •
              V.cliffordCoordinateBaseChangeVector A j) *
          V.cliffordCoordinateBaseChangeReverse A d.clifford := by
        rw [V.cliffordCoordinateBaseChange_mul_sum_mul]

noncomputable instance : One (V.CliffordSpinCandidatePointData A) :=
  ⟨V.cliffordSpinCandidatePointDataOne A⟩

noncomputable instance : Mul (V.CliffordSpinCandidatePointData A) :=
  ⟨V.cliffordSpinCandidatePointDataMul A⟩

noncomputable instance : Inv (V.CliffordSpinCandidatePointData A) :=
  ⟨V.cliffordSpinCandidatePointDataInv A⟩

@[simp]
theorem CliffordSpinCandidatePointData.one_clifford :
    (1 : V.CliffordSpinCandidatePointData A).clifford = 1 := rfl

@[simp]
theorem CliffordSpinCandidatePointData.mul_clifford
    (d e : V.CliffordSpinCandidatePointData A) :
    (d * e).clifford = d.clifford * e.clifford := rfl

@[simp]
theorem CliffordSpinCandidatePointData.inv_clifford
    (d : V.CliffordSpinCandidatePointData A) :
    d⁻¹.clifford = V.cliffordCoordinateBaseChangeReverse A d.clifford := rfl

@[simp]
theorem CliffordSpinCandidatePointData.one_matrixPoint :
    (1 : V.CliffordSpinCandidatePointData A).matrixPoint =
      V.cliffordSpinCandidateMatrixPointOne A := rfl

@[simp]
theorem CliffordSpinCandidatePointData.mul_matrixPoint
    (d e : V.CliffordSpinCandidatePointData A) :
    (d * e).matrixPoint = V.cliffordSpinCandidateMatrixPointMul A d e := rfl

@[simp]
theorem CliffordSpinCandidatePointData.inv_matrixPoint
    (d : V.CliffordSpinCandidatePointData A) :
    d⁻¹.matrixPoint = V.cliffordSpinCandidateMatrixPointInv A d := rfl

@[simp]
theorem CliffordSpinCandidatePointData.one_matrixGroup :
    (1 : V.CliffordSpinCandidatePointData A).matrixGroup = 1 := by
  exact (V.specialOrthogonalMatrixPointEquivGroup A).apply_symm_apply 1

@[simp]
theorem CliffordSpinCandidatePointData.mul_matrixGroup
    (d e : V.CliffordSpinCandidatePointData A) :
    (d * e).matrixGroup = d.matrixGroup * e.matrixGroup := by
  exact (V.specialOrthogonalMatrixPointEquivGroup A).apply_symm_apply
    (d.matrixGroup * e.matrixGroup)

@[simp]
theorem CliffordSpinCandidatePointData.inv_matrixGroup
    (d : V.CliffordSpinCandidatePointData A) :
    d⁻¹.matrixGroup = d.matrixGroup⁻¹ := by
  exact (V.specialOrthogonalMatrixPointEquivGroup A).apply_symm_apply
    d.matrixGroup⁻¹

noncomputable instance : Group (V.CliffordSpinCandidatePointData A) where
  mul_assoc d e f := by
    apply CliffordSpinCandidatePointData.ext
    · simp only [CliffordSpinCandidatePointData.mul_clifford]
      rw [mul_assoc]
    · apply (V.specialOrthogonalMatrixPointEquivGroup A).injective
      change ((d * e) * f).matrixGroup = (d * (e * f)).matrixGroup
      simp only [CliffordSpinCandidatePointData.mul_matrixGroup]
      rw [mul_assoc]
  one_mul d := by
    apply CliffordSpinCandidatePointData.ext
    · simp
    · apply (V.specialOrthogonalMatrixPointEquivGroup A).injective
      change (1 * d).matrixGroup = d.matrixGroup
      simp
  mul_one d := by
    apply CliffordSpinCandidatePointData.ext
    · simp
    · apply (V.specialOrthogonalMatrixPointEquivGroup A).injective
      change (d * 1).matrixGroup = d.matrixGroup
      simp
  inv_mul_cancel d := by
    apply CliffordSpinCandidatePointData.ext
    · simp only [CliffordSpinCandidatePointData.mul_clifford,
        CliffordSpinCandidatePointData.inv_clifford,
        CliffordSpinCandidatePointData.one_clifford]
      exact V.cliffordCoordinateBaseChange_reverse_mul_eq_one_of_mul_reverse_eq_one
        A d.clifford d.mul_reverse_eq_one
    · apply (V.specialOrthogonalMatrixPointEquivGroup A).injective
      change (d⁻¹ * d).matrixGroup = (1 :
        V.CliffordSpinCandidatePointData A).matrixGroup
      simp

noncomputable instance cliffordSpinCandidateCoordinateAlgHomGroup :
    Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :=
  Equiv.group (V.cliffordSpinCandidateCoordinateAlgHomEquivPointData A)

def cliffordSpinCandidateCoordinateAlgHomMulEquivPointData :
    (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) ≃*
      V.CliffordSpinCandidatePointData A :=
  Equiv.mulEquiv (V.cliffordSpinCandidateCoordinateAlgHomEquivPointData A)

@[simp]
theorem cliffordSpinCandidateCoordinateAlgHomMulEquivPointData_apply
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A F =
      V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F := rfl

def cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup :
    (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) →*
      V.specialOrthogonalMatrixGroup A where
  toFun F :=
    (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F).matrixGroup
  map_one' := by
    change (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A 1).matrixGroup = 1
    rw [map_one]
    simp
  map_mul' F G := by
    change (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A
      (F * G)).matrixGroup = _
    rw [map_mul]
    simp

@[simp]
theorem cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup A F).1.1.1 =
      (V.cliffordSpinCandidateMatrixOfCoordinateAlgHom A F) := by
  ext i j
  simp [cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup,
    CliffordSpinCandidatePointData.matrixGroup_coe,
    cliffordSpinCandidateMatrixOfCoordinateAlgHom]

def cliffordSpinCandidateCoordinateAlgHomMap
    {B : Type*} [CommRing B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) →*
      (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] B) where
  toFun F := f.comp F
  map_one' := by
    apply (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData B).injective
    rw [map_one]
    change V.cliffordSpinCandidatePointDataOfCoordinateAlgHom B (f.comp 1) = 1
    apply CliffordSpinCandidatePointData.ext
    · apply (V.cliffordCoordinateBaseChangeBasis B).repr.injective
      ext u
      rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr,
        CliffordSpinCandidatePointData.one_clifford]
      simp only [AlgHom.comp_apply]
      have hA := congrArg
        (fun d : V.CliffordSpinCandidatePointData A =>
          (V.cliffordCoordinateBaseChangeBasis A).repr d.clifford u)
        (map_one (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A))
      change (V.cliffordCoordinateBaseChangeBasis A).repr
          (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A 1).clifford u =
        (V.cliffordCoordinateBaseChangeBasis A).repr
          (1 : V.CliffordSpinCandidatePointData A).clifford u at hA
      rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr]
        at hA
      rw [hA]
      rw [CliffordSpinCandidatePointData.one_clifford]
      calc
        f ((V.cliffordCoordinateBaseChangeBasis A).repr 1 u) =
            f (algebraMap ℚ A (V.cliffordCoordinateBasis.repr 1 u)) := by
          congr 1
          simpa [cliffordCoordinateBaseChangeOfRational] using
            V.cliffordCoordinateBaseChangeOfRational_repr A
              (1 : CliffordAlgebra V.quadraticForm) u
        _ = algebraMap ℚ B (V.cliffordCoordinateBasis.repr 1 u) :=
          f.commutes _
        _ = (V.cliffordCoordinateBaseChangeBasis B).repr 1 u := by
          symm
          simpa [cliffordCoordinateBaseChangeOfRational] using
            V.cliffordCoordinateBaseChangeOfRational_repr B
              (1 : CliffordAlgebra V.quadraticForm) u
    · apply Subtype.ext
      ext i j
      rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply,
        CliffordSpinCandidatePointData.one_matrixPoint]
      simp only [AlgHom.comp_apply]
      have hA := congrArg
        (fun d : V.CliffordSpinCandidatePointData A => d.matrixPoint.1 i j)
        (map_one (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A))
      change (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A 1).matrixPoint.1 i j =
        (1 : V.CliffordSpinCandidatePointData A).matrixPoint.1 i j at hA
      rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply]
        at hA
      rw [hA, CliffordSpinCandidatePointData.one_matrixPoint,
        V.cliffordSpinCandidateMatrixPointOne_apply,
        V.cliffordSpinCandidateMatrixPointOne_apply]
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
  map_mul' F G := by
    apply (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData B).injective
    rw [map_mul]
    change V.cliffordSpinCandidatePointDataOfCoordinateAlgHom B (f.comp (F * G)) =
      V.cliffordSpinCandidatePointDataOfCoordinateAlgHom B (f.comp F) *
        V.cliffordSpinCandidatePointDataOfCoordinateAlgHom B (f.comp G)
    apply CliffordSpinCandidatePointData.ext
    · apply (V.cliffordCoordinateBaseChangeBasis B).repr.injective
      ext u
      rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr,
        CliffordSpinCandidatePointData.mul_clifford]
      simp only [AlgHom.comp_apply]
      have hA := congrArg
        (fun d : V.CliffordSpinCandidatePointData A =>
          (V.cliffordCoordinateBaseChangeBasis A).repr d.clifford u)
        (map_mul (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A) F G)
      change (V.cliffordCoordinateBaseChangeBasis A).repr
          (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A (F * G)).clifford u =
        (V.cliffordCoordinateBaseChangeBasis A).repr
          (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F *
            V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A G).clifford u at hA
      rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr]
        at hA
      rw [hA, CliffordSpinCandidatePointData.mul_clifford,
        V.cliffordCoordinateBaseChangeBasis_repr_mul,
        V.cliffordCoordinateBaseChangeBasis_repr_mul, map_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t _
      simp only [map_mul, AlgHom.comp_apply,
        V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr]
      rw [f.commutes]
    · apply Subtype.ext
      ext i j
      rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply,
        CliffordSpinCandidatePointData.mul_matrixPoint]
      simp only [AlgHom.comp_apply]
      have hA := congrArg
        (fun d : V.CliffordSpinCandidatePointData A => d.matrixPoint.1 i j)
        (map_mul (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A) F G)
      change (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A (F * G)).matrixPoint.1 i j =
        (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F *
          V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A G).matrixPoint.1 i j at hA
      rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply]
        at hA
      rw [hA, CliffordSpinCandidatePointData.mul_matrixPoint,
        V.cliffordSpinCandidateMatrixPointMul_apply,
        V.cliffordSpinCandidateMatrixPointMul_apply, map_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [AlgHom.comp_apply,
        V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply,
        map_mul]

end RationalQuadraticSpaceMatrix
