import SMSFormula.RationalCliffordGeneralSpinIntrinsicPoint

/-!
# Multiplication on intrinsic general-Spin points

This file proves that the carrier-specific intrinsic general-Spin points are
closed under Clifford multiplication.  It packages the similitude character
and the projection to the existing special-orthogonal matrix group as monoid
homomorphisms.  The embedded intrinsic Spin points and central scalar points
are multiplicative, and the scalar similitude remains the square map.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

local notation "C" => V.cliffordCoordinateBaseChangeAlgebra A

namespace CliffordGeneralSpinIntrinsicPoint

def matrixGroup (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.specialOrthogonalMatrixGroup A :=
  V.specialOrthogonalMatrixPointToGroup A x.matrixPoint

@[simp]
theorem matrixGroup_coe (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    x.matrixGroup.1.1.1 = x.matrixPoint.1 := by
  ext i j
  simp [matrixGroup, specialOrthogonalMatrixPointToGroup]

/-- The Clifford unit uniquely determines the stored orthogonal action. -/
theorem matrixPoint_eq_of_cliffordUnit_eq
    (x y : V.CliffordGeneralSpinIntrinsicPoint A)
    (h : x.cliffordUnit = y.cliffordUnit) :
    x.matrixPoint = y.matrixPoint := by
  apply Subtype.ext
  ext j i
  have hgraph :
      (∑ k, x.matrixPoint.1 k i •
          V.cliffordCoordinateBaseChangeVector A k) =
        ∑ k, y.matrixPoint.1 k i •
          V.cliffordCoordinateBaseChangeVector A k := by
    rw [← x.vectorGraph i, ← y.vectorGraph i, h]
  have hcoords :
      V.cliffordCoordinateBaseChangeVectorOfCoordinates A
          (fun k => x.matrixPoint.1 k i) =
        V.cliffordCoordinateBaseChangeVectorOfCoordinates A
          (fun k => y.matrixPoint.1 k i) := by
    simpa [cliffordCoordinateBaseChangeVectorOfCoordinates] using hgraph
  exact congrFun
    (V.cliffordCoordinateBaseChangeVectorOfCoordinates_injective A hcoords) j

/-- Extensionality by the intrinsic Clifford unit alone.  The reverse norm
then determines the similitude, while conjugation determines the matrix. -/
theorem ext_cliffordUnit
    (x y : V.CliffordGeneralSpinIntrinsicPoint A)
    (h : x.cliffordUnit = y.cliffordUnit) : x = y := by
  apply CliffordGeneralSpinIntrinsicPoint.ext
  · exact h
  · apply Units.ext
    apply V.cliffordCoordinateBaseChange_algebraMap_injective A
    rw [← x.mul_reverse_eq, ← y.mul_reverse_eq, h]
  · exact matrixPoint_eq_of_cliffordUnit_eq V A x y h

def matrixPointMul
    (x y : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.specialOrthogonalMatrixPoint A :=
  V.specialOrthogonalMatrixPointOfGroup A (x.matrixGroup * y.matrixGroup)

@[simp]
theorem matrixPointMul_apply
    (x y : V.CliffordGeneralSpinIntrinsicPoint A) (i j : Fin n) :
    (matrixPointMul V A x y).1 i j =
      ∑ k, x.matrixPoint.1 i k * y.matrixPoint.1 k j := by
  change (x.matrixGroup * y.matrixGroup).1.1.1 i j = _
  rw [← x.matrixGroup_coe, ← y.matrixGroup_coe, ← Matrix.mul_apply]
  rfl

/-- Identity intrinsic general-Spin point. -/
def one : V.CliffordGeneralSpinIntrinsicPoint A :=
  ofScalar V A 1

/-- Clifford multiplication of intrinsic general-Spin points. -/
def mul
    (x y : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.CliffordGeneralSpinIntrinsicPoint A where
  cliffordUnit := x.cliffordUnit * y.cliffordUnit
  similitude := x.similitude * y.similitude
  matrixPoint := matrixPointMul V A x y
  involute_eq := by
    simp only [Units.val_mul]
    rw [map_mul, x.involute_eq, y.involute_eq]
  mul_reverse_eq := by
    change ((x.cliffordUnit : C) * (y.cliffordUnit : C)) *
        V.cliffordCoordinateBaseChangeReverse A
          ((x.cliffordUnit : C) * (y.cliffordUnit : C)) = _
    rw [V.cliffordCoordinateBaseChangeReverse_mul]
    calc
      ((x.cliffordUnit : C) * (y.cliffordUnit : C)) *
            (V.cliffordCoordinateBaseChangeReverse A (y.cliffordUnit : C) *
              V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C)) =
          (x.cliffordUnit : C) *
            ((y.cliffordUnit : C) *
              V.cliffordCoordinateBaseChangeReverse A (y.cliffordUnit : C)) *
            V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C) := by
              simp only [mul_assoc]
      _ = (x.cliffordUnit : C) * algebraMap A C y.similitude *
            V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C) := by
              rw [y.mul_reverse_eq]
      _ = algebraMap A C y.similitude *
            ((x.cliffordUnit : C) *
              V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C)) := by
              rw [← Algebra.commutes (y.similitude : A) (x.cliffordUnit : C)]
              simp only [mul_assoc]
      _ = algebraMap A C y.similitude * algebraMap A C x.similitude := by
              rw [x.mul_reverse_eq]
      _ = algebraMap A C (x.similitude * y.similitude) := by
              rw [← map_mul]
              congr 1
              exact mul_comm _ _
  vectorGraph := by
    intro i
    change ((x.cliffordUnit : C) * (y.cliffordUnit : C)) *
        V.cliffordCoordinateBaseChangeVector A i *
          (((y.cliffordUnit⁻¹ : Cˣ) : C) *
            ((x.cliffordUnit⁻¹ : Cˣ) : C)) = _
    calc
      ((x.cliffordUnit : C) * (y.cliffordUnit : C)) *
            V.cliffordCoordinateBaseChangeVector A i *
          (((y.cliffordUnit⁻¹ : Cˣ) : C) *
            ((x.cliffordUnit⁻¹ : Cˣ) : C)) =
        (x.cliffordUnit : C) *
            ((y.cliffordUnit : C) *
              V.cliffordCoordinateBaseChangeVector A i *
                ((y.cliffordUnit⁻¹ : Cˣ) : C)) *
          ((x.cliffordUnit⁻¹ : Cˣ) : C) := by
            simp only [mul_assoc]
      _ = (x.cliffordUnit : C) *
            (∑ j, y.matrixPoint.1 j i •
              V.cliffordCoordinateBaseChangeVector A j) *
          ((x.cliffordUnit⁻¹ : Cˣ) : C) := by
            rw [y.vectorGraph]
      _ = ∑ j, y.matrixPoint.1 j i •
          ((x.cliffordUnit : C) *
            V.cliffordCoordinateBaseChangeVector A j *
              ((x.cliffordUnit⁻¹ : Cˣ) : C)) :=
        V.cliffordCoordinateBaseChange_mul_sum_mul A _ _ _
      _ = ∑ j, y.matrixPoint.1 j i •
          (∑ k, x.matrixPoint.1 k j •
            V.cliffordCoordinateBaseChangeVector A k) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [x.vectorGraph]
      _ = ∑ k, (∑ j, x.matrixPoint.1 k j * y.matrixPoint.1 j i) •
          V.cliffordCoordinateBaseChangeVector A k := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_comm]
      _ = ∑ k, (matrixPointMul V A x y).1 k i •
          V.cliffordCoordinateBaseChangeVector A k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [matrixPointMul_apply]

noncomputable instance : One (V.CliffordGeneralSpinIntrinsicPoint A) :=
  ⟨one V A⟩

noncomputable instance : Mul (V.CliffordGeneralSpinIntrinsicPoint A) :=
  ⟨mul V A⟩

@[simp]
theorem one_cliffordUnit :
    (1 : V.CliffordGeneralSpinIntrinsicPoint A).cliffordUnit = 1 := by
  apply Units.ext
  rfl

@[simp]
theorem mul_cliffordUnit
    (x y : V.CliffordGeneralSpinIntrinsicPoint A) :
    (x * y).cliffordUnit = x.cliffordUnit * y.cliffordUnit :=
  rfl

@[simp]
theorem one_similitude :
    (1 : V.CliffordGeneralSpinIntrinsicPoint A).similitude = 1 := by
  change (1 : Aˣ) ^ 2 = 1
  exact one_pow 2

@[simp]
theorem mul_similitude
    (x y : V.CliffordGeneralSpinIntrinsicPoint A) :
    (x * y).similitude = x.similitude * y.similitude :=
  rfl

@[simp]
theorem one_matrixGroup :
    (1 : V.CliffordGeneralSpinIntrinsicPoint A).matrixGroup = 1 := by
  exact (V.specialOrthogonalMatrixPointEquivGroup A).apply_symm_apply 1

@[simp]
theorem mul_matrixGroup
    (x y : V.CliffordGeneralSpinIntrinsicPoint A) :
    (x * y).matrixGroup = x.matrixGroup * y.matrixGroup := by
  exact (V.specialOrthogonalMatrixPointEquivGroup A).apply_symm_apply
    (x.matrixGroup * y.matrixGroup)

noncomputable instance : Monoid (V.CliffordGeneralSpinIntrinsicPoint A) where
  mul_assoc x y z := by
    apply ext_cliffordUnit V A
    simp only [mul_cliffordUnit]
    rw [mul_assoc]
  one_mul x := by
    apply ext_cliffordUnit V A
    simp
  mul_one x := by
    apply ext_cliffordUnit V A
    simp

/-- The intrinsic general-Spin similitude character. -/
def similitudeMonoidHom :
    V.CliffordGeneralSpinIntrinsicPoint A →* Aˣ where
  toFun := fun x => x.similitude
  map_one' := one_similitude V A
  map_mul' := mul_similitude V A

/-- Projection from intrinsic general Spin to the existing `SO` matrix
group. -/
def toSpecialOrthogonalMonoidHom :
    V.CliffordGeneralSpinIntrinsicPoint A →*
      V.specialOrthogonalMatrixGroup A where
  toFun := matrixGroup V A
  map_one' := one_matrixGroup V A
  map_mul' := mul_matrixGroup V A

/-- The embedded intrinsic Spin carrier is multiplicative. -/
theorem ofSpin_mul
    (x y : V.CliffordSpinCandidatePointData A) :
    ofSpin V A (x * y) = ofSpin V A x * ofSpin V A y := by
  apply ext_cliffordUnit V A
  apply Units.ext
  rfl

/-- The central scalar copy of `G_m` is multiplicative. -/
theorem ofScalar_mul (z w : Aˣ) :
    ofScalar V A (z * w) = ofScalar V A z * ofScalar V A w := by
  apply ext_cliffordUnit V A
  apply Units.ext
  change algebraMap A C ((z * w : Aˣ) : A) =
    algebraMap A C (z : A) * algebraMap A C (w : A)
  exact map_mul (algebraMap A C) (z : A) (w : A)

/-- Monoid homomorphism for the central scalar inclusion. -/
def scalarMonoidHom : Aˣ →* V.CliffordGeneralSpinIntrinsicPoint A where
  toFun := ofScalar V A
  map_one' := by
    apply ext_cliffordUnit V A
    apply Units.ext
    rfl
  map_mul' := ofScalar_mul V A

@[simp]
theorem similitudeMonoidHom_comp_scalarMonoidHom (z : Aˣ) :
    similitudeMonoidHom V A (scalarMonoidHom V A z) = z ^ 2 :=
  rfl

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
