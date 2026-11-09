import SMSFormula.RationalCliffordGeneralSpinIntrinsicPointMonoid

/-!
# Group structure on intrinsic general-Spin points

This file upgrades the carrier-specific intrinsic general-Spin monoid to a
group.  The inverse is the literal inverse Clifford unit, inverse similitude,
and inverse special-orthogonal action.  All identities are proved inside the
existing Clifford-coordinate algebra; no generic algebraic-group interface is
introduced.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

local notation "C" => V.cliffordCoordinateBaseChangeAlgebra A

namespace CliffordGeneralSpinIntrinsicPoint

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- The grade involution fixes the inverse of an even Clifford unit. -/
theorem involute_coe_inv
    (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.cliffordCoordinateBaseChangeInvolute A
        ((x.cliffordUnit⁻¹ : Cˣ) : C) =
      ((x.cliffordUnit⁻¹ : Cˣ) : C) := by
  have hu : Units.map
      (V.cliffordCoordinateBaseChangeInvolute A).toMonoidHom
        x.cliffordUnit = x.cliffordUnit := by
    apply Units.ext
    exact x.involute_eq
  have hinv := congrArg Inv.inv hu
  exact congrArg (fun z : Cˣ => (z : C)) hinv

/-- The reverse product also equals the scalar similitude. -/
theorem reverse_mul_eq
    (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C) *
        (x.cliffordUnit : C) =
      algebraMap A C x.similitude := by
  apply x.cliffordUnit.isUnit.mul_left_cancel
  calc
    (x.cliffordUnit : C) *
        (V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C) *
          (x.cliffordUnit : C)) =
      ((x.cliffordUnit : C) *
          V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C)) *
        (x.cliffordUnit : C) := by rw [mul_assoc]
    _ = algebraMap A C x.similitude * (x.cliffordUnit : C) := by
      rw [x.mul_reverse_eq]
    _ = (x.cliffordUnit : C) * algebraMap A C x.similitude := by
      exact Algebra.commutes _ _

/-- Reversion of the inverse Clifford unit is the original unit multiplied
by the inverse scalar similitude. -/
theorem reverse_coe_inv
    (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.cliffordCoordinateBaseChangeReverse A
        ((x.cliffordUnit⁻¹ : Cˣ) : C) =
      algebraMap A C (x.similitude⁻¹ : Aˣ) *
        (x.cliffordUnit : C) := by
  have hrevUnit : IsUnit
      (V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C)) := by
    have hrev :
        V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C) =
          algebraMap A C x.similitude *
            ((x.cliffordUnit⁻¹ : Cˣ) : C) := by
      apply x.cliffordUnit.isUnit.mul_right_cancel
      calc
        V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C) *
            (x.cliffordUnit : C) =
          algebraMap A C x.similitude := x.reverse_mul_eq
        _ = (algebraMap A C x.similitude *
              ((x.cliffordUnit⁻¹ : Cˣ) : C)) *
            (x.cliffordUnit : C) := by
          rw [mul_assoc]
          have hu : ((x.cliffordUnit⁻¹ : Cˣ) : C) *
              (x.cliffordUnit : C) = 1 := by
            exact congrArg Units.val (inv_mul_cancel x.cliffordUnit)
          rw [hu, mul_one]
    rw [hrev]
    exact
      (Units.isUnit (Units.map (algebraMap A C) x.similitude)).mul
        (x.cliffordUnit⁻¹).isUnit
  apply hrevUnit.mul_left_cancel
  calc
    V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C) *
        V.cliffordCoordinateBaseChangeReverse A
          ((x.cliffordUnit⁻¹ : Cˣ) : C) = 1 := by
      rw [← V.cliffordCoordinateBaseChangeReverse_mul]
      have hu : ((x.cliffordUnit⁻¹ : Cˣ) : C) *
          (x.cliffordUnit : C) = 1 := by
        exact congrArg Units.val (inv_mul_cancel x.cliffordUnit)
      rw [hu]
      change V.cliffordCoordinateBaseChangeReverse A
          ((1 : A) ⊗ₜ[ℚ] (1 : CliffordAlgebra V.quadraticForm)) = 1
      rw [V.cliffordCoordinateBaseChangeReverse_tmul]
      simp [Algebra.TensorProduct.one_def]
    _ = V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C) *
        (algebraMap A C (x.similitude⁻¹ : Aˣ) *
          (x.cliffordUnit : C)) := by
      calc
        1 = algebraMap A C (x.similitude⁻¹ : Aˣ) *
            algebraMap A C x.similitude := by
          rw [← map_mul]
          have hnu : ((x.similitude⁻¹ : Aˣ) : A) *
              (x.similitude : A) = 1 := by
            exact congrArg Units.val (inv_mul_cancel x.similitude)
          rw [hnu, map_one]
        _ = algebraMap A C (x.similitude⁻¹ : Aˣ) *
            (V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C) *
              (x.cliffordUnit : C)) := by rw [x.reverse_mul_eq]
        _ = V.cliffordCoordinateBaseChangeReverse A (x.cliffordUnit : C) *
            (algebraMap A C (x.similitude⁻¹ : Aˣ) *
              (x.cliffordUnit : C)) := by
          calc
            algebraMap A C (x.similitude⁻¹ : Aˣ) *
                (V.cliffordCoordinateBaseChangeReverse A
                    (x.cliffordUnit : C) * (x.cliffordUnit : C)) =
              (algebraMap A C (x.similitude⁻¹ : Aˣ) *
                  V.cliffordCoordinateBaseChangeReverse A
                    (x.cliffordUnit : C)) *
                (x.cliffordUnit : C) := by rw [mul_assoc]
            _ = (V.cliffordCoordinateBaseChangeReverse A
                    (x.cliffordUnit : C) *
                  algebraMap A C (x.similitude⁻¹ : Aˣ)) *
                (x.cliffordUnit : C) := by
              rw [Algebra.commutes ((x.similitude⁻¹ : Aˣ) : A)
                (V.cliffordCoordinateBaseChangeReverse A
                  (x.cliffordUnit : C))]
            _ = V.cliffordCoordinateBaseChangeReverse A
                  (x.cliffordUnit : C) *
                (algebraMap A C (x.similitude⁻¹ : Aˣ) *
                  (x.cliffordUnit : C)) := by rw [mul_assoc]

def matrixPointInv
    (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.specialOrthogonalMatrixPoint A :=
  V.specialOrthogonalMatrixPointOfGroup A x.matrixGroup⁻¹

@[simp]
theorem matrixPointInv_apply
    (x : V.CliffordGeneralSpinIntrinsicPoint A) (i j : Fin n) :
    (matrixPointInv V A x).1 i j = x.matrixGroup⁻¹.1.1.1 i j :=
  rfl

theorem matrix_mul_inv_apply
    (x : V.CliffordGeneralSpinIntrinsicPoint A) (i k : Fin n) :
    ∑ j, x.matrixPoint.1 i j * (matrixPointInv V A x).1 j k =
      (1 : Matrix (Fin n) (Fin n) A) i k := by
  rw [← Matrix.mul_apply]
  change (x.matrixPoint.1 * x.matrixGroup⁻¹.1.1.1) i k = _
  rw [← x.matrixGroup_coe, ← Matrix.GeneralLinearGroup.coe_mul]
  change ((x.matrixGroup * x.matrixGroup⁻¹).1.1.1) i k = _
  rw [mul_inv_cancel]
  rfl

/-- Inverse intrinsic general-Spin point. -/
def inv (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.CliffordGeneralSpinIntrinsicPoint A where
  cliffordUnit := x.cliffordUnit⁻¹
  similitude := x.similitude⁻¹
  matrixPoint := matrixPointInv V A x
  involute_eq := x.involute_coe_inv
  mul_reverse_eq := by
    rw [x.reverse_coe_inv]
    calc
      ((x.cliffordUnit⁻¹ : Cˣ) : C) *
          (algebraMap A C (x.similitude⁻¹ : Aˣ) *
            (x.cliffordUnit : C)) =
        algebraMap A C (x.similitude⁻¹ : Aˣ) *
          (((x.cliffordUnit⁻¹ : Cˣ) : C) *
            (x.cliffordUnit : C)) := by
          calc
            ((x.cliffordUnit⁻¹ : Cˣ) : C) *
                (algebraMap A C (x.similitude⁻¹ : Aˣ) *
                  (x.cliffordUnit : C)) =
              (((x.cliffordUnit⁻¹ : Cˣ) : C) *
                  algebraMap A C (x.similitude⁻¹ : Aˣ)) *
                (x.cliffordUnit : C) := by rw [mul_assoc]
            _ = (algebraMap A C (x.similitude⁻¹ : Aˣ) *
                  ((x.cliffordUnit⁻¹ : Cˣ) : C)) *
                (x.cliffordUnit : C) := by
              rw [Algebra.commutes ((x.similitude⁻¹ : Aˣ) : A)
                ((x.cliffordUnit⁻¹ : Cˣ) : C)]
            _ = algebraMap A C (x.similitude⁻¹ : Aˣ) *
                (((x.cliffordUnit⁻¹ : Cˣ) : C) *
                  (x.cliffordUnit : C)) := by rw [mul_assoc]
      _ = algebraMap A C (x.similitude⁻¹ : Aˣ) := by simp
  vectorGraph := by
    intro i
    change ((x.cliffordUnit⁻¹ : Cˣ) : C) *
        V.cliffordCoordinateBaseChangeVector A i *
          (x.cliffordUnit : C) = _
    apply x.cliffordUnit.isUnit.mul_left_cancel
    apply (x.cliffordUnit⁻¹).isUnit.mul_right_cancel
    calc
      (x.cliffordUnit : C) *
            (((x.cliffordUnit⁻¹ : Cˣ) : C) *
              V.cliffordCoordinateBaseChangeVector A i *
                (x.cliffordUnit : C)) *
          ((x.cliffordUnit⁻¹ : Cˣ) : C) =
        V.cliffordCoordinateBaseChangeVector A i := by
          have hu : (x.cliffordUnit : C) *
              ((x.cliffordUnit⁻¹ : Cˣ) : C) = 1 := by
            exact congrArg Units.val (mul_inv_cancel x.cliffordUnit)
          calc
            (x.cliffordUnit : C) *
                  (((x.cliffordUnit⁻¹ : Cˣ) : C) *
                    V.cliffordCoordinateBaseChangeVector A i *
                      (x.cliffordUnit : C)) *
                ((x.cliffordUnit⁻¹ : Cˣ) : C) =
              (((x.cliffordUnit : C) *
                    ((x.cliffordUnit⁻¹ : Cˣ) : C)) *
                  V.cliffordCoordinateBaseChangeVector A i) *
                ((x.cliffordUnit : C) *
                  ((x.cliffordUnit⁻¹ : Cˣ) : C)) := by
                noncomm_ring
            _ = V.cliffordCoordinateBaseChangeVector A i := by
              rw [hu, one_mul, mul_one]
      _ = ∑ k, (1 : Matrix (Fin n) (Fin n) A) k i •
          V.cliffordCoordinateBaseChangeVector A k := by
        simp [Matrix.one_apply]
      _ = ∑ k, (∑ j, x.matrixPoint.1 k j *
            (matrixPointInv V A x).1 j i) •
          V.cliffordCoordinateBaseChangeVector A k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [x.matrix_mul_inv_apply]
      _ = ∑ j, (matrixPointInv V A x).1 j i •
          (∑ k, x.matrixPoint.1 k j •
            V.cliffordCoordinateBaseChangeVector A k) := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_comm]
      _ = ∑ j, (matrixPointInv V A x).1 j i •
          ((x.cliffordUnit : C) *
            V.cliffordCoordinateBaseChangeVector A j *
              ((x.cliffordUnit⁻¹ : Cˣ) : C)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [x.vectorGraph]
      _ = (x.cliffordUnit : C) *
            (∑ j, (matrixPointInv V A x).1 j i •
              V.cliffordCoordinateBaseChangeVector A j) *
          ((x.cliffordUnit⁻¹ : Cˣ) : C) := by
        rw [V.cliffordCoordinateBaseChange_mul_sum_mul]

noncomputable instance : Inv (V.CliffordGeneralSpinIntrinsicPoint A) :=
  ⟨inv V A⟩

@[simp]
theorem inv_cliffordUnit (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    x⁻¹.cliffordUnit = x.cliffordUnit⁻¹ :=
  rfl

@[simp]
theorem inv_similitude (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    x⁻¹.similitude = x.similitude⁻¹ :=
  rfl

@[simp]
theorem inv_matrixGroup (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    x⁻¹.matrixGroup = x.matrixGroup⁻¹ := by
  exact (V.specialOrthogonalMatrixPointEquivGroup A).apply_symm_apply
    x.matrixGroup⁻¹

noncomputable instance : Group (V.CliffordGeneralSpinIntrinsicPoint A) where
  inv_mul_cancel x := by
    apply ext_cliffordUnit V A
    simp

/-- The similitude character as a genuine group homomorphism. -/
def similitudeGroupHom :
    V.CliffordGeneralSpinIntrinsicPoint A →* Aˣ :=
  similitudeMonoidHom V A

/-- Projection to the existing special-orthogonal group. -/
def toSpecialOrthogonalGroupHom :
    V.CliffordGeneralSpinIntrinsicPoint A →*
      V.specialOrthogonalMatrixGroup A :=
  toSpecialOrthogonalMonoidHom V A

/-- Group homomorphism for the central scalar inclusion. -/
def scalarGroupHom : Aˣ →* V.CliffordGeneralSpinIntrinsicPoint A :=
  scalarMonoidHom V A

@[simp]
theorem similitudeGroupHom_comp_scalarGroupHom (z : Aˣ) :
    similitudeGroupHom V A (scalarGroupHom V A z) = z ^ 2 :=
  rfl

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
