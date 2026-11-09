import SMSFormula.RationalCliffordGeneralSpinIntrinsicPointGroup

/-!
# Vertical exactness for the intrinsic Spin--general-Spin diagram

This file proves the carrier-specific point exactness used by the crossed
Spin--general-Spin comparison.  The existing intrinsic Spin point group maps
into intrinsic general Spin, and its image is exactly the kernel of the
literal similitude character.  No generic exact-sequence or algebraic-group
interface is introduced.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

local notation "C" => V.cliffordCoordinateBaseChangeAlgebra A

namespace CliffordGeneralSpinIntrinsicPoint

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- Reversion is the inverse Clifford unit multiplied by the scalar
similitude. -/
theorem reverse_eq_similitude_mul_coe_inv
    (x : V.CliffordGeneralSpinIntrinsicPoint A) :
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

/-- The existing intrinsic Spin point group embeds in intrinsic general
Spin. -/
def ofSpinGroupHom :
    V.CliffordSpinCandidatePointData A →*
      V.CliffordGeneralSpinIntrinsicPoint A where
  toFun := ofSpin V A
  map_one' := by
    apply ext_cliffordUnit V A
    apply Units.ext
    rfl
  map_mul' := ofSpin_mul V A

@[simp]
theorem ofSpinGroupHom_apply
    (x : V.CliffordSpinCandidatePointData A) :
    ofSpinGroupHom V A x = ofSpin V A x :=
  rfl

/-- A general-Spin point of similitude one gives a literal point of the
implemented intrinsic Spin carrier. -/
def toSpinOfSimilitudeOne
    (x : V.CliffordGeneralSpinIntrinsicPoint A)
    (hnu : x.similitude = 1) :
    V.CliffordSpinCandidatePointData A where
  clifford := x.cliffordUnit
  matrixPoint := x.matrixPoint
  involute_eq := x.involute_eq
  mul_reverse_eq_one := by
    rw [x.mul_reverse_eq, hnu]
    change algebraMap A C (1 : A) = 1
    exact map_one _
  vectorGraph := by
    intro i
    rw [x.reverse_eq_similitude_mul_coe_inv, hnu]
    simp only [Units.val_one, map_one, one_mul]
    exact x.vectorGraph i

@[simp]
theorem toSpinOfSimilitudeOne_clifford
    (x : V.CliffordGeneralSpinIntrinsicPoint A)
    (hnu : x.similitude = 1) :
    (toSpinOfSimilitudeOne V A x hnu).clifford = x.cliffordUnit :=
  rfl

@[simp]
theorem ofSpin_toSpinOfSimilitudeOne
    (x : V.CliffordGeneralSpinIntrinsicPoint A)
    (hnu : x.similitude = 1) :
    ofSpin V A (toSpinOfSimilitudeOne V A x hnu) = x := by
  apply ext_cliffordUnit V A
  apply Units.ext
  rfl

/-- Carrier-specific vertical exactness:

`Spin(A) → GSpin(A) → Aˣ`

is exact at `GSpin(A)` for every commutative rational algebra `A`. -/
theorem range_ofSpinGroupHom_eq_ker_similitudeGroupHom :
    (ofSpinGroupHom V A).range = (similitudeGroupHom V A).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [ofSpinGroupHom, similitudeGroupHom, similitudeMonoidHom]
  · intro hx
    have hnu : x.similitude = 1 := by
      simpa [similitudeGroupHom, similitudeMonoidHom] using hx
    exact ⟨toSpinOfSimilitudeOne V A x hnu,
      ofSpin_toSpinOfSimilitudeOne V A x hnu⟩

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
