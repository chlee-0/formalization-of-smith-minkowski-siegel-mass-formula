import SMSFormula.RationalCliffordSpinCandidateIntrinsicPoint
import SMSFormula.RationalCliffordSpinCandidateScalarCentralizer

/-!
# Intrinsic general-Spin points for the Spin--SO crossed diagram

For a commutative rational algebra `A`, this file packages the carrier-specific
intrinsic `GSpin` points needed in Ono's crossed-diagram calculation.  A point
consists of an even Clifford unit, its scalar reverse norm, and the induced
determinant-one orthogonal action.  The definition is not a generic reductive
group or central-isogeny interface.

The two canonical families already needed by the comparison are constructed:

* the implemented intrinsic Spin candidate embeds with similitude one;
* a scalar unit `z` acts trivially on the vector module and has similitude
  `z ^ 2`.

The latter is the literal carrier-level identity `ν(i(z)) = z²` whose
character-lattice index supplies the final global factor two in the
specialized crossed integral.
-/

noncomputable section

open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local notation "C" => V.cliffordCoordinateBaseChangeAlgebra A

/-- Intrinsic general-Spin point data over a commutative rational algebra.
The stored matrix is the actual determinant-one orthogonal conjugation action;
the stored unit `similitude` is the scalar reverse norm. -/
@[ext]
structure CliffordGeneralSpinIntrinsicPoint where
  cliffordUnit : Cˣ
  similitude : Aˣ
  matrixPoint : V.specialOrthogonalMatrixPoint A
  involute_eq :
    V.cliffordCoordinateBaseChangeInvolute A
        (cliffordUnit : C) = cliffordUnit
  mul_reverse_eq :
    (cliffordUnit : C) *
        V.cliffordCoordinateBaseChangeReverse A (cliffordUnit : C) =
      algebraMap A C similitude
  vectorGraph : ∀ i,
    (cliffordUnit : C) * V.cliffordCoordinateBaseChangeVector A i *
        ((cliffordUnit⁻¹ : Cˣ) : C) =
      ∑ j, matrixPoint.1 j i • V.cliffordCoordinateBaseChangeVector A j

namespace CliffordGeneralSpinIntrinsicPoint

@[simp]
theorem coe_inv_spinCliffordUnit
    (x : V.CliffordSpinCandidatePointData A) :
    ((x.cliffordUnit⁻¹ :
        (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
      V.cliffordCoordinateBaseChangeAlgebra A) =
        V.cliffordCoordinateBaseChangeReverse A x.clifford :=
  V.cliffordCoordinateBaseChangeUnitOfMulReverseEqOne_inv_val A
    x.clifford x.mul_reverse_eq_one

/-- The carrier-specific general-Spin similitude character. -/
def similitudeHom :
    V.CliffordGeneralSpinIntrinsicPoint A → Aˣ :=
  fun x => x.similitude

/-- Projection to the represented special-orthogonal point. -/
def toSpecialOrthogonal :
    V.CliffordGeneralSpinIntrinsicPoint A →
      V.specialOrthogonalMatrixPoint A :=
  fun x => x.matrixPoint

/-- Embed an implemented intrinsic Spin point into general Spin. -/
def ofSpin
    (x : V.CliffordSpinCandidatePointData A) :
    V.CliffordGeneralSpinIntrinsicPoint A where
  cliffordUnit := x.cliffordUnit
  similitude := 1
  matrixPoint := x.matrixPoint
  involute_eq := x.involute_eq
  mul_reverse_eq := by
    rw [CliffordSpinCandidatePointData.coe_cliffordUnit]
    change x.clifford *
      V.cliffordCoordinateBaseChangeReverse A x.clifford = 1
    exact x.mul_reverse_eq_one
  vectorGraph := by
    intro i
    rw [CliffordSpinCandidatePointData.coe_cliffordUnit,
      coe_inv_spinCliffordUnit]
    exact x.vectorGraph i

@[simp]
theorem ofSpin_similitude
    (x : V.CliffordSpinCandidatePointData A) :
    (ofSpin V A x).similitude = 1 :=
  rfl

@[simp]
theorem ofSpin_matrixPoint
    (x : V.CliffordSpinCandidatePointData A) :
    (ofSpin V A x).matrixPoint = x.matrixPoint :=
  rfl

/-- The scalar Clifford unit associated with `z : Aˣ`. -/
def scalarCliffordUnit (z : Aˣ) : Cˣ :=
  Units.map (algebraMap A C) z

@[simp]
theorem coe_scalarCliffordUnit (z : Aˣ) :
    (scalarCliffordUnit V A z : C) = algebraMap A C z :=
  rfl

/-- The central scalar copy of `G_m` inside intrinsic general Spin. -/
def ofScalar (z : Aˣ) : V.CliffordGeneralSpinIntrinsicPoint A where
  cliffordUnit := scalarCliffordUnit V A z
  similitude := z ^ 2
  matrixPoint := V.cliffordSpinCandidateMatrixPointOne A
  involute_eq :=
    V.cliffordCoordinateBaseChangeInvolute_algebraMap A _
  mul_reverse_eq := by
    change algebraMap A C (z : A) *
        V.cliffordCoordinateBaseChangeReverse A (algebraMap A C (z : A)) =
      algebraMap A C ((z ^ 2 : Aˣ) : A)
    rw [V.cliffordCoordinateBaseChangeReverse_algebraMap, ← map_mul]
    congr 1
    simp [pow_two]
  vectorGraph := by
    intro i
    change algebraMap A C (z : A) *
        V.cliffordCoordinateBaseChangeVector A i *
          algebraMap A C ((z⁻¹ : Aˣ) : A) = _
    calc
      algebraMap A C (z : A) *
            V.cliffordCoordinateBaseChangeVector A i *
          algebraMap A C ((z⁻¹ : Aˣ) : A) =
        algebraMap A C ((z : A) * (z⁻¹ : Aˣ)) *
          V.cliffordCoordinateBaseChangeVector A i := by
            rw [mul_assoc, ← Algebra.commutes ((z⁻¹ : Aˣ) : A)
              (V.cliffordCoordinateBaseChangeVector A i),
              ← mul_assoc, ← map_mul]
      _ = V.cliffordCoordinateBaseChangeVector A i := by
            have hz : (z : A) * (z⁻¹ : Aˣ) = 1 := by
              exact congrArg Units.val (mul_inv_cancel z)
            rw [hz, map_one, one_mul]
      _ = ∑ j, (V.cliffordSpinCandidateMatrixPointOne A).1 j i •
            V.cliffordCoordinateBaseChangeVector A j := by
              simp [Matrix.one_apply]

@[simp]
theorem ofScalar_matrixPoint (z : Aˣ) :
    (ofScalar V A z).matrixPoint =
      V.cliffordSpinCandidateMatrixPointOne A :=
  rfl

/-- The crossed-diagram scalar map has literal similitude `z²`. -/
@[simp]
theorem ofScalar_similitude (z : Aˣ) :
    (ofScalar V A z).similitude = z ^ 2 :=
  rfl

/-- Carrier-level form of `ν(i(z)) = z²`. -/
theorem similitudeHom_ofScalar (z : Aˣ) :
    similitudeHom V A (ofScalar V A z) = z ^ 2 :=
  rfl

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
