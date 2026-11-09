import SMSFormula.RationalCliffordGeneralSpinVerticalExactness

/-!
# Horizontal exactness for the intrinsic general-Spin diagram

The scalar units inside intrinsic general Spin are exactly the kernel of its
action on the special-orthogonal carrier.  The proof uses the existing
arbitrary-algebra even Clifford centralizer theorem twice: once for a kernel
point and once for its inverse, which proves that the resulting scalar is a
unit over an arbitrary commutative rational algebra.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

local notation "C" => V.cliffordCoordinateBaseChangeAlgebra A

namespace CliffordGeneralSpinIntrinsicPoint

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- A general-Spin point acting trivially on the vector module commutes with
every standard Clifford vector. -/
theorem commute_vector_of_matrixGroup_eq_one
    (x : V.CliffordGeneralSpinIntrinsicPoint A)
    (hx : x.matrixGroup = 1) (i : Fin n) :
    V.cliffordCoordinateBaseChangeVector A i * (x.cliffordUnit : C) =
      (x.cliffordUnit : C) *
        V.cliffordCoordinateBaseChangeVector A i := by
  have hmatrix : x.matrixPoint.1 = 1 := by
    rw [← x.matrixGroup_coe, hx]
    rfl
  have hgraph :
      (x.cliffordUnit : C) *
          V.cliffordCoordinateBaseChangeVector A i *
            ((x.cliffordUnit⁻¹ : Cˣ) : C) =
        V.cliffordCoordinateBaseChangeVector A i := by
    rw [x.vectorGraph, hmatrix]
    simp [Matrix.one_apply]
  have hinv_mul : ((x.cliffordUnit⁻¹ : Cˣ) : C) *
      (x.cliffordUnit : C) = 1 := by
    exact congrArg Units.val (inv_mul_cancel x.cliffordUnit)
  calc
    V.cliffordCoordinateBaseChangeVector A i * (x.cliffordUnit : C) =
        ((x.cliffordUnit : C) *
            V.cliffordCoordinateBaseChangeVector A i *
              ((x.cliffordUnit⁻¹ : Cˣ) : C)) *
          (x.cliffordUnit : C) := by rw [hgraph]
    _ = (x.cliffordUnit : C) *
          V.cliffordCoordinateBaseChangeVector A i *
            (((x.cliffordUnit⁻¹ : Cˣ) : C) *
              (x.cliffordUnit : C)) := by simp only [mul_assoc]
    _ = (x.cliffordUnit : C) *
          V.cliffordCoordinateBaseChangeVector A i := by
      rw [hinv_mul, mul_one]

/-- A point in the kernel of the general-Spin action is a unique scalar
Clifford unit.  Existence as a unit is proved internally from the scalar
descriptions of the point and its inverse. -/
theorem exists_scalar_eq_of_matrixGroup_eq_one
    (x : V.CliffordGeneralSpinIntrinsicPoint A)
    (hx : x.matrixGroup = 1) :
    ∃ z : Aˣ, ofScalar V A z = x := by
  obtain ⟨r, hr⟩ :=
    V.exists_eq_algebraMap_of_baseChangeInvolute_eq_of_commute_vectors A
      (x.cliffordUnit : C) x.involute_eq
      (commute_vector_of_matrixGroup_eq_one V A x hx)
  have hxinv : x⁻¹.matrixGroup = 1 := by simp [hx]
  obtain ⟨s, hs⟩ :=
    V.exists_eq_algebraMap_of_baseChangeInvolute_eq_of_commute_vectors A
      (x⁻¹.cliffordUnit : C) x⁻¹.involute_eq
      (commute_vector_of_matrixGroup_eq_one V A x⁻¹ hxinv)
  have hs' : ((x.cliffordUnit⁻¹ : Cˣ) : C) = algebraMap A C s := by
    simpa using hs
  have hrs : r * s = 1 := by
    apply V.cliffordCoordinateBaseChange_algebraMap_injective A
    rw [map_mul, map_one, ← hr, ← hs']
    exact congrArg Units.val (mul_inv_cancel x.cliffordUnit)
  let z : Aˣ :=
    { val := r
      inv := s
      val_inv := hrs
      inv_val := by simpa [mul_comm] using hrs }
  refine ⟨z, ?_⟩
  apply ext_cliffordUnit V A
  apply Units.ext
  change algebraMap A C r = (x.cliffordUnit : C)
  exact hr.symm

@[simp]
theorem ofScalar_matrixGroup (z : Aˣ) :
    (ofScalar V A z).matrixGroup = 1 := by
  exact (V.specialOrthogonalMatrixPointEquivGroup A).apply_symm_apply 1

/-- Carrier-specific horizontal exactness:

`Aˣ → GSpin(A) → SO(A)`

is exact at `GSpin(A)` for every commutative rational algebra `A`. -/
theorem range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom :
    (scalarGroupHom V A).range =
      (toSpecialOrthogonalGroupHom V A).ker := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change (ofScalar V A z).matrixGroup = 1
    exact ofScalar_matrixGroup V A z
  · intro hx
    have hmatrix : x.matrixGroup = 1 := by
      simpa [toSpecialOrthogonalGroupHom,
        toSpecialOrthogonalMonoidHom] using hx
    obtain ⟨z, hz⟩ := exists_scalar_eq_of_matrixGroup_eq_one V A x hmatrix
    exact ⟨z, hz⟩

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
