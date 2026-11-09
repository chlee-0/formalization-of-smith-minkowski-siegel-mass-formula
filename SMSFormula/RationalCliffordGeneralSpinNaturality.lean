import SMSFormula.RationalCliffordGeneralSpinSpinorNorm
import SMSFormula.RationalCliffordSpinCandidateIntrinsicPointNaturality

/-!
# Naturality of intrinsic general-Spin points

Intrinsic general-Spin points map coefficientwise along every homomorphism of
commutative rational algebras.  The Clifford unit, similitude, and represented
special-orthogonal action are transported by the already established scalar-
extension maps.  This is the functoriality needed to compare rational, real,
and p-adic points in the carrier-specific crossed integral.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable {A B C : Type*}
variable [CommRing A] [Algebra ℚ A]
variable [CommRing B] [Algebra ℚ B]
variable [CommRing C] [Algebra ℚ C]

namespace CliffordGeneralSpinIntrinsicPoint

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- Scalar extension carries scalar Clifford elements to scalar Clifford
elements. -/
@[simp]
theorem cliffordCoordinateBaseChangeMap_algebraMap
    (f : A →ₐ[ℚ] B) (a : A) :
    V.cliffordCoordinateBaseChangeMap f
        (algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) a) =
      algebraMap B (V.cliffordCoordinateBaseChangeAlgebra B) (f a) := by
  rw [Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.algebraMap_apply,
    V.cliffordCoordinateBaseChangeMap_tmul]
  simp

/-- Coefficientwise scalar extension of an intrinsic general-Spin point. -/
def map (f : A →ₐ[ℚ] B)
    (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.CliffordGeneralSpinIntrinsicPoint B where
  cliffordUnit := Units.map
    (V.cliffordCoordinateBaseChangeMap f).toMonoidHom x.cliffordUnit
  similitude := Units.map f.toMonoidHom x.similitude
  matrixPoint := V.specialOrthogonalMatrixPointMap f x.matrixPoint
  involute_eq := by
    change V.cliffordCoordinateBaseChangeInvolute B
        (V.cliffordCoordinateBaseChangeMap f (x.cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra A)) =
      V.cliffordCoordinateBaseChangeMap f (x.cliffordUnit :
        V.cliffordCoordinateBaseChangeAlgebra A)
    rw [← V.cliffordCoordinateBaseChangeMap_involute, x.involute_eq]
  mul_reverse_eq := by
    change V.cliffordCoordinateBaseChangeMap f (x.cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra A) *
        V.cliffordCoordinateBaseChangeReverse B
          (V.cliffordCoordinateBaseChangeMap f (x.cliffordUnit :
            V.cliffordCoordinateBaseChangeAlgebra A)) =
      algebraMap B (V.cliffordCoordinateBaseChangeAlgebra B)
        (f (x.similitude : A))
    rw [← V.cliffordCoordinateBaseChangeMap_reverse,
      ← map_mul, x.mul_reverse_eq,
      cliffordCoordinateBaseChangeMap_algebraMap]
  vectorGraph := by
    intro i
    change V.cliffordCoordinateBaseChangeMap f (x.cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra A) *
          V.cliffordCoordinateBaseChangeVector B i *
            V.cliffordCoordinateBaseChangeMap f
              ((x.cliffordUnit⁻¹ :
                (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
                  V.cliffordCoordinateBaseChangeAlgebra A) = _
    calc
      V.cliffordCoordinateBaseChangeMap f (x.cliffordUnit :
            V.cliffordCoordinateBaseChangeAlgebra A) *
          V.cliffordCoordinateBaseChangeVector B i *
            V.cliffordCoordinateBaseChangeMap f
              (((x.cliffordUnit⁻¹ :
                (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
                  V.cliffordCoordinateBaseChangeAlgebra A)) =
        V.cliffordCoordinateBaseChangeMap f
          ((x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) *
            V.cliffordCoordinateBaseChangeVector A i *
              ((x.cliffordUnit⁻¹ :
                (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
                  V.cliffordCoordinateBaseChangeAlgebra A)) := by
            rw [map_mul, map_mul,
              V.cliffordCoordinateBaseChangeMap_vector]
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

@[simp]
theorem map_cliffordUnit_coe
    (f : A →ₐ[ℚ] B) (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    ((map V f x).cliffordUnit :
      V.cliffordCoordinateBaseChangeAlgebra B) =
        V.cliffordCoordinateBaseChangeMap f (x.cliffordUnit :
          V.cliffordCoordinateBaseChangeAlgebra A) :=
  rfl

@[simp]
theorem map_similitude
    (f : A →ₐ[ℚ] B) (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    (map V f x).similitude = Units.map f.toMonoidHom x.similitude :=
  rfl

@[simp]
theorem map_matrixPoint
    (f : A →ₐ[ℚ] B) (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    (map V f x).matrixPoint =
      V.specialOrthogonalMatrixPointMap f x.matrixPoint :=
  rfl

/-- Scalar extension as a group homomorphism. -/
def mapGroupHom (f : A →ₐ[ℚ] B) :
    V.CliffordGeneralSpinIntrinsicPoint A →*
      V.CliffordGeneralSpinIntrinsicPoint B where
  toFun := map V f
  map_one' := by
    apply ext_cliffordUnit V B
    apply Units.ext
    change V.cliffordCoordinateBaseChangeMap f 1 = 1
    exact map_one _
  map_mul' x y := by
    apply ext_cliffordUnit V B
    apply Units.ext
    change V.cliffordCoordinateBaseChangeMap f
        ((x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) *
          (y.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A)) =
      V.cliffordCoordinateBaseChangeMap f
          (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) *
        V.cliffordCoordinateBaseChangeMap f
          (y.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A)
    exact map_mul _ _ _

@[simp]
theorem mapGroupHom_apply
    (f : A →ₐ[ℚ] B) (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    mapGroupHom V f x = map V f x :=
  rfl

@[simp]
theorem map_id (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    map V (AlgHom.id ℚ A) x = x := by
  apply ext_cliffordUnit V A
  apply Units.ext
  exact V.cliffordCoordinateBaseChangeMap_id_apply
    (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A)

@[simp]
theorem map_comp (f : A →ₐ[ℚ] B) (g : B →ₐ[ℚ] C)
    (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    map V g (map V f x) = map V (g.comp f) x := by
  apply ext_cliffordUnit V C
  apply Units.ext
  exact V.cliffordCoordinateBaseChangeMap_comp_apply f g
    (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A)

/-- Similitude is natural under scalar extension. -/
theorem similitude_naturality (f : A →ₐ[ℚ] B) :
    (Units.map f.toMonoidHom).comp (similitudeGroupHom V A) =
      (similitudeGroupHom V B).comp (mapGroupHom V f) := by
  rfl

/-- The orthogonal action is natural under scalar extension. -/
theorem toSpecialOrthogonal_naturality (f : A →ₐ[ℚ] B) :
    (V.specialOrthogonalMatrixGroupMap f).comp
        (toSpecialOrthogonalGroupHom V A) =
      (toSpecialOrthogonalGroupHom V B).comp (mapGroupHom V f) := by
  apply MonoidHom.ext
  intro x
  exact ((V.specialOrthogonalMatrixPointEquivGroup B).apply_symm_apply
    (V.specialOrthogonalMatrixGroupMap f x.matrixGroup)).symm

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
