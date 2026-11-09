import SMSFormula.RationalQuadraticIsometryGeneralSpinTransport
import SMSFormula.RationalCliffordGeneralSpinIntrinsicPointGroup

/-!
# Intrinsic general-Spin equivalence across anisotropic presentations

This file constructs the inverse of the point transport induced by a supplied
anisotropic-complement presentation and packages the two maps as a
multiplicative equivalence.  Everything is proved on the native coordinate
carriers over an arbitrary commutative rational algebra.

No topology, Haar measure, quotient, shell measure, orbit kernel, or cutoff is
transported here.
-/

noncomputable section

open scoped Matrix TensorProduct

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The inverse presentation Clifford equivalence carries arbitrary ambient
vectors through the inverse scalar-extended quadratic isometry. -/
theorem blockToAmbientCliffordBaseChangeAlgEquiv_symm_vectorOfCoordinates
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (v : Fin n → A) :
    (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).symm
        (V.cliffordCoordinateBaseChangeVectorOfCoordinates A v) =
      (P.blockSpace hx).cliffordCoordinateBaseChangeVectorOfCoordinates A
        ((P.blockToAmbientBaseChangeIsometryEquiv hx A).symm v) := by
  apply (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).injective
  rw [AlgEquiv.apply_symm_apply,
    P.blockToAmbientCliffordBaseChangeAlgEquiv_vectorOfCoordinates A hx]
  exact congrArg (V.cliffordCoordinateBaseChangeVectorOfCoordinates A)
    (P.blockToAmbientBaseChangeIsometryEquiv hx A |>.apply_symm_apply v).symm

/-- Conjugate an ambient special-orthogonal point back through the supplied
block-to-ambient quadratic isometry. -/
def ambientToBlockConjugateIsometryEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.specialOrthogonalMatrixPoint A) :
    ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm A).IsometryEquiv
      ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm A) :=
  let e := P.blockToAmbientBaseChangeIsometryEquiv hx A
  (e.trans (V.specialOrthogonalMatrixPointIsometryEquiv A g)).trans e.symm

/-- Reverse conjugation preserves determinant one over every commutative
rational algebra. -/
theorem ambientToBlockConjugateIsometryEquiv_det
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.specialOrthogonalMatrixPoint A) :
    LinearMap.det
        (P.ambientToBlockConjugateIsometryEquiv A hx g).toLinearEquiv.toLinearMap = 1 := by
  let e := P.blockToAmbientBaseChangeIsometryEquiv hx A
  let h := V.specialOrthogonalMatrixPointIsometryEquiv A g
  have hhdet : LinearEquiv.det h.toLinearEquiv = 1 := by
    apply Units.ext
    simp only [LinearEquiv.coe_det, Units.val_one]
    rw [← LinearMap.det_toMatrix',
      V.specialOrthogonalMatrixPointIsometryEquiv_toMatrix' A g]
    exact g.2.2
  have hconj := LinearEquiv.det_conj h.toLinearEquiv e.symm.toLinearEquiv
  change LinearMap.det
      ((e.trans h).trans e.symm).toLinearEquiv.toLinearMap = 1
  rw [← LinearEquiv.coe_det]
  exact congrArg Units.val (hconj.trans hhdet)

/-- The block special-orthogonal matrix point obtained by reverse
conjugation. -/
def ambientToBlockSpecialOrthogonalMatrixPoint
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.specialOrthogonalMatrixPoint A) :
    (P.blockSpace hx).specialOrthogonalMatrixPoint A := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  let h := P.ambientToBlockConjugateIsometryEquiv A hx g
  refine ⟨LinearMap.toMatrix' h.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · have hcomp :
        ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm A).comp
            h.toLinearEquiv.toLinearMap =
          (P.blockSpace hx).commutativeScalarExtensionQuadraticForm A := by
      apply QuadraticMap.ext
      intro y
      exact h.map_app y
    have hmatrix := congrArg QuadraticForm.toMatrix' hcomp
    rw [QuadraticForm.toMatrix'_comp,
      (P.blockSpace hx).commutativeScalarExtensionQuadraticForm_toMatrix' A] at hmatrix
    simpa [commutativeScalarExtensionFormMatrix,
      specialOrthogonalMappedFormMatrix] using hmatrix
  · rw [LinearMap.det_toMatrix']
    exact P.ambientToBlockConjugateIsometryEquiv_det A hx g

@[simp]
theorem ambientToBlockSpecialOrthogonalMatrixPoint_mulVec
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.specialOrthogonalMatrixPoint A)
    (y : Fin (m + 1) → A) :
    Matrix.mulVec (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx g).1 y =
      P.ambientToBlockConjugateIsometryEquiv A hx g y := by
  change Matrix.toLin'
      (LinearMap.toMatrix'
        (P.ambientToBlockConjugateIsometryEquiv A hx g).toLinearEquiv.toLinearMap) y = _
  rw [Matrix.toLin'_toMatrix']
  rfl

/-- Transport an ambient intrinsic general-Spin point back to the supplied
native block presentation. -/
def ambientToBlockGeneralSpinIntrinsicPoint
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : V.CliffordGeneralSpinIntrinsicPoint A) :
    (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A where
  cliffordUnit := Units.map
    (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).symm.toAlgHom.toMonoidHom
      z.cliffordUnit
  similitude := z.similitude
  matrixPoint := P.ambientToBlockSpecialOrthogonalMatrixPoint A hx z.matrixPoint
  involute_eq := by
    let Phi := P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
    have hunit :
        Phi (((Units.map Phi.symm.toAlgHom.toMonoidHom z.cliffordUnit :
          ((P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
            (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)) =
          (z.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) := by
      rw [Units.coe_map]
      exact Phi.apply_symm_apply _
    apply Phi.injective
    rw [rationalIsometryCliffordBaseChangeAlgEquiv_involute,
      hunit, z.involute_eq]
  mul_reverse_eq := by
    let Phi := P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
    have hunit :
        Phi (((Units.map Phi.symm.toAlgHom.toMonoidHom z.cliffordUnit :
          ((P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
            (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)) =
          (z.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) := by
      rw [Units.coe_map]
      exact Phi.apply_symm_apply _
    apply Phi.injective
    rw [map_mul, rationalIsometryCliffordBaseChangeAlgEquiv_reverse]
    rw [hunit, z.mul_reverse_eq]
    exact (Phi.commutes z.similitude).symm
  vectorGraph := by
    intro i
    let E := P.blockToAmbientBaseChangeIsometryEquiv hx A
    let Phi := P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
    let b : Fin (m + 1) → A := Pi.single i 1
    have hunit :
        Phi (((Units.map Phi.symm.toAlgHom.toMonoidHom z.cliffordUnit :
          ((P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
            (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)) =
          (z.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) := by
      rw [Units.coe_map]
      exact Phi.apply_symm_apply _
    have hinv :
        Phi ((((Units.map Phi.symm.toAlgHom.toMonoidHom z.cliffordUnit)⁻¹ :
          ((P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
            (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)) =
          (((z.cliffordUnit⁻¹ :
            (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
              V.cliffordCoordinateBaseChangeAlgebra A)) := by
      have hunitU :
          Units.map Phi.toAlgHom.toMonoidHom
              (Units.map Phi.symm.toAlgHom.toMonoidHom z.cliffordUnit) =
            z.cliffordUnit := by
        apply Units.ext
        exact hunit
      simpa only [map_inv, Units.coe_map] using
        congrArg Units.val (congrArg Inv.inv hunitU)
    have hbvec :
        (P.blockSpace hx).cliffordCoordinateBaseChangeVector A i =
          (P.blockSpace hx).cliffordCoordinateBaseChangeVectorOfCoordinates A b := by
      simp [b, cliffordCoordinateBaseChangeVectorOfCoordinates,
        Pi.single_apply]
    rw [hbvec]
    rw [← cliffordCoordinateBaseChangeVectorOfCoordinates]
    have hcolumn :
        (fun j ↦ (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx
          z.matrixPoint).1 j i) =
          Matrix.mulVec
            (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx z.matrixPoint).1 b := by
      ext j
      simp [b, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcolumn]
    apply Phi.injective
    rw [map_mul, map_mul,
      P.blockToAmbientCliffordBaseChangeAlgEquiv_vectorOfCoordinates A hx,
      P.blockToAmbientCliffordBaseChangeAlgEquiv_vectorOfCoordinates A hx,
      hunit, hinv,
      P.ambientToBlockSpecialOrthogonalMatrixPoint_mulVec A hx z.matrixPoint b]
    change _ = V.cliffordCoordinateBaseChangeVectorOfCoordinates A
      (E (E.symm
        (V.specialOrthogonalMatrixPointIsometryEquiv A z.matrixPoint (E b))))
    have hE := E.apply_symm_apply
      (V.specialOrthogonalMatrixPointIsometryEquiv A z.matrixPoint (E b))
    calc
      _ = V.cliffordCoordinateBaseChangeVectorOfCoordinates A
          (Matrix.mulVec z.matrixPoint.1 (E b)) :=
        CliffordGeneralSpinIntrinsicPoint.vectorGraph_coordinates V A z (E b)
      _ = V.cliffordCoordinateBaseChangeVectorOfCoordinates A
          (V.specialOrthogonalMatrixPointIsometryEquiv A z.matrixPoint (E b)) :=
        congrArg (V.cliffordCoordinateBaseChangeVectorOfCoordinates A)
          (V.specialOrthogonalMatrixPointIsometryEquiv_apply A z.matrixPoint (E b)).symm
      _ = _ :=
        (congrArg (V.cliffordCoordinateBaseChangeVectorOfCoordinates A) hE).symm

@[simp]
theorem ambientToBlockGeneralSpinIntrinsicPoint_cliffordUnit
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : V.CliffordGeneralSpinIntrinsicPoint A) :
    (P.ambientToBlockGeneralSpinIntrinsicPoint A hx z).cliffordUnit =
      Units.map
        (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).symm.toAlgHom.toMonoidHom
          z.cliffordUnit :=
  rfl

@[simp]
theorem blockToAmbientGeneralSpinIntrinsicPoint_cliffordUnit
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A) :
    (P.blockToAmbientGeneralSpinIntrinsicPoint A hx z).cliffordUnit =
      Units.map
        (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).toAlgHom.toMonoidHom
          z.cliffordUnit :=
  rfl

/-- Reverse transport is a left inverse of the block-to-ambient intrinsic
general-Spin point map. -/
theorem ambientToBlockGeneralSpinIntrinsicPoint_blockToAmbient
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A) :
    P.ambientToBlockGeneralSpinIntrinsicPoint A hx
        (P.blockToAmbientGeneralSpinIntrinsicPoint A hx z) = z := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit (P.blockSpace hx) A
  apply Units.ext
  change (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).symm
      (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
        (z.cliffordUnit :
          (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)) = _
  exact (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).symm_apply_apply _

/-- Reverse transport is a right inverse of the block-to-ambient intrinsic
general-Spin point map. -/
theorem blockToAmbientGeneralSpinIntrinsicPoint_ambientToBlock
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : V.CliffordGeneralSpinIntrinsicPoint A) :
    P.blockToAmbientGeneralSpinIntrinsicPoint A hx
        (P.ambientToBlockGeneralSpinIntrinsicPoint A hx z) = z := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V A
  apply Units.ext
  change P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
      ((P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).symm
        (z.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A)) = _
  exact (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).apply_symm_apply _

/-- Intrinsic general-Spin groups attached to a supplied anisotropic block
presentation are multiplicatively equivalent on every native coefficient
algebra. -/
def blockToAmbientGeneralSpinMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A ≃*
      V.CliffordGeneralSpinIntrinsicPoint A where
  toFun := P.blockToAmbientGeneralSpinIntrinsicPoint A hx
  invFun := P.ambientToBlockGeneralSpinIntrinsicPoint A hx
  left_inv := P.ambientToBlockGeneralSpinIntrinsicPoint_blockToAmbient A hx
  right_inv := P.blockToAmbientGeneralSpinIntrinsicPoint_ambientToBlock A hx
  map_mul' z w := by
    apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V A
    apply Units.ext
    change P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
        ((z.cliffordUnit :
            (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A) *
          (w.cliffordUnit :
            (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)) =
      P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
          (z.cliffordUnit :
            (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A) *
        P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
          (w.cliffordUnit :
            (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)
    exact map_mul _ _ _

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
