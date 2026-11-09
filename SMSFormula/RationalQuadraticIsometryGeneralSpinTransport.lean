import SMSFormula.RationalQuadraticIsometryCliffordTransport
import SMSFormula.RationalCliffordGeneralSpinNaturality

/-!
# Intrinsic general-Spin transport along rational quadratic isometries

This file begins the group-level comparison attached to a supplied
anisotropic-complement presentation.  It first upgrades a native
special-orthogonal matrix point over an arbitrary commutative rational algebra
to its quadratic self-isometry, then conjugates that self-isometry through the
already certified block-to-ambient quadratic equivalence.

The construction works over the actual adelic coefficient rings; it does not
use the field-only determinant-one-isometry interface.  No topology, Haar
measure, quotient, shell measure, or orbit kernel is transported here.
-/

noncomputable section

open scoped Matrix TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {r : ℕ} (U : RationalQuadraticSpaceMatrix r)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- A native special-orthogonal matrix point over an arbitrary commutative
rational algebra acts as a quadratic self-isometry. -/
def specialOrthogonalMatrixPointIsometryEquiv
    (g : U.specialOrthogonalMatrixPoint A) :
    (U.commutativeScalarExtensionQuadraticForm A).IsometryEquiv
      (U.commutativeScalarExtensionQuadraticForm A) := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  let G := U.specialOrthogonalMatrixPointToGroup A g
  let e : (Fin r → A) ≃ₗ[A] (Fin r → A) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv A (Fin r → A))
      (Matrix.GeneralLinearGroup.toLin G.1.1)
  have he : LinearMap.toMatrix' e.toLinearMap = g.1 := by
    change LinearMap.toMatrix' (Matrix.toLin' G.1.1.1) = g.1
    rw [LinearMap.toMatrix'_toLin']
    exact U.specialOrthogonalMatrixPointEquivGroup A |>.left_inv g |>
      congrArg Subtype.val
  have hmatrix :
      QuadraticForm.toMatrix' ((U.commutativeScalarExtensionQuadraticForm A).comp
        e.toLinearMap) =
      QuadraticForm.toMatrix' (U.commutativeScalarExtensionQuadraticForm A) := by
    rw [QuadraticForm.toMatrix'_comp, he,
      U.commutativeScalarExtensionQuadraticForm_toMatrix' A]
    simpa [commutativeScalarExtensionFormMatrix,
      specialOrthogonalMappedFormMatrix] using g.2.1
  have hassoc :
      ((U.commutativeScalarExtensionQuadraticForm A).comp
        e.toLinearMap).associated =
      (U.commutativeScalarExtensionQuadraticForm A).associated :=
    (LinearMap.toMatrix₂' A).injective hmatrix
  exact
    { toLinearEquiv := e
      map_app' := fun x ↦ by
        calc
          U.commutativeScalarExtensionQuadraticForm A (e x) =
              ((U.commutativeScalarExtensionQuadraticForm A).comp
                e.toLinearMap) x := rfl
          _ = ((U.commutativeScalarExtensionQuadraticForm A).comp
                e.toLinearMap).associated x x :=
              (((U.commutativeScalarExtensionQuadraticForm A).comp
                e.toLinearMap).associated_eq_self_apply ℕ x).symm
          _ = (U.commutativeScalarExtensionQuadraticForm A).associated x x :=
              congrArg (fun B ↦ B x x) hassoc
          _ = U.commutativeScalarExtensionQuadraticForm A x :=
              (U.commutativeScalarExtensionQuadraticForm A).associated_eq_self_apply ℕ x }

@[simp]
theorem specialOrthogonalMatrixPointIsometryEquiv_toMatrix'
    (g : U.specialOrthogonalMatrixPoint A) :
    LinearMap.toMatrix'
        (U.specialOrthogonalMatrixPointIsometryEquiv A g).toLinearEquiv.toLinearMap =
      g.1 := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  simp only [specialOrthogonalMatrixPointIsometryEquiv]
  change LinearMap.toMatrix' (Matrix.toLin'
      (U.specialOrthogonalMatrixPointToGroup A g).1.1.1) = g.1
  rw [LinearMap.toMatrix'_toLin']
  exact U.specialOrthogonalMatrixPointEquivGroup A |>.left_inv g |>
    congrArg Subtype.val

@[simp]
theorem specialOrthogonalMatrixPointIsometryEquiv_apply
    (g : U.specialOrthogonalMatrixPoint A) (y : Fin r → A) :
    U.specialOrthogonalMatrixPointIsometryEquiv A g y =
      Matrix.mulVec g.1 y := by
  rw [← U.specialOrthogonalMatrixPointIsometryEquiv_toMatrix' A g]
  change _ = Matrix.toLin'
    (LinearMap.toMatrix'
      (U.specialOrthogonalMatrixPointIsometryEquiv A g).toLinearEquiv.toLinearMap) y
  rw [Matrix.toLin'_toMatrix']
  rfl

namespace CliffordGeneralSpinIntrinsicPoint

/-- The stored basis graph of an intrinsic general-Spin point extends to the
whole native vector module. -/
theorem vectorGraph_coordinates
    (z : U.CliffordGeneralSpinIntrinsicPoint A) (v : Fin r → A) :
    (z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A) *
        U.cliffordCoordinateBaseChangeVectorOfCoordinates A v *
        ((z.cliffordUnit⁻¹ :
          (U.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
            U.cliffordCoordinateBaseChangeAlgebra A) =
      U.cliffordCoordinateBaseChangeVectorOfCoordinates A
        (Matrix.mulVec z.matrixPoint.1 v) := by
  rw [cliffordCoordinateBaseChangeVectorOfCoordinates,
    U.cliffordCoordinateBaseChange_mul_sum_mul]
  simp_rw [z.vectorGraph, Finset.smul_sum, smul_smul]
  rw [cliffordCoordinateBaseChangeVectorOfCoordinates, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

end CliffordGeneralSpinIntrinsicPoint

namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The presentation Clifford equivalence carries the entire native vector
module through the supplied scalar-extended quadratic isometry. -/
theorem blockToAmbientCliffordBaseChangeAlgEquiv_vectorOfCoordinates
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (v : Fin (m + 1) → A) :
    P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
        ((P.blockSpace hx).cliffordCoordinateBaseChangeVectorOfCoordinates A v) =
      V.cliffordCoordinateBaseChangeVectorOfCoordinates A
        (P.blockToAmbientBaseChangeIsometryEquiv hx A v) := by
  let E := P.blockToAmbientBaseChangeIsometryEquiv hx A
  have hv : v = ∑ i, v i • (Pi.single i (1 : A) : Fin (m + 1) → A) := by
    symm
    exact commutativeScalarExtension_single_sum A v
  change P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
      (∑ i, v i • (P.blockSpace hx).cliffordCoordinateBaseChangeVector A i) = _
  rw [map_sum]
  simp_rw [map_smul]
  have hE : E v =
      ∑ i, v i • E (Pi.single i (1 : A)) := by
    calc
      E v = E (∑ i, v i •
          (Pi.single i (1 : A) : Fin (m + 1) → A)) := congrArg E hv
      _ = ∑ i, v i • E (Pi.single i (1 : A)) := by simp
  rw [hE]
  rw [cliffordCoordinateBaseChangeVectorOfCoordinates]
  simp_rw [Finset.sum_apply, Pi.smul_apply]
  conv_rhs =>
    enter [2, j]
    rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [smul_assoc]
  rw [← Finset.smul_sum]
  congr 1
  change P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
      ((1 : A) ⊗ₜ[ℚ] CliffordAlgebra.ι
        (P.blockSpace hx).quadraticForm
        (Pi.single i (1 : ℚ))) = _
  rw [rationalIsometryCliffordBaseChangeAlgEquiv_tmul_ι]
  have hEi := P.blockToAmbientBaseChangeIsometryEquiv_rational hx A
    (Pi.single i (1 : ℚ))
  apply (V.commutativeTensorCliffordEquiv A).injective
  rw [V.commutativeTensorCliffordEquiv_tmul_ι, map_sum]
  simp_rw [map_smul,
    V.commutativeTensorCliffordEquiv_baseChangeVector]
  simp_rw [← map_smul
    (CliffordAlgebra.ι (V.commutativeScalarExtensionQuadraticForm A))]
  rw [← map_sum]
  congr 1
  rw [commutativeScalarExtension_single_sum]
  have hsingle :
      (fun j ↦ algebraMap ℚ A
        ((Pi.single i (1 : ℚ) : Fin (m + 1) → ℚ) j)) =
        (Pi.single i (1 : A) : Fin (m + 1) → A) := by
    ext j
    simp [Pi.single_apply]
  simpa [Algebra.smul_def] using
    hEi.symm.trans (congrArg E hsingle)

/-- Conjugate a block special-orthogonal point through the supplied native
block-to-ambient quadratic isometry. -/
def blockToAmbientConjugateIsometryEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : (P.blockSpace hx).specialOrthogonalMatrixPoint A) :
    (V.commutativeScalarExtensionQuadraticForm A).IsometryEquiv
      (V.commutativeScalarExtensionQuadraticForm A) :=
  let e := P.blockToAmbientBaseChangeIsometryEquiv hx A
  (e.symm.trans
    ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g)).trans e

/-- Conjugation through a quadratic equivalence preserves the literal
determinant-one normalization over every commutative rational algebra. -/
theorem blockToAmbientConjugateIsometryEquiv_det
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : (P.blockSpace hx).specialOrthogonalMatrixPoint A) :
    LinearMap.det
        (P.blockToAmbientConjugateIsometryEquiv A hx g).toLinearEquiv.toLinearMap = 1 := by
  let e := P.blockToAmbientBaseChangeIsometryEquiv hx A
  let h := (P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g
  have hhdet : LinearEquiv.det h.toLinearEquiv = 1 := by
    apply Units.ext
    simp only [LinearEquiv.coe_det, Units.val_one]
    rw [← LinearMap.det_toMatrix',
      (P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv_toMatrix' A g]
    exact g.2.2
  have hconj := LinearEquiv.det_conj h.toLinearEquiv e.toLinearEquiv
  change LinearMap.det
      ((e.symm.trans h).trans e).toLinearEquiv.toLinearMap = 1
  rw [← LinearEquiv.coe_det]
  exact congrArg Units.val (hconj.trans hhdet)

/-- The special-orthogonal matrix point obtained by conjugating the source
action through the supplied block-to-ambient isometry. -/
def blockToAmbientSpecialOrthogonalMatrixPoint
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : (P.blockSpace hx).specialOrthogonalMatrixPoint A) :
    V.specialOrthogonalMatrixPoint A := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  let h := P.blockToAmbientConjugateIsometryEquiv A hx g
  refine ⟨LinearMap.toMatrix' h.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · have hcomp :
        (V.commutativeScalarExtensionQuadraticForm A).comp
            h.toLinearEquiv.toLinearMap =
          V.commutativeScalarExtensionQuadraticForm A := by
      apply QuadraticMap.ext
      intro y
      exact h.map_app y
    have hmatrix := congrArg QuadraticForm.toMatrix' hcomp
    rw [QuadraticForm.toMatrix'_comp,
      V.commutativeScalarExtensionQuadraticForm_toMatrix' A] at hmatrix
    simpa [commutativeScalarExtensionFormMatrix,
      specialOrthogonalMappedFormMatrix] using hmatrix
  · rw [LinearMap.det_toMatrix']
    exact P.blockToAmbientConjugateIsometryEquiv_det A hx g

@[simp]
theorem blockToAmbientSpecialOrthogonalMatrixPoint_toMatrix'
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : (P.blockSpace hx).specialOrthogonalMatrixPoint A) :
    (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx g).1 =
      LinearMap.toMatrix'
        (P.blockToAmbientConjugateIsometryEquiv A hx g).toLinearEquiv.toLinearMap :=
  rfl

/-- The matrix of the conjugated special-orthogonal point acts literally as
the conjugated quadratic self-isometry. -/
theorem blockToAmbientSpecialOrthogonalMatrixPoint_mulVec
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : (P.blockSpace hx).specialOrthogonalMatrixPoint A)
    (y : Fin n → A) :
    Matrix.mulVec (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx g).1 y =
      P.blockToAmbientConjugateIsometryEquiv A hx g y := by
  change Matrix.toLin'
      (LinearMap.toMatrix'
        (P.blockToAmbientConjugateIsometryEquiv A hx g).toLinearEquiv.toLinearMap) y = _
  rw [Matrix.toLin'_toMatrix']
  rfl

/-- A supplied anisotropic-complement presentation transports an intrinsic
general-Spin point from the native block presentation to the ambient one. -/
def blockToAmbientGeneralSpinIntrinsicPoint
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A) :
    V.CliffordGeneralSpinIntrinsicPoint A where
  cliffordUnit := Units.map
    (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).toAlgHom.toMonoidHom
      z.cliffordUnit
  similitude := z.similitude
  matrixPoint := P.blockToAmbientSpecialOrthogonalMatrixPoint A hx z.matrixPoint
  involute_eq := by
    change V.cliffordCoordinateBaseChangeInvolute A
        (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
          (z.cliffordUnit :
            (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)) =
      P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
        (z.cliffordUnit :
          (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)
    rw [← rationalIsometryCliffordBaseChangeAlgEquiv_involute,
      z.involute_eq]
  mul_reverse_eq := by
    change
      P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
          (z.cliffordUnit :
            (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A) *
        V.cliffordCoordinateBaseChangeReverse A
          (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
            (z.cliffordUnit :
              (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)) =
      algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) z.similitude
    rw [← rationalIsometryCliffordBaseChangeAlgEquiv_reverse,
      ← map_mul, z.mul_reverse_eq]
    exact (P.blockToAmbientCliffordBaseChangeAlgEquiv hx A).commutes z.similitude
  vectorGraph := by
    intro i
    let E := P.blockToAmbientBaseChangeIsometryEquiv hx A
    let Phi := P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
    let b : Fin n → A := Pi.single i 1
    let v : Fin (m + 1) → A := E.symm b
    have hz := congrArg Phi
      (CliffordGeneralSpinIntrinsicPoint.vectorGraph_coordinates
        (P.blockSpace hx) A z v)
    have hleft :
        Phi
          ((z.cliffordUnit :
              (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A) *
            (P.blockSpace hx).cliffordCoordinateBaseChangeVectorOfCoordinates A v *
            ((z.cliffordUnit⁻¹ :
              ((P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
                (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)) =
          ((Units.map Phi.toAlgHom.toMonoidHom z.cliffordUnit :
              (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
                V.cliffordCoordinateBaseChangeAlgebra A) *
            V.cliffordCoordinateBaseChangeVector A i *
            (((Units.map Phi.toAlgHom.toMonoidHom z.cliffordUnit)⁻¹ :
              (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
                V.cliffordCoordinateBaseChangeAlgebra A) := by
      rw [map_mul, map_mul,
        P.blockToAmbientCliffordBaseChangeAlgEquiv_vectorOfCoordinates A hx]
      change _ * V.cliffordCoordinateBaseChangeVectorOfCoordinates A (E v) * _ = _
      have hEv : E v = b := E.apply_symm_apply b
      rw [hEv]
      simp [b, cliffordCoordinateBaseChangeVectorOfCoordinates,
        Pi.single_apply]
    rw [hleft] at hz
    rw [P.blockToAmbientCliffordBaseChangeAlgEquiv_vectorOfCoordinates A hx] at hz
    rw [← cliffordCoordinateBaseChangeVectorOfCoordinates]
    have hcolumn :
        (fun j ↦ (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx
          z.matrixPoint).1 j i) =
          Matrix.mulVec
            (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx z.matrixPoint).1 b := by
      ext j
      simp [b, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcolumn,
      P.blockToAmbientSpecialOrthogonalMatrixPoint_mulVec A hx z.matrixPoint b]
    change _ = V.cliffordCoordinateBaseChangeVectorOfCoordinates A
      (E ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A
        z.matrixPoint (E.symm b)))
    rw [(P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv_apply A]
    exact hz

end AnisotropicComplementPresentation

end RationalQuadraticSpaceMatrix
