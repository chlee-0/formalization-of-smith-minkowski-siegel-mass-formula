import SMSFormula.RationalQuadraticIsometryGeneralSpinTopology
import SMSFormula.RationalCliffordSpinCandidateAdelicGeneralSpinQuotientExactness

/-!
# Spin transport along an arbitrary rational quadratic isometry

The anisotropic-complement transport developed earlier is specialized to an
isometry from a last-coordinate block.  Equal-norm complement witnesses,
however, naturally produce an isometry between two unrelated coordinate
matrices of the same rank.  This file supplies the missing algebraic carrier
interface for that situation.

A supplied rational quadratic isometry is extended to every commutative
rational algebra, then used to conjugate the represented special-orthogonal
action and transport Clifford coordinates.  The resulting intrinsic
`GSpin` equivalence preserves similitude and restricts to the implemented
Spin carrier.  No topology, Haar measure, integral structure, quotient
measure, lattice presentation, or Tamagawa value is chosen here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix TensorProduct

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 800000

variable {r s : ℕ}
variable (U : RationalQuadraticSpaceMatrix r)
variable (V : RationalQuadraticSpaceMatrix s)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

/-- Scalar extension of an arbitrary rational quadratic isometry on the
repository's native coordinate carriers. -/
def rationalIsometryBaseChangeIsometryEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (U.commutativeScalarExtensionQuadraticForm A).IsometryEquiv
      (V.commutativeScalarExtensionQuadraticForm A) := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  exact
    (U.commutativeScalarExtensionQuadraticIsometryEquiv A).symm
      |>.trans (e.baseChange (A := A))
      |>.trans (V.commutativeScalarExtensionQuadraticIsometryEquiv A)

/-- Scalar extension agrees with entrywise base change on rational vectors. -/
@[simp]
theorem rationalIsometryBaseChangeIsometryEquiv_rational
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (y : Fin r → ℚ) :
    rationalIsometryBaseChangeIsometryEquiv U V e A
        (fun i ↦ algebraMap ℚ A (y i)) =
      fun i ↦ algebraMap ℚ A (e y i) := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  let eU := U.commutativeScalarExtensionQuadraticIsometryEquiv A
  let eV := V.commutativeScalarExtensionQuadraticIsometryEquiv A
  have hU :
      eU.symm (fun i ↦ algebraMap ℚ A (y i)) =
        (1 : A) ⊗ₜ[ℚ] y := by
    change (commutativeScalarExtensionModuleEquiv (n := r) A).symm
      (fun i ↦ algebraMap ℚ A (y i)) = (1 : A) ⊗ₜ[ℚ] y
    rw [LinearEquiv.symm_apply_eq]
    ext i
    symm
    change (TensorProduct.piScalarRight ℚ A A (Fin r)
      ((1 : A) ⊗ₜ[ℚ] y)) i = _
    rw [TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    simp [Algebra.smul_def]
  change eV ((e.baseChange (A := A))
    (eU.symm (fun i ↦ algebraMap ℚ A (y i)))) = _
  rw [hU, QuadraticMap.IsometryEquiv.baseChange_tmul]
  ext i
  change (TensorProduct.piScalarRight ℚ A A (Fin s)
      ((1 : A) ⊗ₜ[ℚ] e y)) i = _
  rw [TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
  simp [Algebra.smul_def]

/-- Reversing the rational isometry reverses its Clifford transport. -/
theorem rationalIsometryCliffordBaseChangeAlgEquiv_symm_eq
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    rationalIsometryCliffordBaseChangeAlgEquiv V U e.symm A =
      (rationalIsometryCliffordBaseChangeAlgEquiv U V e A).symm := by
  ext z
  exact
    (rationalIsometryCliffordBaseChangeAlgEquiv_symm_apply U V e A z).symm

/-- Clifford transport carries the entire native vector module through the
scalar-extended quadratic isometry. -/
theorem rationalIsometryCliffordBaseChangeAlgEquiv_vectorOfCoordinates
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (v : Fin r → A) :
    rationalIsometryCliffordBaseChangeAlgEquiv U V e A
        (U.cliffordCoordinateBaseChangeVectorOfCoordinates A v) =
      V.cliffordCoordinateBaseChangeVectorOfCoordinates A
        (rationalIsometryBaseChangeIsometryEquiv U V e A v) := by
  let E := rationalIsometryBaseChangeIsometryEquiv U V e A
  have hv : v = ∑ i, v i • (Pi.single i (1 : A) : Fin r → A) := by
    symm
    exact commutativeScalarExtension_single_sum A v
  change rationalIsometryCliffordBaseChangeAlgEquiv U V e A
      (∑ i, v i • U.cliffordCoordinateBaseChangeVector A i) = _
  rw [map_sum]
  simp_rw [map_smul]
  have hE : E v = ∑ i, v i • E (Pi.single i (1 : A)) := by
    calc
      E v = E (∑ i, v i • (Pi.single i (1 : A) : Fin r → A)) :=
        congrArg E hv
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
  change rationalIsometryCliffordBaseChangeAlgEquiv U V e A
      ((1 : A) ⊗ₜ[ℚ] CliffordAlgebra.ι U.quadraticForm
        (Pi.single i (1 : ℚ))) = _
  rw [rationalIsometryCliffordBaseChangeAlgEquiv_tmul_ι]
  have hEi := rationalIsometryBaseChangeIsometryEquiv_rational U V e A
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
        ((Pi.single i (1 : ℚ) : Fin r → ℚ) j)) =
        (Pi.single i (1 : A) : Fin r → A) := by
    ext j
    simp [Pi.single_apply]
  simpa [Algebra.smul_def] using
    hEi.symm.trans (congrArg E hsingle)

/-- Conjugate a represented special-orthogonal point through an arbitrary
rational quadratic isometry. -/
def rationalIsometrySpecialOrthogonalMatrixPoint
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : U.specialOrthogonalMatrixPoint A) :
    V.specialOrthogonalMatrixPoint A := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  let E := rationalIsometryBaseChangeIsometryEquiv U V e A
  let h : (V.commutativeScalarExtensionQuadraticForm A).IsometryEquiv
      (V.commutativeScalarExtensionQuadraticForm A) :=
    (E.symm.trans (U.specialOrthogonalMatrixPointIsometryEquiv A g)).trans E
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
  · let hU := U.specialOrthogonalMatrixPointIsometryEquiv A g
    have hhdet : LinearEquiv.det hU.toLinearEquiv = 1 := by
      apply Units.ext
      simp only [LinearEquiv.coe_det, Units.val_one]
      rw [← LinearMap.det_toMatrix',
        U.specialOrthogonalMatrixPointIsometryEquiv_toMatrix' A g]
      exact g.2.2
    have hconj := LinearEquiv.det_conj hU.toLinearEquiv E.toLinearEquiv
    rw [LinearMap.det_toMatrix']
    change LinearMap.det h.toLinearEquiv.toLinearMap = 1
    rw [← LinearEquiv.coe_det]
    exact congrArg Units.val (hconj.trans hhdet)

@[simp]
theorem rationalIsometrySpecialOrthogonalMatrixPoint_mulVec
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : U.specialOrthogonalMatrixPoint A) (y : Fin s → A) :
    Matrix.mulVec
        (rationalIsometrySpecialOrthogonalMatrixPoint U V e A g).1 y =
      rationalIsometryBaseChangeIsometryEquiv U V e A
        (Matrix.mulVec g.1
          ((rationalIsometryBaseChangeIsometryEquiv U V e A).symm y)) := by
  change Matrix.toLin'
      (LinearMap.toMatrix' _)
      y = _
  rw [Matrix.toLin'_toMatrix']
  rfl

/-- Transport an intrinsic `GSpin` point along an arbitrary rational
quadratic isometry. -/
def rationalIsometryGeneralSpinIntrinsicPoint
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : U.CliffordGeneralSpinIntrinsicPoint A) :
    V.CliffordGeneralSpinIntrinsicPoint A where
  cliffordUnit := Units.map
    (rationalIsometryCliffordBaseChangeAlgEquiv U V e A).toAlgHom.toMonoidHom
      z.cliffordUnit
  similitude := z.similitude
  matrixPoint := rationalIsometrySpecialOrthogonalMatrixPoint U V e A z.matrixPoint
  involute_eq := by
    change V.cliffordCoordinateBaseChangeInvolute A
        (rationalIsometryCliffordBaseChangeAlgEquiv U V e A
          (z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A)) =
      rationalIsometryCliffordBaseChangeAlgEquiv U V e A
        (z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A)
    rw [← rationalIsometryCliffordBaseChangeAlgEquiv_involute,
      z.involute_eq]
  mul_reverse_eq := by
    change
      rationalIsometryCliffordBaseChangeAlgEquiv U V e A
          (z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A) *
        V.cliffordCoordinateBaseChangeReverse A
          (rationalIsometryCliffordBaseChangeAlgEquiv U V e A
            (z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A)) =
      algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) z.similitude
    rw [← rationalIsometryCliffordBaseChangeAlgEquiv_reverse,
      ← map_mul, z.mul_reverse_eq]
    exact (rationalIsometryCliffordBaseChangeAlgEquiv U V e A).commutes
      z.similitude
  vectorGraph := by
    intro i
    let E := rationalIsometryBaseChangeIsometryEquiv U V e A
    let Phi := rationalIsometryCliffordBaseChangeAlgEquiv U V e A
    let b : Fin s → A := Pi.single i 1
    let v : Fin r → A := E.symm b
    have hz := congrArg Phi
      (CliffordGeneralSpinIntrinsicPoint.vectorGraph_coordinates U A z v)
    have hleft :
        Phi
          ((z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A) *
            U.cliffordCoordinateBaseChangeVectorOfCoordinates A v *
            ((z.cliffordUnit⁻¹ :
              (U.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
                U.cliffordCoordinateBaseChangeAlgebra A)) =
          ((Units.map Phi.toAlgHom.toMonoidHom z.cliffordUnit :
              (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
                V.cliffordCoordinateBaseChangeAlgebra A) *
            V.cliffordCoordinateBaseChangeVector A i *
            (((Units.map Phi.toAlgHom.toMonoidHom z.cliffordUnit)⁻¹ :
              (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
                V.cliffordCoordinateBaseChangeAlgebra A) := by
      rw [map_mul, map_mul,
        rationalIsometryCliffordBaseChangeAlgEquiv_vectorOfCoordinates]
      change _ * V.cliffordCoordinateBaseChangeVectorOfCoordinates A (E v) * _ = _
      have hEv : E v = b := E.apply_symm_apply b
      rw [hEv]
      simp [b, cliffordCoordinateBaseChangeVectorOfCoordinates,
        Pi.single_apply]
    rw [hleft] at hz
    rw [rationalIsometryCliffordBaseChangeAlgEquiv_vectorOfCoordinates] at hz
    rw [← cliffordCoordinateBaseChangeVectorOfCoordinates]
    have hcolumn :
        (fun j ↦ (rationalIsometrySpecialOrthogonalMatrixPoint U V e A
          z.matrixPoint).1 j i) =
          Matrix.mulVec
            (rationalIsometrySpecialOrthogonalMatrixPoint U V e A
              z.matrixPoint).1 b := by
      ext j
      simp [b, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcolumn,
      rationalIsometrySpecialOrthogonalMatrixPoint_mulVec]
    change _ = V.cliffordCoordinateBaseChangeVectorOfCoordinates A
      (E (Matrix.mulVec z.matrixPoint.1 (E.symm b)))
    exact hz

@[simp]
theorem rationalIsometryGeneralSpinIntrinsicPoint_cliffordUnit
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : U.CliffordGeneralSpinIntrinsicPoint A) :
    (rationalIsometryGeneralSpinIntrinsicPoint U V e A z).cliffordUnit =
      Units.map
        (rationalIsometryCliffordBaseChangeAlgEquiv U V e A).toAlgHom.toMonoidHom
        z.cliffordUnit :=
  rfl

@[simp]
theorem rationalIsometryGeneralSpinIntrinsicPoint_similitude
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : U.CliffordGeneralSpinIntrinsicPoint A) :
    (rationalIsometryGeneralSpinIntrinsicPoint U V e A z).similitude =
      z.similitude :=
  rfl

/-- Intrinsic `GSpin` is invariant under every supplied rational quadratic
isometry. -/
def rationalIsometryGeneralSpinMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    U.CliffordGeneralSpinIntrinsicPoint A ≃*
      V.CliffordGeneralSpinIntrinsicPoint A where
  toFun := rationalIsometryGeneralSpinIntrinsicPoint U V e A
  invFun := rationalIsometryGeneralSpinIntrinsicPoint V U e.symm A
  left_inv z := by
    apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit U A
    apply Units.ext
    change rationalIsometryCliffordBaseChangeAlgEquiv V U e.symm A
        (rationalIsometryCliffordBaseChangeAlgEquiv U V e A
          (z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A)) = _
    rw [rationalIsometryCliffordBaseChangeAlgEquiv_symm_eq]
    exact (rationalIsometryCliffordBaseChangeAlgEquiv U V e A).symm_apply_apply _
  right_inv z := by
    apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V A
    apply Units.ext
    change rationalIsometryCliffordBaseChangeAlgEquiv U V e A
        (rationalIsometryCliffordBaseChangeAlgEquiv V U e.symm A
          (z.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A)) = _
    rw [rationalIsometryCliffordBaseChangeAlgEquiv_symm_eq]
    exact (rationalIsometryCliffordBaseChangeAlgEquiv U V e A).apply_symm_apply _
  map_mul' z w := by
    apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V A
    apply Units.ext
    change rationalIsometryCliffordBaseChangeAlgEquiv U V e A
        ((z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A) *
          (w.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A)) = _
    exact map_mul _ _ _

/-- General-Spin transport commutes with extension of the coefficient
algebra. -/
theorem rationalIsometryGeneralSpinIntrinsicPoint_naturality
    {A B : Type*} [CommRing A] [Algebra ℚ A]
    [CommRing B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B)
    (z : U.CliffordGeneralSpinIntrinsicPoint A) :
    rationalIsometryGeneralSpinIntrinsicPoint U V e B
        (CliffordGeneralSpinIntrinsicPoint.map U f z) =
      CliffordGeneralSpinIntrinsicPoint.map V f
        (rationalIsometryGeneralSpinIntrinsicPoint U V e A z) := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V B
  apply Units.ext
  exact rationalIsometryCliffordBaseChangeAlgEquiv_naturality U V e f
    (z.cliffordUnit : U.cliffordCoordinateBaseChangeAlgebra A)

private theorem rationalIsometrySpinCandidateEmbedding_injective
    (W : RationalQuadraticSpaceMatrix r)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Injective
      (W.cliffordSpinCandidateToCliffordGeneralSpinHom A) := by
  intro a b hab
  apply (W.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).injective
  apply CliffordSpinCandidatePointData.ext_clifford W A
  exact congrArg
    (fun z : W.CliffordGeneralSpinIntrinsicPoint A ↦
      (z.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A)) hab

private def rationalIsometrySpinCandidateGeneralSpinKernelMulEquiv
    (W : RationalQuadraticSpaceMatrix r)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.CliffordSpinCandidateGroup A ≃*
      (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom W A).ker :=
  MulEquiv.ofBijective
    ((W.cliffordSpinCandidateToCliffordGeneralSpinHom A).codRestrict
      (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom W A).ker
      (fun z => by
        change
          (W.cliffordSpinCandidateToCliffordGeneralSpinHom A z).similitude = 1
        exact
          W.cliffordSpinCandidateToCliffordGeneralSpinHom_apply_similitude A z))
    ⟨fun _ _ h ↦ W.rationalIsometrySpinCandidateEmbedding_injective A
        (congrArg Subtype.val h), by
      intro z
      have hz : z.1 ∈
          (W.cliffordSpinCandidateToCliffordGeneralSpinHom A).range := by
        rw [W.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker A]
        exact z.2
      rcases hz with ⟨w, hw⟩
      exact ⟨w, Subtype.ext hw⟩⟩

/-- Arbitrary rational-isometry transport maps the similitude-one subgroup
of intrinsic `GSpin` exactly onto the target similitude-one subgroup. -/
theorem rationalIsometryGeneralSpin_similitudeKernel_map
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    ((CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom U A).ker.map
      (rationalIsometryGeneralSpinMulEquiv U V e A).toMonoidHom) =
      (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V A).ker := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    refine ⟨(rationalIsometryGeneralSpinMulEquiv U V e A).symm z, ?_, ?_⟩
    · exact hz
    · exact (rationalIsometryGeneralSpinMulEquiv U V e A).apply_symm_apply z

private def rationalIsometryGeneralSpinKernelMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom U A).ker ≃*
      (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V A).ker :=
  ((rationalIsometryGeneralSpinMulEquiv U V e A).subgroupMap
    (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom U A).ker).trans
    (MulEquiv.subgroupCongr
      (rationalIsometryGeneralSpin_similitudeKernel_map U V e A))

/-- The implemented Spin carriers are multiplicatively equivalent under an
arbitrary supplied rational quadratic isometry. -/
def rationalIsometrySpinCandidateMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    U.CliffordSpinCandidateGroup A ≃* V.CliffordSpinCandidateGroup A :=
  (U.rationalIsometrySpinCandidateGeneralSpinKernelMulEquiv A).trans
    ((rationalIsometryGeneralSpinKernelMulEquiv U V e A).trans
      (V.rationalIsometrySpinCandidateGeneralSpinKernelMulEquiv A).symm)

@[simp]
theorem cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : U.CliffordSpinCandidateGroup A) :
    V.cliffordSpinCandidateToCliffordGeneralSpinHom A
        (rationalIsometrySpinCandidateMulEquiv U V e A z) =
      rationalIsometryGeneralSpinMulEquiv U V e A
        (U.cliffordSpinCandidateToCliffordGeneralSpinHom A z) := by
  let kV := V.rationalIsometrySpinCandidateGeneralSpinKernelMulEquiv A
  let t := rationalIsometryGeneralSpinKernelMulEquiv U V e A
      (U.rationalIsometrySpinCandidateGeneralSpinKernelMulEquiv A z)
  have h := congrArg Subtype.val (kV.apply_symm_apply t)
  exact h

/-- Spin transport commutes with extension of the coefficient algebra. -/
theorem rationalIsometrySpinCandidateMulEquiv_naturality
    {A B : Type*} [CommRing A] [Algebra ℚ A]
    [CommRing B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B)
    (z : U.CliffordSpinCandidateGroup A) :
    rationalIsometrySpinCandidateMulEquiv U V e B
        (U.cliffordSpinCandidateGroupMap f z) =
      V.cliffordSpinCandidateGroupMap f
        (rationalIsometrySpinCandidateMulEquiv U V e A z) := by
  apply V.rationalIsometrySpinCandidateEmbedding_injective B
  calc
    V.cliffordSpinCandidateToCliffordGeneralSpinHom B
          (rationalIsometrySpinCandidateMulEquiv U V e B
            (U.cliffordSpinCandidateGroupMap f z)) =
        rationalIsometryGeneralSpinIntrinsicPoint U V e B
          (U.cliffordSpinCandidateToCliffordGeneralSpinHom B
            (U.cliffordSpinCandidateGroupMap f z)) :=
      cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv
        U V e B _
    _ = rationalIsometryGeneralSpinIntrinsicPoint U V e B
          (CliffordGeneralSpinIntrinsicPoint.mapGroupHom U f
            (U.cliffordSpinCandidateToCliffordGeneralSpinHom A z)) := by
      rw [U.cliffordSpinCandidateToCliffordGeneralSpinHom_naturality]
    _ = CliffordGeneralSpinIntrinsicPoint.mapGroupHom V f
          (rationalIsometryGeneralSpinIntrinsicPoint U V e A
            (U.cliffordSpinCandidateToCliffordGeneralSpinHom A z)) :=
      rationalIsometryGeneralSpinIntrinsicPoint_naturality U V e f _
    _ = CliffordGeneralSpinIntrinsicPoint.mapGroupHom V f
          (V.cliffordSpinCandidateToCliffordGeneralSpinHom A
            (rationalIsometrySpinCandidateMulEquiv U V e A z)) := by
      rw [cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv]
      rfl
    _ = V.cliffordSpinCandidateToCliffordGeneralSpinHom B
          (V.cliffordSpinCandidateGroupMap f
            (rationalIsometrySpinCandidateMulEquiv U V e A z)) :=
      V.cliffordSpinCandidateToCliffordGeneralSpinHom_naturality A f _

/-! ## Rational diagonals and adelic quotient carriers -/

/-- Generic `GSpin` transport commutes with the rational diagonal into the
full adeles. -/
theorem rationalIsometryGeneralSpinFullAdelic_diagonal_commutes
    (z : U.RationalCliffordGeneralSpinGroup) :
    rationalIsometryGeneralSpinMulEquiv U V e RationalAdele
        (U.rationalCliffordGeneralSpinFullAdelicDiagonalHom z) =
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
        (rationalIsometryGeneralSpinMulEquiv U V e ℚ z) := by
  exact rationalIsometryGeneralSpinIntrinsicPoint_naturality U V e
    (Algebra.ofId ℚ RationalAdele) z

/-- Generic `GSpin` transport maps the rational adelic diagonal subgroup
exactly. -/
theorem rationalIsometryGeneralSpinFullAdelic_diagonalSubgroup_map :
    U.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup.map
        (rationalIsometryGeneralSpinMulEquiv U V e RationalAdele).toMonoidHom =
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup := by
  ext z
  simp only [rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
    Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, ⟨q, rfl⟩, rfl⟩
    exact ⟨rationalIsometryGeneralSpinMulEquiv U V e ℚ q,
      (rationalIsometryGeneralSpinFullAdelic_diagonal_commutes U V e q).symm⟩
  · rintro ⟨q, rfl⟩
    let q' := (rationalIsometryGeneralSpinMulEquiv U V e ℚ).symm q
    refine ⟨U.rationalCliffordGeneralSpinFullAdelicDiagonalHom q',
      ⟨q', rfl⟩, ?_⟩
    exact (rationalIsometryGeneralSpinFullAdelic_diagonal_commutes U V e q').trans
      (congrArg V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
        ((rationalIsometryGeneralSpinMulEquiv U V e ℚ).apply_symm_apply q))

/-- Generic Spin transport commutes with the rational diagonal into the full
adeles. -/
theorem rationalIsometrySpinCandidateFullAdelic_diagonal_commutes
    (z : U.RationalCliffordSpinCandidateGroup) :
    rationalIsometrySpinCandidateMulEquiv U V e RationalAdele
        (U.rationalCliffordSpinCandidateFullAdelicDiagonalHom z) =
      V.rationalCliffordSpinCandidateFullAdelicDiagonalHom
        (rationalIsometrySpinCandidateMulEquiv U V e ℚ z) := by
  exact rationalIsometrySpinCandidateMulEquiv_naturality U V e
    (Algebra.ofId ℚ RationalAdele) z

/-- Generic Spin transport maps the rational adelic diagonal subgroup
exactly. -/
theorem rationalIsometrySpinCandidateFullAdelic_diagonalSubgroup_map :
    U.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup.map
        (rationalIsometrySpinCandidateMulEquiv U V e RationalAdele).toMonoidHom =
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup := by
  ext z
  simp only [rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
    Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, ⟨q, rfl⟩, rfl⟩
    exact ⟨rationalIsometrySpinCandidateMulEquiv U V e ℚ q,
      (rationalIsometrySpinCandidateFullAdelic_diagonal_commutes U V e q).symm⟩
  · rintro ⟨q, rfl⟩
    let q' := (rationalIsometrySpinCandidateMulEquiv U V e ℚ).symm q
    refine ⟨U.rationalCliffordSpinCandidateFullAdelicDiagonalHom q',
      ⟨q', rfl⟩, ?_⟩
    exact (rationalIsometrySpinCandidateFullAdelic_diagonal_commutes U V e q').trans
      (congrArg V.rationalCliffordSpinCandidateFullAdelicDiagonalHom
        ((rationalIsometrySpinCandidateMulEquiv U V e ℚ).apply_symm_apply q))

private def rationalIsometryLeftCosetSetEquivOfMulEquiv
    {G H : Type*} [Group G] [Group H]
    (E : G ≃* H) (Gamma : Subgroup G) (Delta : Subgroup H)
    (hmap : Gamma.map E.toMonoidHom = Delta) :
    leftCosetSet Gamma ≃ leftCosetSet Delta where
  toFun :=
    Quot.map E (by
      intro g h hgh
      rcases hgh with ⟨gamma, rfl⟩
      have hgamma : E (gamma : G) ∈ Delta := by
        rw [← hmap]
        exact ⟨gamma, gamma.property, rfl⟩
      exact ⟨⟨E (gamma : G), hgamma⟩, by simp⟩)
  invFun :=
    Quot.map E.symm (by
      intro g h hgh
      rcases hgh with ⟨delta, rfl⟩
      have hdelta : (delta : H) ∈ Gamma.map E.toMonoidHom := by
        rw [hmap]
        exact delta.property
      rcases hdelta with ⟨gamma, hgamma, heq⟩
      exact ⟨⟨gamma, hgamma⟩, by simp [← heq]⟩)
  left_inv := by
    intro C
    refine Quot.inductionOn C ?_
    intro g
    change Quot.mk (leftCosetSetoid Gamma) (E.symm (E g)) =
      Quot.mk (leftCosetSetoid Gamma) g
    rw [E.symm_apply_apply]
  right_inv := by
    intro C
    refine Quot.inductionOn C ?_
    intro g
    change Quot.mk (leftCosetSetoid Delta) (E (E.symm g)) =
      Quot.mk (leftCosetSetoid Delta) g
    rw [E.apply_symm_apply]

/-- The arbitrary rational isometry descends to the existing adelic
`GSpin(ℚ) \\ GSpin(𝔸)` carrier. -/
def rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv :
    U.FullAdelicCliffordGeneralSpinLeftQuotient ≃
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  rationalIsometryLeftCosetSetEquivOfMulEquiv
    (rationalIsometryGeneralSpinMulEquiv U V e RationalAdele)
    U.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
    (rationalIsometryGeneralSpinFullAdelic_diagonalSubgroup_map U V e)

@[simp]
theorem rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv_mk
    (g : U.FullAdelicCliffordGeneralSpinGroup) :
    rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv U V e
        (U.fullAdelicCliffordGeneralSpinLeftQuotientMap g) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (rationalIsometryGeneralSpinMulEquiv U V e RationalAdele g) :=
  rfl

/-- The arbitrary rational isometry descends to the existing adelic
`Spin(ℚ) \\ Spin(𝔸)` carrier. -/
def rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv :
    U.FullAdelicCliffordSpinCandidateLeftQuotient ≃
      V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  rationalIsometryLeftCosetSetEquivOfMulEquiv
    (rationalIsometrySpinCandidateMulEquiv U V e RationalAdele)
    U.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
    (rationalIsometrySpinCandidateFullAdelic_diagonalSubgroup_map U V e)

@[simp]
theorem rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv_mk
    (g : U.FullAdelicCliffordSpinCandidateGroup) :
    rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv U V e
        (U.fullAdelicCliffordSpinCandidateLeftQuotientMap g) =
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap
        (rationalIsometrySpinCandidateMulEquiv U V e RationalAdele g) :=
  rfl

/-- The descended Spin and `GSpin` quotient maps commute literally. -/
theorem rationalIsometrySpinCandidateFullAdelicLeftQuotientToGeneralSpin_commutes
    (q : U.FullAdelicCliffordSpinCandidateLeftQuotient) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
        (rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv U V e q) =
      rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv U V e
        (U.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin q) := by
  induction q using Quot.inductionOn with
  | _ z =>
      change V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
          (rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv U V e
            (U.fullAdelicCliffordSpinCandidateLeftQuotientMap z)) =
        rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv U V e
          (U.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
            (U.fullAdelicCliffordSpinCandidateLeftQuotientMap z))
      rw [U.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_mk,
        rationalIsometryGeneralSpinFullAdelicLeftQuotientEquiv_mk,
        rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv_mk,
        V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_mk]
      apply congrArg V.fullAdelicCliffordGeneralSpinLeftQuotientMap
      exact
        cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv
          U V e RationalAdele z

end RationalQuadraticSpaceMatrix

end
