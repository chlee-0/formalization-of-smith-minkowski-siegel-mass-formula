import SMSFormula.RationalCliffordSpinBlockIntrinsicPoint
import SMSFormula.RationalCliffordGeneralSpinNaturality

/-!
# Intrinsic general-Spin points on an orthogonal-complement block

The complement Clifford map carries intrinsic general-Spin points into the
nonsingular block extension.  It preserves the similitude unit, induces the
existing fixed-last-coordinate special-orthogonal action, and is natural over
all commutative rational algebras.

No injectivity or exact stabilizer-range statement is asserted here.
-/

noncomputable section

open CliffordAlgebra

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

@[simp]
theorem nonisotropicLastComplementCoordinateCliffordMap_algebraMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (r : A) :
    W.nonisotropicLastComplementCoordinateCliffordMap a ha A
        (algebraMap A (W.cliffordCoordinateBaseChangeAlgebra A) r) =
      algebraMap A
        ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)
        r := by
  apply (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A |>.injective
  rw [commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap]
  rw [(W.commutativeTensorCliffordEquiv A).commutes r,
    ((W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A).commutes r]
  exact (W.nonisotropicLastComplementCliffordMap a ha A).commutes r

/-- The Clifford unit obtained by mapping a general-Spin unit through the
complement Clifford map. -/
def nonisotropicLastComplementGeneralSpinCliffordUnit
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)ˣ :=
  Units.map
    (W.nonisotropicLastComplementCoordinateCliffordMap a ha A).toMonoidHom
    x.cliffordUnit

@[simp]
theorem coe_nonisotropicLastComplementGeneralSpinCliffordUnit
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementGeneralSpinCliffordUnit a ha A x :
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) =
      W.nonisotropicLastComplementCoordinateCliffordMap a ha A
        (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A) :=
  rfl

/-- The fixed-last-coordinate special-orthogonal matrix attached to a mapped
general-Spin point. -/
def nonisotropicLastComplementGeneralSpinMatrixPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixPoint A :=
  (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixPointOfGroup A
    (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A x.matrixGroup)

@[simp]
theorem nonisotropicLastComplementGeneralSpinMatrixPoint_coe
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementGeneralSpinMatrixPoint a ha A x).1 =
      fixLastBlockMatrix x.matrixPoint.1 := by
  change fixLastBlockMatrix x.matrixGroup.1.1.1 =
    fixLastBlockMatrix x.matrixPoint.1
  rw [x.matrixGroup_coe]

theorem nonisotropicLastComplementGeneralSpin_vectorGraph_castSucc
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) (i : Fin n) :
    let y := W.nonisotropicLastComplementGeneralSpinCliffordUnit a ha A x
    (y : (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) *
          (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A
            i.castSucc *
        ((y⁻¹ : ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
          (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) =
      ∑ j, (W.nonisotropicLastComplementGeneralSpinMatrixPoint a ha A x).1
          j i.castSucc •
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A j := by
  dsimp only
  change
    W.nonisotropicLastComplementCoordinateCliffordMap a ha A
          (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A) *
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A
          i.castSucc *
      W.nonisotropicLastComplementCoordinateCliffordMap a ha A
          (((x.cliffordUnit⁻¹ :
            (W.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
              W.cliffordCoordinateBaseChangeAlgebra A)) = _
  rw [← W.nonisotropicLastComplementCoordinateCliffordMap_vector a ha A i,
    ← map_mul, ← map_mul, x.vectorGraph]
  rw [← cliffordCoordinateBaseChangeVectorOfCoordinates]
  rw [W.nonisotropicLastComplementCoordinateCliffordMap_vectorOfCoordinates]
  rw [← cliffordCoordinateBaseChangeVectorOfCoordinates]
  congr 1
  funext j
  cases j using Fin.lastCases with
  | last =>
      rw [W.nonisotropicLastComplementGeneralSpinMatrixPoint_coe]
      simp [fixLastBlockMatrix]
  | cast j =>
      rw [W.nonisotropicLastComplementGeneralSpinMatrixPoint_coe]
      simp [fixLastBlockMatrix]

theorem nonisotropicLastComplementGeneralSpin_vectorGraph_last
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    let y := W.nonisotropicLastComplementGeneralSpinCliffordUnit a ha A x
    (y : (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) *
          (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A
            (Fin.last n) *
        ((y⁻¹ : ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
          (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) =
      ∑ j, (W.nonisotropicLastComplementGeneralSpinMatrixPoint a ha A x).1
          j (Fin.last n) •
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A j := by
  dsimp only
  change
    W.nonisotropicLastComplementCoordinateCliffordMap a ha A
          (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A) *
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A
          (Fin.last n) *
      W.nonisotropicLastComplementCoordinateCliffordMap a ha A
          (((x.cliffordUnit⁻¹ :
            (W.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
              W.cliffordCoordinateBaseChangeAlgebra A)) = _
  apply (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A |>.injective
  simp only [map_mul,
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv_baseChangeVector,
    commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap,
    map_sum, map_smul]
  let z := W.nonisotropicLastComplementCliffordMap a ha A
    (W.commutativeTensorCliffordEquiv A
      (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A))
  let zinv := W.nonisotropicLastComplementCliffordMap a ha A
    (W.commutativeTensorCliffordEquiv A
      (((x.cliffordUnit⁻¹ :
        (W.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
          W.cliffordCoordinateBaseChangeAlgebra A)))
  let e := CliffordAlgebra.ι
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
    (lastCoordinateVector (n := n))
  have heq :
      CliffordAlgebra.ι
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
          (Pi.single (Fin.last n) 1) = e := by
    congr 1
  have hxEven :
      W.commutativeTensorCliffordEquiv A
          (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A) ∈
        CliffordAlgebra.even (W.commutativeScalarExtensionQuadraticForm A) :=
    (W.commutativeTensorCliffordEquiv_mem_even_iff A _).2 x.involute_eq
  have hcomm : Commute z e :=
    W.nonisotropicLastComplementCliffordMap_commute_lastGenerator a ha A
      (W.commutativeTensorCliffordEquiv A
        (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A)) hxEven
  have hunit :
      (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A) *
          (((x.cliffordUnit⁻¹ :
            (W.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
              W.cliffordCoordinateBaseChangeAlgebra A)) = 1 :=
    congrArg Units.val (mul_inv_cancel x.cliffordUnit)
  have hnorm : z * zinv = 1 := by
    rw [← map_mul, ← map_mul, hunit, map_one, map_one]
  change z * _ * zinv = _
  rw [heq]
  calc
    z * e * zinv = e * (z * zinv) := by
      rw [← mul_assoc, hcomm.eq, mul_assoc]
    _ = e := by rw [hnorm, mul_one]
    _ = ∑ j, (W.nonisotropicLastComplementGeneralSpinMatrixPoint a ha A x).1
          j (Fin.last n) •
          CliffordAlgebra.ι
            ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
            (Pi.single j 1) := by
      rw [W.nonisotropicLastComplementGeneralSpinMatrixPoint_coe,
        Fin.sum_univ_castSucc]
      simp [e, fixLastBlockMatrix]
      exact heq.symm

theorem nonisotropicLastComplementGeneralSpin_vectorGraph
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) (i : Fin (n + 1)) :
    let y := W.nonisotropicLastComplementGeneralSpinCliffordUnit a ha A x
    (y : (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) *
          (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A i *
        ((y⁻¹ : ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
          (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) =
      ∑ j, (W.nonisotropicLastComplementGeneralSpinMatrixPoint a ha A x).1 j i •
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A j := by
  cases i using Fin.lastCases with
  | last => exact W.nonisotropicLastComplementGeneralSpin_vectorGraph_last a ha A x
  | cast i => exact W.nonisotropicLastComplementGeneralSpin_vectorGraph_castSucc a ha A x i

/-- A lower-rank intrinsic general-Spin point embedded into the nonsingular
block extension. -/
def nonisotropicLastComplementGeneralSpinPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A where
  cliffordUnit :=
    W.nonisotropicLastComplementGeneralSpinCliffordUnit a ha A x
  similitude := x.similitude
  matrixPoint := W.nonisotropicLastComplementGeneralSpinMatrixPoint a ha A x
  involute_eq := by
    change
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeInvolute A
          (W.nonisotropicLastComplementCoordinateCliffordMap a ha A
            (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A)) =
        W.nonisotropicLastComplementCoordinateCliffordMap a ha A
          (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A)
    rw [← W.nonisotropicLastComplementCoordinateCliffordMap_involute,
      x.involute_eq]
  mul_reverse_eq := by
    change
      W.nonisotropicLastComplementCoordinateCliffordMap a ha A
            (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A) *
          (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeReverse A
            (W.nonisotropicLastComplementCoordinateCliffordMap a ha A
              (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A)) =
        algebraMap A
          ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)
          x.similitude
    rw [← W.nonisotropicLastComplementCoordinateCliffordMap_reverse,
      ← map_mul, x.mul_reverse_eq,
      W.nonisotropicLastComplementCoordinateCliffordMap_algebraMap]
  vectorGraph :=
    W.nonisotropicLastComplementGeneralSpin_vectorGraph a ha A x

@[simp]
theorem nonisotropicLastComplementGeneralSpinPoint_cliffordUnit
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementGeneralSpinPoint a ha A x).cliffordUnit =
      W.nonisotropicLastComplementGeneralSpinCliffordUnit a ha A x :=
  rfl

@[simp]
theorem nonisotropicLastComplementGeneralSpinPoint_similitude
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementGeneralSpinPoint a ha A x).similitude =
      x.similitude :=
  rfl

@[simp]
theorem nonisotropicLastComplementGeneralSpinPoint_matrixPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementGeneralSpinPoint a ha A x).matrixPoint =
      W.nonisotropicLastComplementGeneralSpinMatrixPoint a ha A x :=
  rfl

@[simp]
theorem nonisotropicLastComplementGeneralSpinPoint_matrixGroup
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementGeneralSpinPoint a ha A x).matrixGroup =
      W.nonisotropicLastCoordinateFiberEmbedGroup a ha A x.matrixGroup := by
  exact (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixPointEquivGroup A
    |>.apply_symm_apply
      (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A x.matrixGroup)

/-- The intrinsic general-Spin block embedding as a group homomorphism. -/
def nonisotropicLastComplementGeneralSpinPointHom
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.CliffordGeneralSpinIntrinsicPoint A →*
      (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A where
  toFun := W.nonisotropicLastComplementGeneralSpinPoint a ha A
  map_one' := by
    apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit
    apply Units.ext
    simp [nonisotropicLastComplementGeneralSpinPoint,
      nonisotropicLastComplementGeneralSpinCliffordUnit]
  map_mul' x y := by
    apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit
    apply Units.ext
    simp [nonisotropicLastComplementGeneralSpinPoint,
      nonisotropicLastComplementGeneralSpinCliffordUnit]

/-- The block general-Spin homomorphism preserves similitude exactly. -/
theorem nonisotropicLastComplementGeneralSpinPointHom_similitude
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
        (W.nonisotropicLastExtension a ha) A).comp
        (W.nonisotropicLastComplementGeneralSpinPointHom a ha A) =
      CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom W A := by
  rfl

/-- The represented special-orthogonal action of the block general-Spin
homomorphism is the existing fixed-last-coordinate block embedding. -/
theorem nonisotropicLastComplementGeneralSpinPointHom_toSpecialOrthogonal
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
        (W.nonisotropicLastExtension a ha) A).comp
        (W.nonisotropicLastComplementGeneralSpinPointHom a ha A) =
      (W.nonisotropicLastCoordinateFiberEmbedHom a ha A).comp
        (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom W A) := by
  apply MonoidHom.ext
  intro x
  exact W.nonisotropicLastComplementGeneralSpinPoint_matrixGroup a ha A x

/-- The block general-Spin point map preserves the central scalar inclusion. -/
@[simp]
theorem nonisotropicLastComplementGeneralSpinPoint_ofScalar
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (z : Aˣ) :
    W.nonisotropicLastComplementGeneralSpinPoint a ha A
        (CliffordGeneralSpinIntrinsicPoint.ofScalar W A z) =
      CliffordGeneralSpinIntrinsicPoint.ofScalar
        (W.nonisotropicLastExtension a ha) A z := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit
  apply Units.ext
  exact W.nonisotropicLastComplementCoordinateCliffordMap_algebraMap a ha A z

/-- The block general-Spin point map extends the already constructed intrinsic
Spin block point map. -/
@[simp]
theorem nonisotropicLastComplementGeneralSpinPoint_ofSpin
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    W.nonisotropicLastComplementGeneralSpinPoint a ha A
        (CliffordGeneralSpinIntrinsicPoint.ofSpin W A
          (CliffordSpinIntrinsicPoint.toCandidatePointData W A x)) =
      CliffordGeneralSpinIntrinsicPoint.ofSpin
        (W.nonisotropicLastExtension a ha) A
        (CliffordSpinIntrinsicPoint.toCandidatePointData
          (W.nonisotropicLastExtension a ha) A
          (W.nonisotropicLastComplementSpinPoint a ha A x)) := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit
  apply Units.ext
  rfl

/-- The intrinsic general-Spin block point map commutes with arbitrary scalar
extension. -/
@[simp]
theorem nonisotropicLastComplementGeneralSpinPoint_naturality
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    CliffordGeneralSpinIntrinsicPoint.map (W.nonisotropicLastExtension a ha) f
        (W.nonisotropicLastComplementGeneralSpinPoint a ha A x) =
      W.nonisotropicLastComplementGeneralSpinPoint a ha B
        (CliffordGeneralSpinIntrinsicPoint.map W f x) := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit
  apply Units.ext
  change
    (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeMap f
        (W.nonisotropicLastComplementCoordinateCliffordMap a ha A
          (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A)) =
      W.nonisotropicLastComplementCoordinateCliffordMap a ha B
        (W.cliffordCoordinateBaseChangeMap f
          (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A))
  exact W.nonisotropicLastComplementCoordinateCliffordMap_naturality a ha f _

/-- Naturality of the intrinsic general-Spin block embedding as an equality
of group homomorphisms. -/
theorem nonisotropicLastComplementGeneralSpinPointHom_naturality
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    (CliffordGeneralSpinIntrinsicPoint.mapGroupHom
        (W.nonisotropicLastExtension a ha) f).comp
        (W.nonisotropicLastComplementGeneralSpinPointHom a ha A) =
      (W.nonisotropicLastComplementGeneralSpinPointHom a ha B).comp
        (CliffordGeneralSpinIntrinsicPoint.mapGroupHom W f) := by
  apply MonoidHom.ext
  intro x
  exact W.nonisotropicLastComplementGeneralSpinPoint_naturality a ha f x

end RationalQuadraticSpaceMatrix
