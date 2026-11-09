import SMSFormula.RationalCliffordSpinBlockCliffordEmbedding

/-!
# Intrinsic Spin points on an orthogonal-complement block

The Clifford map induced by the complement inclusion carries intrinsic Spin
points to intrinsic Spin points on the nonsingular block extension.  The
induced special-orthogonal action is the existing fixed-last-coordinate block
embedding, and the construction commutes with scalar extension.

This file constructs only the point map and its represented action.  It does
not identify its range with the full fixed-vector preimage.
-/

noncomputable section

open CliffordAlgebra

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The complement Clifford map in the fixed tensor coordinates used by the
intrinsic Spin carrier. -/
def nonisotropicLastComplementCoordinateCliffordMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.cliffordCoordinateBaseChangeAlgebra A →ₐ[A]
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A :=
  (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A |>.symm.toAlgHom.comp
    ((W.nonisotropicLastComplementCliffordMap a ha A).comp
      (W.commutativeTensorCliffordEquiv A).toAlgHom)

@[simp]
theorem commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.cliffordCoordinateBaseChangeAlgebra A) :
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A
        (W.nonisotropicLastComplementCoordinateCliffordMap a ha A x) =
      W.nonisotropicLastComplementCliffordMap a ha A
        (W.commutativeTensorCliffordEquiv A x) := by
  simp [nonisotropicLastComplementCoordinateCliffordMap]

@[simp]
theorem nonisotropicLastComplementCoordinateCliffordMap_involute
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.cliffordCoordinateBaseChangeAlgebra A) :
    W.nonisotropicLastComplementCoordinateCliffordMap a ha A
        (W.cliffordCoordinateBaseChangeInvolute A x) =
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeInvolute A
        (W.nonisotropicLastComplementCoordinateCliffordMap a ha A x) := by
  apply (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A |>.injective
  rw [commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap,
    W.commutativeTensorCliffordEquiv_involute,
    W.nonisotropicLastComplementCliffordMap_involute,
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv_involute,
    commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap]

@[simp]
theorem nonisotropicLastComplementCoordinateCliffordMap_reverse
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.cliffordCoordinateBaseChangeAlgebra A) :
    W.nonisotropicLastComplementCoordinateCliffordMap a ha A
        (W.cliffordCoordinateBaseChangeReverse A x) =
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeReverse A
        (W.nonisotropicLastComplementCoordinateCliffordMap a ha A x) := by
  apply (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A |>.injective
  rw [commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap,
    W.commutativeTensorCliffordEquiv_reverse,
    W.nonisotropicLastComplementCliffordMap_reverse,
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv_reverse,
    commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap]

@[simp]
theorem nonisotropicLastComplementCoordinateCliffordMap_vectorOfCoordinates
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (v : Fin n → A) :
    W.nonisotropicLastComplementCoordinateCliffordMap a ha A
        (W.cliffordCoordinateBaseChangeVectorOfCoordinates A v) =
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVectorOfCoordinates A
        (nonisotropicLastComplementInclude v) := by
  apply (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A |>.injective
  simp

theorem cliffordCoordinateBaseChangeVectorOfCoordinates_single
    (V : RationalQuadraticSpaceMatrix n)
    (A : Type*) [CommRing A] [Algebra ℚ A] (i : Fin n) :
    V.cliffordCoordinateBaseChangeVectorOfCoordinates A (Pi.single i 1) =
      V.cliffordCoordinateBaseChangeVector A i := by
  simp [cliffordCoordinateBaseChangeVectorOfCoordinates, Pi.single_apply]

@[simp]
theorem nonisotropicLastComplementCoordinateCliffordMap_vector
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (i : Fin n) :
    W.nonisotropicLastComplementCoordinateCliffordMap a ha A
        (W.cliffordCoordinateBaseChangeVector A i) =
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A
        i.castSucc := by
  rw [← W.cliffordCoordinateBaseChangeVectorOfCoordinates_single A i,
    W.nonisotropicLastComplementCoordinateCliffordMap_vectorOfCoordinates]
  rw [← cliffordCoordinateBaseChangeVectorOfCoordinates_single
    (W.nonisotropicLastExtension a ha) A i.castSucc]
  congr 1
  ext j
  cases j using Fin.lastCases <;> simp [Pi.single_apply]

/-- The special-orthogonal matrix point obtained by adjoining a fixed final
coordinate to the action of a lower-rank intrinsic Spin point. -/
def nonisotropicLastComplementSpinMatrixPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixPoint A :=
  (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixPointOfGroup A
    (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A
      (W.cliffordSpinIntrinsicPointToSpecialOrthogonalGroup A x))

@[simp]
theorem nonisotropicLastComplementSpinMatrixPoint_coe
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementSpinMatrixPoint a ha A x).1 =
      fixLastBlockMatrix x.matrixPoint.1 := by
  rfl

theorem nonisotropicLastComplementCoordinateCliffordMap_vectorGraph_castSucc
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) (i : Fin n) :
    let y := W.nonisotropicLastComplementCoordinateCliffordMap a ha A x.1
    y * (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A
          i.castSucc *
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeReverse A y =
      ∑ j, (W.nonisotropicLastComplementSpinMatrixPoint a ha A x).1 j i.castSucc •
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A j := by
  dsimp only
  rw [← W.nonisotropicLastComplementCoordinateCliffordMap_vector a ha A i,
    ← W.nonisotropicLastComplementCoordinateCliffordMap_reverse,
    ← map_mul, ← map_mul, x.vectorGraph]
  rw [← cliffordCoordinateBaseChangeVectorOfCoordinates]
  rw [W.nonisotropicLastComplementCoordinateCliffordMap_vectorOfCoordinates]
  rw [← cliffordCoordinateBaseChangeVectorOfCoordinates]
  congr 1
  funext j
  cases j using Fin.lastCases with
  | last =>
      rw [W.nonisotropicLastComplementSpinMatrixPoint_coe]
      simp [fixLastBlockMatrix]
  | cast j =>
      rw [W.nonisotropicLastComplementSpinMatrixPoint_coe]
      simp [fixLastBlockMatrix]

theorem nonisotropicLastComplementCoordinateCliffordMap_vectorGraph_last
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    let y := W.nonisotropicLastComplementCoordinateCliffordMap a ha A x.1
    y * (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A
          (Fin.last n) *
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeReverse A y =
      ∑ j, (W.nonisotropicLastComplementSpinMatrixPoint a ha A x).1 j (Fin.last n) •
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A j := by
  dsimp only
  apply (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A |>.injective
  simp only [map_mul,
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv_baseChangeVector,
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv_reverse,
    commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap,
    map_sum, map_smul]
  let z := W.nonisotropicLastComplementCliffordMap a ha A
    (W.commutativeTensorCliffordEquiv A x.1)
  let e := CliffordAlgebra.ι
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
    (lastCoordinateVector (n := n))
  have heq :
      CliffordAlgebra.ι
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
          (Pi.single (Fin.last n) 1) = e := by
    congr 1
  have hcomm : Commute z e :=
    W.nonisotropicLastComplementCliffordMap_commute_lastGenerator a ha A
      (W.commutativeTensorCliffordEquiv A x.1) x.commutativeClifford_mem_even
  have hnorm : z * CliffordAlgebra.reverse z = 1 := by
    rw [← W.nonisotropicLastComplementCliffordMap_reverse, ← map_mul,
      x.commutativeClifford_mul_reverse_eq_one, map_one]
  change z * _ * CliffordAlgebra.reverse z = _
  rw [heq]
  calc
    z * e * CliffordAlgebra.reverse z =
        e * (z * CliffordAlgebra.reverse z) := by
          rw [← mul_assoc, hcomm.eq, mul_assoc]
    _ = e := by rw [hnorm, mul_one]
    _ = ∑ j, (W.nonisotropicLastComplementSpinMatrixPoint a ha A x).1 j
          (Fin.last n) •
          CliffordAlgebra.ι
            ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
            (Pi.single j 1) := by
      rw [W.nonisotropicLastComplementSpinMatrixPoint_coe,
        Fin.sum_univ_castSucc]
      simp [e, fixLastBlockMatrix]
      exact heq.symm

theorem nonisotropicLastComplementCoordinateCliffordMap_vectorGraph
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) (i : Fin (n + 1)) :
    let y := W.nonisotropicLastComplementCoordinateCliffordMap a ha A x.1
    y * (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A i *
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeReverse A y =
      ∑ j, (W.nonisotropicLastComplementSpinMatrixPoint a ha A x).1 j i •
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A j := by
  cases i using Fin.lastCases with
  | last => exact W.nonisotropicLastComplementCoordinateCliffordMap_vectorGraph_last a ha A x
  | cast i => exact W.nonisotropicLastComplementCoordinateCliffordMap_vectorGraph_castSucc a ha A x i

/-- A lower-rank intrinsic Spin point embedded into the nonsingular block
extension. -/
def nonisotropicLastComplementSpinPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A := by
  let y := W.nonisotropicLastComplementCoordinateCliffordMap a ha A x.1
  refine ⟨y, ?_, ?_, ⟨W.nonisotropicLastComplementSpinMatrixPoint a ha A x, ?_⟩⟩
  · dsimp [y]
    rw [← W.nonisotropicLastComplementCoordinateCliffordMap_involute,
      x.involute_eq]
  · dsimp [y]
    rw [← W.nonisotropicLastComplementCoordinateCliffordMap_reverse,
      ← map_mul, x.mul_reverse_eq_one, map_one]
  · exact W.nonisotropicLastComplementCoordinateCliffordMap_vectorGraph a ha A x

@[simp]
theorem nonisotropicLastComplementSpinPoint_coe
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementSpinPoint a ha A x).1 =
      W.nonisotropicLastComplementCoordinateCliffordMap a ha A x.1 :=
  rfl

@[simp]
theorem nonisotropicLastComplementSpinPoint_matrixPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    (W.nonisotropicLastComplementSpinPoint a ha A x).matrixPoint =
      W.nonisotropicLastComplementSpinMatrixPoint a ha A x := by
  apply CliffordSpinIntrinsicPoint.matrixPoint_eq
  exact W.nonisotropicLastComplementCoordinateCliffordMap_vectorGraph a ha A x

/-- The intrinsic Spin block embedding as a group homomorphism. -/
def nonisotropicLastComplementSpinPointHom
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.CliffordSpinIntrinsicPoint A →*
      (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A where
  toFun := W.nonisotropicLastComplementSpinPoint a ha A
  map_one' := by
    apply CliffordSpinIntrinsicPoint.ext
    simp [nonisotropicLastComplementSpinPoint]
  map_mul' x y := by
    apply CliffordSpinIntrinsicPoint.ext
    simp [nonisotropicLastComplementSpinPoint]

/-- The represented special-orthogonal action of the intrinsic Spin block
embedding is the existing fixed-last-coordinate block embedding. -/
theorem nonisotropicLastComplementSpinPointHom_toSpecialOrthogonal
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    ((W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointToSpecialOrthogonalGroup A).comp
        (W.nonisotropicLastComplementSpinPointHom a ha A) =
      (W.nonisotropicLastCoordinateFiberEmbedHom a ha A).comp
        (W.cliffordSpinIntrinsicPointToSpecialOrthogonalGroup A) := by
  apply MonoidHom.ext
  intro x
  change
    (W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointToSpecialOrthogonalGroup A
        (W.nonisotropicLastComplementSpinPoint a ha A x) =
      W.nonisotropicLastCoordinateFiberEmbedGroup a ha A
        (W.cliffordSpinIntrinsicPointToSpecialOrthogonalGroup A x)
  rw [(W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointToSpecialOrthogonalGroup_apply,
    W.nonisotropicLastComplementSpinPoint_matrixPoint]
  exact (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixPointEquivGroup A
    |>.apply_symm_apply
      (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A
        (W.cliffordSpinIntrinsicPointToSpecialOrthogonalGroup A x))

/-- The coordinate complement Clifford map commutes with arbitrary scalar
extension of commutative rational algebras. -/
theorem nonisotropicLastComplementCoordinateCliffordMap_naturality
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x : W.cliffordCoordinateBaseChangeAlgebra A) :
    (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeMap f
        (W.nonisotropicLastComplementCoordinateCliffordMap a ha A x) =
      W.nonisotropicLastComplementCoordinateCliffordMap a ha B
        (W.cliffordCoordinateBaseChangeMap f x) := by
  apply (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv B |>.injective
  rw [← commutativeCliffordAlgebraBaseChangeHom_apply_tensorEquiv
      (W.nonisotropicLastExtension a ha),
    commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap,
    W.nonisotropicLastComplementCliffordMap_naturality,
    W.commutativeCliffordAlgebraBaseChangeHom_apply_tensorEquiv,
    commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap]

/-- The intrinsic Spin block point map commutes with arbitrary scalar
extension. -/
@[simp]
theorem nonisotropicLastComplementSpinPoint_naturality
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x : W.CliffordSpinIntrinsicPoint A) :
    (W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointMap f
        (W.nonisotropicLastComplementSpinPoint a ha A x) =
      W.nonisotropicLastComplementSpinPoint a ha B
        (W.cliffordSpinIntrinsicPointMap f x) := by
  apply CliffordSpinIntrinsicPoint.ext
  simp only [cliffordSpinIntrinsicPointMap_coe,
    nonisotropicLastComplementSpinPoint_coe]
  rw [W.nonisotropicLastComplementCoordinateCliffordMap_naturality]

/-- Naturality of the intrinsic Spin block embedding as an equality of group
homomorphisms. -/
theorem nonisotropicLastComplementSpinPointHom_naturality
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    ((W.nonisotropicLastExtension a ha).cliffordSpinIntrinsicPointMap f).comp
        (W.nonisotropicLastComplementSpinPointHom a ha A) =
      (W.nonisotropicLastComplementSpinPointHom a ha B).comp
        (W.cliffordSpinIntrinsicPointMap f) := by
  apply MonoidHom.ext
  intro x
  exact W.nonisotropicLastComplementSpinPoint_naturality a ha f x

end RationalQuadraticSpaceMatrix
