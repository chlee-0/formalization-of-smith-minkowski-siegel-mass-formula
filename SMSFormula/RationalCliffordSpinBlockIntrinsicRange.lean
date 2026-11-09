import SMSFormula.RationalCliffordSpinBlockCentralizer

/-!
# Exact intrinsic Spin range on a nonisotropic block

This file reconstructs a lower-rank intrinsic Spin point from an intrinsic
Spin point on `W orthogonal_sum <a>` whose represented action fixes the added
coordinate.  It uses the exact even-Clifford centralizer theorem and proves
only the Spin point range; the analogous GSpin range is left to the next
layer.
-/

noncomputable section

open CliffordAlgebra

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Intrinsic block-Spin points whose represented action fixes the added
coordinate. -/
def IsNonisotropicLastBlockSpinFixedPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A) : Prop :=
  FixesLastCoordinate z.matrixPoint.1

/-- Intrinsic block-Spin points whose scalar-extended Clifford element lies
in the centralizer of the added generator.  Keeping this predicate named
prevents the large Clifford expression from being normalized at every range
theorem declaration. -/
def IsNonisotropicLastBlockSpinCliffordCentralizerPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A) : Prop :=
  Commute
    ((W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A z.1)
    (CliffordAlgebra.ι
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
      (lastCoordinateVector (n := n)))

/-- The final-coordinate instance of the intrinsic vector graph.  It is a named
definition so that proofs never ask elaboration to infer its large dependent type. -/
def HasNonisotropicLastBlockSpinLastVectorGraph
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A) : Prop :=
  z.1 *
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A
          (Fin.last n) *
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeReverse A z.1 =
    ∑ j, z.matrixPoint.1 j (Fin.last n) •
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A j

/-- Exact even complement-Clifford preimage carried by a block-Spin point. -/
def HasUniqueNonisotropicLastComplementEvenCliffordPreimage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A) : Prop :=
  ∃! x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A),
    x ∈ CliffordAlgebra.even (W.commutativeScalarExtensionQuadraticForm A) ∧
      W.nonisotropicLastComplementCliffordMap a ha A x =
        (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A z.1

/-- Exact intrinsic Spin preimage under the complement block embedding. -/
def HasUniqueNonisotropicLastComplementSpinPreimage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A) : Prop :=
  ∃! x : W.CliffordSpinIntrinsicPoint A,
    W.nonisotropicLastComplementSpinPoint a ha A x = z

/-- If the represented action of an intrinsic block-Spin point fixes the
added coordinate, its scalar-extended Clifford element commutes with the
added Clifford generator. -/
theorem nonisotropicLastBlockSpin_commutativeClifford_commute_lastGenerator_of_fixes
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A)
    (hzFixes : W.IsNonisotropicLastBlockSpinFixedPoint a ha A z) :
    W.IsNonisotropicLastBlockSpinCliffordCentralizerPoint a ha A z := by
  let QB :=
    (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A
  let Z : CliffordAlgebra QB :=
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A z.1
  let e : CliffordAlgebra QB :=
    CliffordAlgebra.ι QB (lastCoordinateVector (n := n))
  change FixesLastCoordinate z.matrixPoint.1 at hzFixes
  change Commute Z e
  have hgraphCoordinate :
      W.HasNonisotropicLastBlockSpinLastVectorGraph a ha A z := by
    exact Classical.choose_spec z.2.2.2 (Fin.last n)
  unfold HasNonisotropicLastBlockSpinLastVectorGraph at hgraphCoordinate
  have hgraph := congrArg
    ((W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A)
    hgraphCoordinate
  simp only [map_mul,
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv_baseChangeVector,
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv_reverse,
    map_sum, map_smul] at hgraph
  have heq :
      CliffordAlgebra.ι QB (Pi.single (Fin.last n) 1) = e := by
    rfl
  have hcol := (fixesLastCoordinate_iff_column z.matrixPoint.1).1 hzFixes
  have hrhs :
      (∑ j, z.matrixPoint.1 j (Fin.last n) •
        CliffordAlgebra.ι QB (Pi.single j 1)) = e := by
    rw [Fin.sum_univ_castSucc]
    simp_rw [hcol]
    simp [e, lastCoordinateVector]
  have hconj : Z * e * CliffordAlgebra.reverse Z = e := by
    change Z * CliffordAlgebra.ι QB (Pi.single (Fin.last n) 1) *
        CliffordAlgebra.reverse Z = _ at hgraph
    rw [heq, hrhs] at hgraph
    exact hgraph
  have hreverseCoordinate :
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeReverse A z.1 *
          z.1 = 1 :=
    (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChange_reverse_mul_eq_one_of_mul_reverse_eq_one
        A z.1 z.mul_reverse_eq_one
  have hreverseMul := congrArg
    ((W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A)
    hreverseCoordinate
  simp only [map_mul,
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv_reverse,
    map_one] at hreverseMul
  show Z * e = e * Z
  calc
    Z * e = (Z * e) * (CliffordAlgebra.reverse Z * Z) := by
      rw [hreverseMul, mul_one]
    _ = (Z * e * CliffordAlgebra.reverse Z) * Z := by
      simp only [mul_assoc]
    _ = e * Z := by rw [hconj]

/-- A fixed-last-vector intrinsic block-Spin point has a unique even
complement-Clifford preimage. -/
theorem existsUnique_nonisotropicLastComplement_evenCliffordPreimage_of_fixes
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A)
    (hzFixes : W.IsNonisotropicLastBlockSpinFixedPoint a ha A z) :
    W.HasUniqueNonisotropicLastComplementEvenCliffordPreimage a ha A z := by
  unfold HasUniqueNonisotropicLastComplementEvenCliffordPreimage
  apply W.existsUnique_even_complementCliffordMap_of_commute_lastGenerator
    a ha A
  · exact z.commutativeClifford_mem_even
  · have hcomm :=
      W.nonisotropicLastBlockSpin_commutativeClifford_commute_lastGenerator_of_fixes
        a ha A z hzFixes
    exact hcomm

/-- Every intrinsic block-Spin point fixing the added vector is in the unique
image of the intrinsic complement Spin embedding. -/
theorem existsUnique_nonisotropicLastComplementSpinPreimage_of_fixes
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A)
    (hzFixes : W.IsNonisotropicLastBlockSpinFixedPoint a ha A z) :
    W.HasUniqueNonisotropicLastComplementSpinPreimage a ha A z := by
  unfold HasUniqueNonisotropicLastComplementSpinPreimage
  have hpre :=
    W.existsUnique_nonisotropicLastComplement_evenCliffordPreimage_of_fixes
      a ha A z hzFixes
  unfold HasUniqueNonisotropicLastComplementEvenCliffordPreimage at hpre
  rcases hpre with ⟨xOrd, ⟨_, hxMap⟩, _⟩
  let xCoord : W.cliffordCoordinateBaseChangeAlgebra A :=
    (W.commutativeTensorCliffordEquiv A).symm xOrd
  have hxCoordMap :
      W.nonisotropicLastComplementCoordinateCliffordMap a ha A xCoord = z.1 := by
    apply (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A |>.injective
    rw [W.commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap]
    dsimp only [xCoord]
    rw [(W.commutativeTensorCliffordEquiv A).apply_symm_apply, hxMap]
  have hxInvolute : W.cliffordCoordinateBaseChangeInvolute A xCoord = xCoord := by
    apply W.nonisotropicLastComplementCoordinateCliffordMap_injective a ha A
    rw [W.nonisotropicLastComplementCoordinateCliffordMap_involute,
      hxCoordMap, z.involute_eq]
  have hxNorm :
      xCoord * W.cliffordCoordinateBaseChangeReverse A xCoord = 1 := by
    apply W.nonisotropicLastComplementCoordinateCliffordMap_injective a ha A
    rw [map_mul, W.nonisotropicLastComplementCoordinateCliffordMap_reverse,
      hxCoordMap, z.mul_reverse_eq_one, map_one]
  let g := (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixPointToGroup
    A z.matrixPoint
  have hgMatrix : g.1.1.1 = z.matrixPoint.1 := by
    simp [g, specialOrthogonalMatrixPointToGroup]
  have hg : g ∈ W.nonisotropicLastCoordinateFiber a ha A := by
    change FixesLastCoordinate g.1.1.1
    rw [hgMatrix]
    exact hzFixes
  let lowerG := W.nonisotropicLastCoordinateFiberExtract a ha A ⟨g, hg⟩
  let M : W.specialOrthogonalMatrixPoint A :=
    W.specialOrthogonalMatrixPointOfGroup A lowerG
  have hM : M.1 = upperLeftBlock z.matrixPoint.1 := by
    change upperLeftBlock g.1.1.1 = upperLeftBlock z.matrixPoint.1
    rw [hgMatrix]
  have hMatrix : z.matrixPoint.1 = fixLastBlockMatrix M.1 := by
    calc
      z.matrixPoint.1 = g.1.1.1 := hgMatrix.symm
      _ = fixLastBlockMatrix (upperLeftBlock g.1.1.1) :=
        W.nonisotropicLastCoordinateFiber_eq_fixLastBlockMatrix a ha A g hg
      _ = fixLastBlockMatrix M.1 := by rw [hgMatrix, ← hM]
  have hxGraph (i : Fin n) :
      xCoord * W.cliffordCoordinateBaseChangeVector A i *
          W.cliffordCoordinateBaseChangeReverse A xCoord =
        ∑ j, M.1 j i • W.cliffordCoordinateBaseChangeVector A j := by
    apply W.nonisotropicLastComplementCoordinateCliffordMap_injective a ha A
    simp only [map_mul,
      W.nonisotropicLastComplementCoordinateCliffordMap_vector,
      W.nonisotropicLastComplementCoordinateCliffordMap_reverse,
      map_sum, map_smul, hxCoordMap]
    have hzGraph := Classical.choose_spec z.2.2.2 i.castSucc
    change z.1 *
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A i.castSucc *
          (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeReverse A z.1 =
      ∑ j, z.matrixPoint.1 j i.castSucc •
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A j
      at hzGraph
    rw [hMatrix, Fin.sum_univ_castSucc] at hzGraph
    simpa [fixLastBlockMatrix] using hzGraph
  let x : W.CliffordSpinIntrinsicPoint A :=
    ⟨xCoord, hxInvolute, hxNorm, ⟨M, hxGraph⟩⟩
  have hxImage : W.nonisotropicLastComplementSpinPoint a ha A x = z := by
    apply CliffordSpinIntrinsicPoint.ext
    exact hxCoordMap
  refine ⟨x, hxImage, ?_⟩
  intro y hy
  apply W.nonisotropicLastComplementSpinPointHom_injective a ha A
  exact hy.trans hxImage.symm

/-- Every embedded complement Spin point fixes the added coordinate. -/
theorem nonisotropicLastComplementSpinPoint_fixesLastCoordinate
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordSpinIntrinsicPoint A) :
    W.IsNonisotropicLastBlockSpinFixedPoint a ha A
      (W.nonisotropicLastComplementSpinPoint a ha A x) := by
  unfold IsNonisotropicLastBlockSpinFixedPoint
  rw [W.nonisotropicLastComplementSpinPoint_matrixPoint,
    W.nonisotropicLastComplementSpinMatrixPoint_coe]
  rw [fixesLastCoordinate_iff_column]
  intro i
  cases i using Fin.lastCases <;> simp [fixLastBlockMatrix]

/-- Exact pointwise range of the intrinsic Spin block embedding. -/
theorem isNonisotropicLastBlockSpinFixedPoint_iff_existsUnique_preimage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A) :
    W.IsNonisotropicLastBlockSpinFixedPoint a ha A z ↔
      W.HasUniqueNonisotropicLastComplementSpinPreimage a ha A z := by
  constructor
  · exact W.existsUnique_nonisotropicLastComplementSpinPreimage_of_fixes
      a ha A z
  · intro hpre
    unfold HasUniqueNonisotropicLastComplementSpinPreimage at hpre
    rcases hpre with ⟨x, hx, _⟩
    rw [← hx]
    exact W.nonisotropicLastComplementSpinPoint_fixesLastCoordinate a ha A x

/-- Set-theoretic image equality for the intrinsic Spin block embedding. -/
theorem range_nonisotropicLastComplementSpinPoint_eq_fixedPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Set.range (W.nonisotropicLastComplementSpinPoint a ha A) =
      {z | W.IsNonisotropicLastBlockSpinFixedPoint a ha A z} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact W.nonisotropicLastComplementSpinPoint_fixesLastCoordinate a ha A x
  · intro hz
    have hpre :=
      W.existsUnique_nonisotropicLastComplementSpinPreimage_of_fixes
        a ha A z hz
    unfold HasUniqueNonisotropicLastComplementSpinPreimage at hpre
    rcases hpre with ⟨x, hx, _⟩
    exact ⟨x, hx⟩

end RationalQuadraticSpaceMatrix
