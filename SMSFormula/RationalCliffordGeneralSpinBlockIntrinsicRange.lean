import SMSFormula.RationalCliffordSpinBlockIntrinsicRange

/-!
# Exact intrinsic general-Spin range on a nonisotropic block

This file reconstructs a lower-rank intrinsic general-Spin point from an
intrinsic general-Spin point on `W orthogonal_sum <a>` whose represented
action fixes the added coordinate.  The reconstruction uses the exact even
Clifford centralizer theorem and keeps the ambient similitude unchanged.
-/

noncomputable section

open CliffordAlgebra

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Intrinsic block-GSpin points whose represented action fixes the added
coordinate. -/
def IsNonisotropicLastBlockGeneralSpinFixedPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A) :
    Prop :=
  FixesLastCoordinate z.matrixPoint.1

/-- Intrinsic block-GSpin points whose Clifford unit commutes with the added
generator after passing to the ordinary scalar-extended Clifford algebra. -/
def IsNonisotropicLastBlockGeneralSpinCliffordCentralizerPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A) :
    Prop :=
  Commute
    ((W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A
      (z.cliffordUnit :
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A))
    (CliffordAlgebra.ι
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
      (lastCoordinateVector (n := n)))

/-- The final-coordinate instance of the intrinsic GSpin vector graph. -/
def HasNonisotropicLastBlockGeneralSpinLastVectorGraph
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A) :
    Prop :=
  (z.cliffordUnit :
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) *
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A
          (Fin.last n) *
      ((z.cliffordUnit⁻¹ :
          ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) =
    ∑ j, z.matrixPoint.1 j (Fin.last n) •
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeVector A j

/-- Exact even complement-Clifford preimage carried by a block-GSpin point. -/
def HasUniqueNonisotropicLastComplementGeneralSpinEvenCliffordPreimage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A) :
    Prop :=
  ∃! x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A),
    x ∈ CliffordAlgebra.even (W.commutativeScalarExtensionQuadraticForm A) ∧
      W.nonisotropicLastComplementCliffordMap a ha A x =
        (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A
          (z.cliffordUnit :
            (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)

/-- Exact intrinsic GSpin preimage under the complement block embedding. -/
def HasUniqueNonisotropicLastComplementGeneralSpinPreimage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A) :
    Prop :=
  ∃! x : W.CliffordGeneralSpinIntrinsicPoint A,
    W.nonisotropicLastComplementGeneralSpinPoint a ha A x = z

/-- Fixing the added vector forces the ambient GSpin Clifford unit to commute
with the added Clifford generator. -/
theorem nonisotropicLastBlockGeneralSpin_commutativeClifford_commute_lastGenerator_of_fixes
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A)
    (hzFixes : W.IsNonisotropicLastBlockGeneralSpinFixedPoint a ha A z) :
    W.IsNonisotropicLastBlockGeneralSpinCliffordCentralizerPoint a ha A z := by
  let QB :=
    (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A
  let Z : CliffordAlgebra QB :=
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A
      (z.cliffordUnit :
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)
  let Zinv : CliffordAlgebra QB :=
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A
      ((z.cliffordUnit⁻¹ :
          ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)
  let e : CliffordAlgebra QB :=
    CliffordAlgebra.ι QB (lastCoordinateVector (n := n))
  change FixesLastCoordinate z.matrixPoint.1 at hzFixes
  change Commute Z e
  have hgraphCoordinate :
      W.HasNonisotropicLastBlockGeneralSpinLastVectorGraph a ha A z := by
    exact z.vectorGraph (Fin.last n)
  unfold HasNonisotropicLastBlockGeneralSpinLastVectorGraph at hgraphCoordinate
  have hgraph := congrArg
    ((W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A)
    hgraphCoordinate
  simp only [map_mul,
    (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv_baseChangeVector,
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
  have hconj : Z * e * Zinv = e := by
    change Z * CliffordAlgebra.ι QB (Pi.single (Fin.last n) 1) * Zinv = _
      at hgraph
    rw [heq, hrhs] at hgraph
    exact hgraph
  have hinvCoordinate :
      ((z.cliffordUnit⁻¹ :
          ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
        (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) *
          (z.cliffordUnit :
            (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) = 1 :=
    congrArg Units.val (inv_mul_cancel z.cliffordUnit)
  have hinvMul := congrArg
    ((W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A)
    hinvCoordinate
  simp only [map_mul, map_one] at hinvMul
  show Z * e = e * Z
  calc
    Z * e = (Z * e) * (Zinv * Z) := by rw [hinvMul, mul_one]
    _ = (Z * e * Zinv) * Z := by simp only [mul_assoc]
    _ = e * Z := by rw [hconj]

/-- A fixed-last-vector intrinsic block-GSpin point has a unique even
complement-Clifford preimage. -/
theorem existsUnique_nonisotropicLastComplementGeneralSpin_evenCliffordPreimage_of_fixes
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A)
    (hzFixes : W.IsNonisotropicLastBlockGeneralSpinFixedPoint a ha A z) :
    W.HasUniqueNonisotropicLastComplementGeneralSpinEvenCliffordPreimage
      a ha A z := by
  unfold HasUniqueNonisotropicLastComplementGeneralSpinEvenCliffordPreimage
  apply W.existsUnique_even_complementCliffordMap_of_commute_lastGenerator
    a ha A
  · exact
      ((W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv_mem_even_iff
        A _).2 z.involute_eq
  · exact
      W.nonisotropicLastBlockGeneralSpin_commutativeClifford_commute_lastGenerator_of_fixes
        a ha A z hzFixes

/-- Every intrinsic block-GSpin point fixing the added vector is in the unique
image of the intrinsic complement GSpin embedding. -/
theorem existsUnique_nonisotropicLastComplementGeneralSpinPreimage_of_fixes
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A)
    (hzFixes : W.IsNonisotropicLastBlockGeneralSpinFixedPoint a ha A z) :
    W.HasUniqueNonisotropicLastComplementGeneralSpinPreimage a ha A z := by
  unfold HasUniqueNonisotropicLastComplementGeneralSpinPreimage
  have hpre :=
    W.existsUnique_nonisotropicLastComplementGeneralSpin_evenCliffordPreimage_of_fixes
      a ha A z hzFixes
  unfold HasUniqueNonisotropicLastComplementGeneralSpinEvenCliffordPreimage at hpre
  rcases hpre with ⟨xOrd, ⟨_, hxMap⟩, _⟩
  let xCoord : W.cliffordCoordinateBaseChangeAlgebra A :=
    (W.commutativeTensorCliffordEquiv A).symm xOrd
  have hxCoordMap :
      W.nonisotropicLastComplementCoordinateCliffordMap a ha A xCoord =
        (z.cliffordUnit :
          (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) := by
    apply (W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A |>.injective
    rw [W.commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap]
    dsimp only [xCoord]
    rw [(W.commutativeTensorCliffordEquiv A).apply_symm_apply, hxMap]
  have hxInvolute : W.cliffordCoordinateBaseChangeInvolute A xCoord = xCoord := by
    apply W.nonisotropicLastComplementCoordinateCliffordMap_injective a ha A
    rw [W.nonisotropicLastComplementCoordinateCliffordMap_involute,
      hxCoordMap, z.involute_eq]
  have hxNorm :
      xCoord * W.cliffordCoordinateBaseChangeReverse A xCoord =
        algebraMap A (W.cliffordCoordinateBaseChangeAlgebra A) z.similitude := by
    apply W.nonisotropicLastComplementCoordinateCliffordMap_injective a ha A
    rw [map_mul, W.nonisotropicLastComplementCoordinateCliffordMap_reverse,
      hxCoordMap, z.mul_reverse_eq,
      W.nonisotropicLastComplementCoordinateCliffordMap_algebraMap]
  have hxRightInverse :
      xCoord *
          (W.cliffordCoordinateBaseChangeReverse A xCoord *
            algebraMap A (W.cliffordCoordinateBaseChangeAlgebra A)
              (z.similitude⁻¹ : Aˣ)) = 1 := by
    rw [← mul_assoc, hxNorm, ← map_mul]
    have hnu : (z.similitude : A) * (z.similitude⁻¹ : Aˣ) = 1 :=
      congrArg Units.val (mul_inv_cancel z.similitude)
    rw [hnu, map_one]
  let xUnit : (W.cliffordCoordinateBaseChangeAlgebra A)ˣ :=
    Units.mkOfMulEqOne xCoord
      (W.cliffordCoordinateBaseChangeReverse A xCoord *
        algebraMap A (W.cliffordCoordinateBaseChangeAlgebra A)
          (z.similitude⁻¹ : Aˣ))
      hxRightInverse
  have hxUnitMap :
      Units.map
          (W.nonisotropicLastComplementCoordinateCliffordMap a ha A).toMonoidHom
          xUnit = z.cliffordUnit := by
    apply Units.ext
    exact hxCoordMap
  have hxInvMap :
      W.nonisotropicLastComplementCoordinateCliffordMap a ha A
          ((xUnit⁻¹ : (W.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
            W.cliffordCoordinateBaseChangeAlgebra A) =
        ((z.cliffordUnit⁻¹ :
            ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
          (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A) := by
    have h := congrArg
      (fun u :
        ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)ˣ =>
          ((u⁻¹ :
            ((W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)ˣ) :
            (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A))
      hxUnitMap
    exact h
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
      (xUnit : W.cliffordCoordinateBaseChangeAlgebra A) *
          W.cliffordCoordinateBaseChangeVector A i *
        ((xUnit⁻¹ : (W.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
          W.cliffordCoordinateBaseChangeAlgebra A) =
        ∑ j, M.1 j i • W.cliffordCoordinateBaseChangeVector A j := by
    change xCoord * W.cliffordCoordinateBaseChangeVector A i *
        ((xUnit⁻¹ : (W.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
          W.cliffordCoordinateBaseChangeAlgebra A) = _
    apply W.nonisotropicLastComplementCoordinateCliffordMap_injective a ha A
    simp only [map_mul,
      W.nonisotropicLastComplementCoordinateCliffordMap_vector,
      map_sum, map_smul, hxCoordMap, hxInvMap]
    have hzGraph := z.vectorGraph i.castSucc
    rw [hMatrix, Fin.sum_univ_castSucc] at hzGraph
    simpa [fixLastBlockMatrix] using hzGraph
  let x : W.CliffordGeneralSpinIntrinsicPoint A :=
    { cliffordUnit := xUnit
      similitude := z.similitude
      matrixPoint := M
      involute_eq := by
        exact hxInvolute
      mul_reverse_eq := by
        exact hxNorm
      vectorGraph := hxGraph }
  have hxImage :
      W.nonisotropicLastComplementGeneralSpinPoint a ha A x = z := by
    apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit
    exact hxUnitMap
  refine ⟨x, hxImage, ?_⟩
  intro y hy
  apply W.nonisotropicLastComplementGeneralSpinPointHom_injective a ha A
  exact hy.trans hxImage.symm

/-- Every embedded complement GSpin point fixes the added coordinate. -/
theorem nonisotropicLastComplementGeneralSpinPoint_fixesLastCoordinate
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : W.CliffordGeneralSpinIntrinsicPoint A) :
    W.IsNonisotropicLastBlockGeneralSpinFixedPoint a ha A
      (W.nonisotropicLastComplementGeneralSpinPoint a ha A x) := by
  unfold IsNonisotropicLastBlockGeneralSpinFixedPoint
  rw [W.nonisotropicLastComplementGeneralSpinPoint_matrixPoint]
  change FixesLastCoordinate (fixLastBlockMatrix x.matrixPoint.1)
  rw [fixesLastCoordinate_iff_column]
  intro i
  cases i using Fin.lastCases <;> simp [fixLastBlockMatrix]

/-- Exact pointwise range of the intrinsic GSpin block embedding. -/
theorem isNonisotropicLastBlockGeneralSpinFixedPoint_iff_existsUnique_preimage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A) :
    W.IsNonisotropicLastBlockGeneralSpinFixedPoint a ha A z ↔
      W.HasUniqueNonisotropicLastComplementGeneralSpinPreimage a ha A z := by
  constructor
  · exact W.existsUnique_nonisotropicLastComplementGeneralSpinPreimage_of_fixes
      a ha A z
  · intro hpre
    unfold HasUniqueNonisotropicLastComplementGeneralSpinPreimage at hpre
    rcases hpre with ⟨x, hx, _⟩
    rw [← hx]
    exact W.nonisotropicLastComplementGeneralSpinPoint_fixesLastCoordinate
      a ha A x

/-- Set-theoretic image equality for the intrinsic GSpin block embedding. -/
theorem range_nonisotropicLastComplementGeneralSpinPoint_eq_fixedPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Set.range (W.nonisotropicLastComplementGeneralSpinPoint a ha A) =
      {z | W.IsNonisotropicLastBlockGeneralSpinFixedPoint a ha A z} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact W.nonisotropicLastComplementGeneralSpinPoint_fixesLastCoordinate
      a ha A x
  · intro hz
    have hpre :=
      W.existsUnique_nonisotropicLastComplementGeneralSpinPreimage_of_fixes
        a ha A z hz
    unfold HasUniqueNonisotropicLastComplementGeneralSpinPreimage at hpre
    rcases hpre with ⟨x, hx, _⟩
    exact ⟨x, hx⟩

end RationalQuadraticSpaceMatrix
