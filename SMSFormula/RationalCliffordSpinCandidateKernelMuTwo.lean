import SMSFormula.RationalCliffordSpinCandidateScalarCentralizer

/-!
# The affine Clifford--Spin candidate kernel is `mu_2`

This file upgrades the arbitrary-rational-algebra calculation of the unit
fiber to a natural equivalence of group-valued point functors and hence to an
isomorphism of group schemes.
-/

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidalCategory

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

section AlgebraPoints

variable {A B : Type} [CommRing A] [CommRing B]
  [Algebra ℚ A] [Algebra ℚ B]

/-- The scalar-root description of the affine candidate kernel commutes with
extension of the rational coefficient algebra. -/
theorem rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_naturality
    (f : A →ₐ[ℚ] B) (z : rootsOfUnity 2 A) :
    V.cliffordSpinCandidateCoordinateAlgHomMap A f
        ((V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
          A z).1) =
      (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
        B (restrictRootsOfUnity f 2 z)).1 := by
  apply Ideal.Quotient.algHom_ext ℚ
  apply MvPolynomial.algHom_ext
  intro u
  rcases u with s | ij
  · change f
        (V.cliffordSpinCandidateCoordinateAlgHomOfPointData A
          (V.cliffordSpinCandidatePointDataOfRootOfUnity A z)
          (V.cliffordSpinCandidateCliffordCoordinate s)) =
        V.cliffordSpinCandidateCoordinateAlgHomOfPointData B
          (V.cliffordSpinCandidatePointDataOfRootOfUnity B
            (restrictRootsOfUnity f 2 z))
          (V.cliffordSpinCandidateCliffordCoordinate s)
    rw [V.cliffordSpinCandidateCoordinateAlgHomOfPointData_cliffordCoordinate,
      V.cliffordSpinCandidateCoordinateAlgHomOfPointData_cliffordCoordinate]
    change f
        ((V.cliffordCoordinateBaseChangeBasis A).repr
          (algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
            ((z : Aˣ) : A)) s) =
        (V.cliffordCoordinateBaseChangeBasis B).repr
          (algebraMap B (V.cliffordCoordinateBaseChangeAlgebra B)
            ((restrictRootsOfUnity f 2 z : rootsOfUnity 2 B) : Bˣ)) s
    simp [cliffordCoordinateBaseChangeBasis,
      Algebra.TensorProduct.algebraMap_apply]
  · rcases ij with ⟨i, j⟩
    change f
        (V.cliffordSpinCandidateCoordinateAlgHomOfPointData A
          (V.cliffordSpinCandidatePointDataOfRootOfUnity A z)
          (V.cliffordSpinCandidateMatrixCoordinate i j)) =
        V.cliffordSpinCandidateCoordinateAlgHomOfPointData B
          (V.cliffordSpinCandidatePointDataOfRootOfUnity B
            (restrictRootsOfUnity f 2 z))
          (V.cliffordSpinCandidateMatrixCoordinate i j)
    rw [V.cliffordSpinCandidateCoordinateAlgHomOfPointData_matrixCoordinate,
      V.cliffordSpinCandidateCoordinateAlgHomOfPointData_matrixCoordinate]
    change f ((1 : Matrix (Fin n) (Fin n) A) i j) =
      (1 : Matrix (Fin n) (Fin n) B) i j
    simp [Matrix.one_apply]

/-- Scalar-root candidate coordinates commute with every affine candidate
coordinate point. -/
theorem rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_commutes
    (z : rootsOfUnity 2 A)
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
        A z).1 * F =
      F *
        (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
          A z).1 := by
  have hz :
      V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A
          (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
            A z).1 =
        V.cliffordSpinCandidatePointDataOfRootOfUnity A z := by
    exact (V.cliffordSpinCandidateCoordinateAlgHomEquivPointData A).apply_symm_apply _
  apply (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).injective
  rw [map_mul, map_mul, hz]
  apply CliffordSpinCandidatePointData.ext
  · rw [CliffordSpinCandidatePointData.mul_clifford,
      CliffordSpinCandidatePointData.mul_clifford]
    change algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
        ((z : Aˣ) : A) *
          (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F).clifford =
      (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F).clifford *
        algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) ((z : Aˣ) : A)
    exact Algebra.commutes _ _
  · apply (V.specialOrthogonalMatrixPointEquivGroup A).injective
    change
      (V.cliffordSpinCandidatePointDataOfRootOfUnity A z *
          V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A F).matrixGroup =
        (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A F *
          V.cliffordSpinCandidatePointDataOfRootOfUnity A z).matrixGroup
    rw [CliffordSpinCandidatePointData.mul_matrixGroup,
      CliffordSpinCandidatePointData.mul_matrixGroup]
    rw [V.cliffordSpinCandidatePointDataOfRootOfUnity_matrixGroup]
    change 1 *
        (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F).matrixGroup =
      (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F).matrixGroup * 1
    simp

end AlgebraPoints

end RationalQuadraticSpaceMatrix
