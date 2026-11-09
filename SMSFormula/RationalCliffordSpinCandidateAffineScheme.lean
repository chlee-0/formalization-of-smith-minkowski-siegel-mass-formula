import SMSFormula.RationalCliffordSpinCandidateCoordinates
import SMSFormula.RationalSpecialOrthogonalGroupScheme

/-!
# The affine Clifford--Spin candidate and its morphism to `SO`

The finite coordinate equations from
`RationalCliffordSpinCandidateCoordinates` define an affine scheme over
`Spec ℚ`.  The matrix coordinates satisfy the defining equations of the
completed special-orthogonal coordinate algebra, so they induce a coordinate
algebra homomorphism in the opposite direction and hence a morphism

```text
Spec(SpinCandidate) ⟶ SO.
```

On every characteristic-zero extension field, the candidate point attached
to an existing Clifford `spinGroup` element is sent to its already constructed
special-orthogonal matrix representation.  This file only constructs the
affine carrier and this morphism.  It does not identify all candidate points
with the closure-generated `spinGroup`, bundle the candidate as a group
object, or prove any form of fppf exactness or surjectivity.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

def cliffordSpinCandidateUniversalMatrixInCoordinateRing :
    Matrix (Fin n) (Fin n) V.cliffordSpinCandidateCoordinateRing :=
  fun i j => V.cliffordSpinCandidateMatrixCoordinate i j

def cliffordSpinCandidateUniversalSpecialOrthogonalPoint :
    V.specialOrthogonalMatrixPoint V.cliffordSpinCandidateCoordinateRing := by
  refine ⟨V.cliffordSpinCandidateUniversalMatrixInCoordinateRing, ?_, ?_⟩
  · ext i j
    have hmem : V.cliffordSpinSpecialOrthogonalRelation i j ∈
        V.cliffordSpinCandidateRelationIdeal := by
      apply Ideal.subset_span
      exact Or.inl (Or.inr ⟨(i, j), rfl⟩)
    have hzero : Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal
        (V.cliffordSpinSpecialOrthogonalRelation i j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [cliffordSpinSpecialOrthogonalRelation, map_sub] at hzero
    rw [sub_eq_zero] at hzero
    simp only [map_sum, map_mul] at hzero
    simp only [cliffordSpinCandidateUniversalMatrixInCoordinateRing,
      specialOrthogonalMappedFormMatrix, Matrix.mul_apply,
      Matrix.transpose_apply]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simpa [cliffordSpinCandidateMatrixCoordinate] using hzero
  · have hmem : V.cliffordSpinSpecialOrthogonalDetRelation ∈
        V.cliffordSpinCandidateRelationIdeal := by
      apply Ideal.subset_span
      exact Or.inr (Set.mem_singleton _)
    have hzero : Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal
        V.cliffordSpinSpecialOrthogonalDetRelation = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [cliffordSpinSpecialOrthogonalDetRelation, map_sub] at hzero
    rw [sub_eq_zero] at hzero
    change (Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal)
        (cliffordSpinUniversalMatrix (n := n)).det = 1 at hzero
    rw [RingHom.map_det] at hzero
    simpa [cliffordSpinUniversalMatrix,
      cliffordSpinCandidateUniversalMatrixInCoordinateRing,
      cliffordSpinCandidateMatrixCoordinate] using hzero

def specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom :
    V.specialOrthogonalCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing :=
  V.specialOrthogonalCoordinateAlgHomOfMatrixPoint
    V.cliffordSpinCandidateUniversalSpecialOrthogonalPoint

@[simp]
theorem specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom_coordinate
    (i j : Fin n) :
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
        (V.specialOrthogonalCoordinate i j) =
      V.cliffordSpinCandidateMatrixCoordinate i j := by
  rw [specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom,
    V.specialOrthogonalCoordinateAlgHomOfMatrixPoint_coordinate]
  rfl

abbrev cliffordSpinCandidateAffineScheme : Scheme :=
  Spec (CommRingCat.of V.cliffordSpinCandidateCoordinateRing)

def cliffordSpinCandidateToSpecialOrthogonalSchemeHom :
    V.cliffordSpinCandidateAffineScheme ⟶
      V.specialOrthogonalAffineScheme :=
  Spec.map (CommRingCat.ofHom
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom)

end RationalQuadraticSpaceMatrix
