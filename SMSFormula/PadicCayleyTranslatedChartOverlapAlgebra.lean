import SMSFormula.PadicCayleyTranslatedChartOverlapTopology

/-!
# Algebra on overlaps of translated p-adic Cayley charts

This module unfolds the exact overlap topology into ambient matrix algebra.
Target-overlap membership is expressed by the two inverse-domain unit
conditions.  Source-overlap membership is expressed using the relative target
matrix

`d⁻¹ * cayley_c(X) = (d⁻¹c) * cayley(X)`.

The forward and inverse transition homeomorphisms are then identified
pointwise with inverse Cayley applied to the corresponding relative target
matrix.  These formulas are uniform at every prime.  No derivative, Jacobian,
measure comparison, translation invariance, full-group measure, or chart
gluing is introduced.
-/

noncomputable section

open scoped Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- A point lies in the overlap of two translated targets exactly when both
inverse translations lie in the ambient Cayley inverse domain. -/
theorem mem_padicCayleySpecialOrthogonalTranslatedTargetOverlapSet_iff_inverseDomains
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c d g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    g ∈ padicCayleySpecialOrthogonalTranslatedTargetOverlapSet F p c d ↔
      (((c⁻¹ * g).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) ∈
          Matrix.padicCayleyInverseDomain p ∧
        (((d⁻¹ * g).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) ∈
          Matrix.padicCayleyInverseDomain p := by
  rw [mem_padicCayleySpecialOrthogonalTranslatedTargetOverlapSet_iff,
    mem_padicCayleySpecialOrthogonalTranslatedTarget_iff_inverseDomain,
    mem_padicCayleySpecialOrthogonalTranslatedTarget_iff_inverseDomain]

/-- Target-overlap membership is the pair of matrix-unit conditions for
`c⁻¹g + 1` and `d⁻¹g + 1`. -/
theorem mem_padicCayleySpecialOrthogonalTranslatedTargetOverlapSet_iff_isUnit
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (c d g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    g ∈ padicCayleySpecialOrthogonalTranslatedTargetOverlapSet F p c d ↔
      IsUnit
          (((c⁻¹ * g).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) + 1) ∧
        IsUnit
          (((d⁻¹ * g).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) + 1) := by
  rw [
    mem_padicCayleySpecialOrthogonalTranslatedTargetOverlapSet_iff_inverseDomains]
  rfl

/-- The target matrix seen from the center `d` after applying the translated
Cayley chart centered at `c`. -/
def skewAdjointPadicCayleyTranslatedRelativeTargetMatrix
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    Matrix (Fin n) (Fin n) ℚ_[p] :=
  ((d⁻¹ *
      (skewAdjointPadicCayleyTranslatedHomeomorph
        F p hF c X).1).1.1.1 :
    Matrix (Fin n) (Fin n) ℚ_[p])

/-- The relative target matrix is `(d⁻¹c)` times the identity-centered
Cayley transform. -/
theorem skewAdjointPadicCayleyTranslatedRelativeTargetMatrix_eq_mul_cayley
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyTranslatedRelativeTargetMatrix
        F p hF c d X =
      (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
        Matrix.padicCayleyForwardMatrix p
          (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  change
    (((d⁻¹).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
        (skewAdjointPadicCayleyTranslatedHomeomorph
          F p hF c X).1.1.1.1) =
      (((d⁻¹).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
          (c.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
        Matrix.padicCayleyForwardMatrix p
          (X.1 : Matrix (Fin n) (Fin n) ℚ_[p])
  rw [coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]
  exact (mul_assoc
    ((d⁻¹).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])
    (c.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])
    (Matrix.padicCayleyForwardMatrix p
      (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]))).symm

/-- The relative target matrix with the Cayley fraction completely
unfolded. -/
theorem skewAdjointPadicCayleyTranslatedRelativeTargetMatrix_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyTranslatedRelativeTargetMatrix
        F p hF c d X =
      (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
        ((1 + (X.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
          (1 - (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹) := by
  rw [
    skewAdjointPadicCayleyTranslatedRelativeTargetMatrix_eq_mul_cayley]
  rfl

/-- Source-overlap membership is exactly membership of the relative target
matrix in the Cayley inverse domain. -/
theorem mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff_relative_inverseDomain
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    X ∈ skewAdjointPadicCayleyTranslatedSourceOverlapSet F p hF c d ↔
      skewAdjointPadicCayleyTranslatedRelativeTargetMatrix
          F p hF c d X ∈ Matrix.padicCayleyInverseDomain p := by
  rw [mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff,
    mem_padicCayleySpecialOrthogonalTranslatedTarget_iff_inverseDomain]
  rfl

/-- Source-overlap membership is the matrix-unit condition for the relative
target plus the identity. -/
theorem mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff_relative_isUnit
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    X ∈ skewAdjointPadicCayleyTranslatedSourceOverlapSet F p hF c d ↔
      IsUnit
        (skewAdjointPadicCayleyTranslatedRelativeTargetMatrix
          F p hF c d X + 1) := by
  rw [
    mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff_relative_inverseDomain]
  rfl

/-- Source-overlap membership unfolded entirely into source matrix
coordinates. -/
theorem mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff_isUnit
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    X ∈ skewAdjointPadicCayleyTranslatedSourceOverlapSet F p hF c d ↔
      IsUnit
        ((((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
          ((1 + (X.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
            (1 - (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹) + 1) := by
  rw [
    mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff_relative_isUnit,
    skewAdjointPadicCayleyTranslatedRelativeTargetMatrix_eq]

/-- The forward overlap transition is inverse Cayley applied to the relative
target matrix `d⁻¹ * cayley_c(X)`. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_eq_inverse_relative
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1.1 :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      Matrix.padicCayleyInverseMatrix p
        (skewAdjointPadicCayleyTranslatedRelativeTargetMatrix
          F p hF c d X.1) := by
  rw [
    coe_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph_apply_matrix]
  rfl

/-- The forward overlap transition is inverse Cayley applied to
`(d⁻¹c) * cayley(X)`. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_eq_inverse_mul_cayley
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1.1 :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      Matrix.padicCayleyInverseMatrix p
        ((((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
          Matrix.padicCayleyForwardMatrix p
            (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransition_eq_inverse_relative,
    skewAdjointPadicCayleyTranslatedRelativeTargetMatrix_eq_mul_cayley]

/-- The forward overlap transition with both Cayley formulas completely
unfolded. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1.1 :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((((((d⁻¹ * c).1.1.1 :
          Matrix (Fin n) (Fin n) ℚ_[p])) *
          ((1 + (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
            (1 - (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹)) + 1)⁻¹ *
        (((((d⁻¹ * c).1.1.1 :
          Matrix (Fin n) (Fin n) ℚ_[p])) *
          ((1 + (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
            (1 - (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹)) - 1)) := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransition_eq_inverse_mul_cayley]
  rfl

/-- The inverse overlap transition is inverse Cayley applied to the relative
target matrix `c⁻¹ * cayley_d(Y)`. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_symm_eq_inverse_relative
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF d c) :
    (((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d).symm X).1.1 :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      Matrix.padicCayleyInverseMatrix p
        (skewAdjointPadicCayleyTranslatedRelativeTargetMatrix
          F p hF d c X.1) := by
  rw [
    coe_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph_symm_apply_matrix]
  rfl

/-- The inverse overlap transition is inverse Cayley applied to
`(c⁻¹d) * cayley(Y)`. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_symm_eq_inverse_mul_cayley
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF d c) :
    (((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d).symm X).1.1 :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      Matrix.padicCayleyInverseMatrix p
        ((((c⁻¹ * d).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
          Matrix.padicCayleyForwardMatrix p
            (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransition_symm_eq_inverse_relative,
    skewAdjointPadicCayleyTranslatedRelativeTargetMatrix_eq_mul_cayley]

/-- The inverse overlap transition with both Cayley formulas completely
unfolded. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_symm_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF d c) :
    (((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d).symm X).1.1 :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((((((c⁻¹ * d).1.1.1 :
          Matrix (Fin n) (Fin n) ℚ_[p])) *
          ((1 + (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
            (1 - (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹)) + 1)⁻¹ *
        (((((c⁻¹ * d).1.1.1 :
          Matrix (Fin n) (Fin n) ℚ_[p])) *
          ((1 + (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
            (1 - (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹)) - 1)) := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransition_symm_eq_inverse_mul_cayley]
  rfl

end PositiveDefiniteIntegralLattice
