import SMSFormula.PadicSpecialOrthogonalDifferentialCongruence

/-!
# Surjectivity of sign-separated special-orthogonal reduction

Finite reduction of the integral special-orthogonal stabilizer lands in the
determinant-one subgroup of the ordinary stabilizer reduction image.  If the
residue ring distinguishes `1` and `-1`, every element of that subgroup has a
determinant-one integral lift.

Indeed, an arbitrary integral stabilizer lift has p-adic determinant whose
square is one, hence determinant `1` or `-1`.  Its residue determinant is one,
so sign separation excludes the second case.  The theorem is then transported
through the common-matrix equivalence to the direct corrected stabilizer.

The sign-separation hypothesis remains explicit.  No index-two assertion,
raw congruence-solution set, or Haar-measure comparison is used.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- If `1` and `-1` remain distinct modulo `p ^ k`, finite reduction of the
original integral special-orthogonal stabilizer is onto the determinant-one
part of the ordinary stabilizer reduction image. -/
theorem
    surjective_localPadicSpecialOrthogonalLatticeStabilizerReduction_of_neg_one_ne_one
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hsep : (-1 : ZMod (p ^ k)) ≠ 1) :
    Function.Surjective
      (L.localPadicSpecialOrthogonalLatticeStabilizerReduction p k) := by
  intro u
  rcases u.1.2 with ⟨g, hg⟩
  have hdetSq :
      ((L.localPadicLatticeStabilizerDeterminant p g : ℤ_[p]ˣ) : ℤ_[p]) ^ 2 =
        1 := by
    exact congrArg Units.val
      (L.localPadicLatticeStabilizerDeterminant_sq p g)
  rcases sq_eq_one_iff.mp hdetSq with hdetOne | hdetNeg
  · have hdetOneUnits :
        L.localPadicLatticeStabilizerDeterminant p g = 1 :=
      Units.ext hdetOne
    refine ⟨⟨g, hdetOneUnits⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hg
  · have hdetNegUnits :
        L.localPadicLatticeStabilizerDeterminant p g = -1 :=
      Units.ext hdetNeg
    let ug :
        (L.localPadicLatticeStabilizerReduction p k).range :=
      ⟨L.localPadicLatticeStabilizerReduction p k g, ⟨g, rfl⟩⟩
    have hug : ug = u.1 := by
      apply Subtype.ext
      exact hg
    have hdetUgNeg :
        L.localPadicLatticeStabilizerReductionRangeDeterminant p k ug = -1 := by
      rw [L.localPadicLatticeStabilizerReductionRangeDeterminant_apply p k g,
        hdetNegUnits]
      simp
    have hdetUgOne :
        L.localPadicLatticeStabilizerReductionRangeDeterminant p k ug = 1 := by
      rw [hug]
      exact u.2
    have hunit : (-1 : (ZMod (p ^ k))ˣ) = 1 :=
      hdetUgNeg.symm.trans hdetUgOne
    exact (hsep (congrArg Units.val hunit)).elim

/-- Under the same explicit sign-separation hypothesis, the transported
finite reduction on the direct corrected stabilizer is surjective. -/
theorem
    surjective_localPadicSpecialOrthogonalDifferentialStabilizerReduction_of_neg_one_ne_one
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hsep : (-1 : ZMod (p ^ k)) ≠ 1) :
    Function.Surjective
      (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction p k) :=
  (L.surjective_localPadicSpecialOrthogonalLatticeStabilizerReduction_of_neg_one_ne_one
      p k hsep).comp
    (L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
      p).surjective

/-- At a sign-separated depth, the literal range of the direct corrected
reduction has the cardinality of the full determinant-one subgroup inside the
ordinary finite stabilizer reduction image. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialStabilizerReduction_range_eq
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hsep : (-1 : ZMod (p ^ k)) ≠ 1) :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction p k).range =
      Nat.card
        (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
          p k) := by
  have hrange :
      (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction p k).range =
        ⊤ :=
    MonoidHom.range_eq_top.mpr
      (L.surjective_localPadicSpecialOrthogonalDifferentialStabilizerReduction_of_neg_one_ne_one
        p k hsep)
  rw [hrange]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv

end PositiveDefiniteIntegralLattice
