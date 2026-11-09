import SMSFormula.PadicSpecialOrthogonalDeterminantRangeCardinality

/-!
# Transporting the integral p-adic determinant image to finite reduction

Reduction modulo `p ^ k` maps the actual image of the integral p-adic
determinant character onto the actual determinant image of the finite
stabilizer reduction range.  When the residue ring distinguishes `1` and
`-1`, this map is injective as well: every integral determinant value has
square one.

Thus the finite determinant correction is exactly the cardinality of the
integral determinant-character image.  That cardinal remains literal; it is
not declared to be two.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix Matrix.Norms.Operator NNReal Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Reduction of integral p-adic determinant values to the actual determinant
image of the finite stabilizer reduction range. -/
def localPadicLatticeStabilizerDeterminantRangeReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    (L.localPadicLatticeStabilizerDeterminant p).range →*
      (L.localPadicLatticeStabilizerReductionRangeDeterminant p k).range where
  toFun u :=
    ⟨Units.map (PadicInt.toZModPow k).toMonoidHom u.1, by
      rcases u.2 with ⟨g, hg⟩
      let ug : (L.localPadicLatticeStabilizerReduction p k).range :=
        ⟨L.localPadicLatticeStabilizerReduction p k g, ⟨g, rfl⟩⟩
      refine ⟨ug, ?_⟩
      rw [L.localPadicLatticeStabilizerReductionRangeDeterminant_apply p k g,
        hg]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp

/-- Every finite determinant-image value is the reduction of an integral
p-adic determinant value. -/
theorem
    surjective_localPadicLatticeStabilizerDeterminantRangeReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Function.Surjective
      (L.localPadicLatticeStabilizerDeterminantRangeReduction p k) := by
  intro y
  rcases y.2 with ⟨u, hu⟩
  rcases u.2 with ⟨g, hg⟩
  let d : (L.localPadicLatticeStabilizerDeterminant p).range :=
    ⟨L.localPadicLatticeStabilizerDeterminant p g, ⟨g, rfl⟩⟩
  refine ⟨d, ?_⟩
  apply Subtype.ext
  let ug : (L.localPadicLatticeStabilizerReduction p k).range :=
    ⟨L.localPadicLatticeStabilizerReduction p k g, ⟨g, rfl⟩⟩
  have hug : ug = u := by
    apply Subtype.ext
    exact hg
  calc
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (L.localPadicLatticeStabilizerDeterminant p g) =
        L.localPadicLatticeStabilizerReductionRangeDeterminant p k ug := by
      exact
        (L.localPadicLatticeStabilizerReductionRangeDeterminant_apply
          p k g).symm
    _ = L.localPadicLatticeStabilizerReductionRangeDeterminant p k u := by
      rw [hug]
    _ = y.1 := hu

/-- At a sign-separated depth, reduction is injective on the actual integral
p-adic determinant image. -/
theorem
    injective_localPadicLatticeStabilizerDeterminantRangeReduction_of_neg_one_ne_one
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hsep : (-1 : ZMod (p ^ k)) ≠ 1) :
    Function.Injective
      (L.localPadicLatticeStabilizerDeterminantRangeReduction p k) := by
  intro u v huv
  have huSq : ((u.1 : ℤ_[p]ˣ) : ℤ_[p]) ^ 2 = 1 := by
    rcases u.2 with ⟨g, hg⟩
    have hgSq :=
      congrArg Units.val
        (L.localPadicLatticeStabilizerDeterminant_sq p g)
    rw [hg] at hgSq
    exact hgSq
  have hvSq : ((v.1 : ℤ_[p]ˣ) : ℤ_[p]) ^ 2 = 1 := by
    rcases v.2 with ⟨g, hg⟩
    have hgSq :=
      congrArg Units.val
        (L.localPadicLatticeStabilizerDeterminant_sq p g)
    rw [hg] at hgSq
    exact hgSq
  have huvReduction :
      Units.map (PadicInt.toZModPow k).toMonoidHom u.1 =
        Units.map (PadicInt.toZModPow k).toMonoidHom v.1 :=
    congrArg Subtype.val huv
  rcases sq_eq_one_iff.mp huSq with huOne | huNeg <;>
    rcases sq_eq_one_iff.mp hvSq with hvOne | hvNeg
  · apply Subtype.ext
    apply Units.ext
    exact huOne.trans hvOne.symm
  · have huOneUnits : u.1 = 1 := Units.ext huOne
    have hvNegUnits : v.1 = -1 := Units.ext hvNeg
    rw [huOneUnits, hvNegUnits] at huvReduction
    have hz : (1 : ZMod (p ^ k)) = -1 := by
      simpa using congrArg Units.val huvReduction
    exact (hsep hz.symm).elim
  · have huNegUnits : u.1 = -1 := Units.ext huNeg
    have hvOneUnits : v.1 = 1 := Units.ext hvOne
    rw [huNegUnits, hvOneUnits] at huvReduction
    have hz : (-1 : ZMod (p ^ k)) = 1 := by
      simpa using congrArg Units.val huvReduction
    exact (hsep hz).elim
  · apply Subtype.ext
    apply Units.ext
    exact huNeg.trans hvNeg.symm

/-- At a sign-separated depth, reduction gives a multiplicative equivalence
between the integral p-adic determinant image and the finite determinant
image. -/
def localPadicLatticeStabilizerDeterminantRangeReductionMulEquiv
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hsep : (-1 : ZMod (p ^ k)) ≠ 1) :
    (L.localPadicLatticeStabilizerDeterminant p).range ≃*
      (L.localPadicLatticeStabilizerReductionRangeDeterminant p k).range :=
  MulEquiv.ofBijective
    (L.localPadicLatticeStabilizerDeterminantRangeReduction p k)
    ⟨L.injective_localPadicLatticeStabilizerDeterminantRangeReduction_of_neg_one_ne_one
        p k hsep,
      L.surjective_localPadicLatticeStabilizerDeterminantRangeReduction p k⟩

/-- At a sign-separated depth, the finite determinant-image cardinal is the
cardinal of the integral p-adic determinant-character image. -/
theorem
    natCard_localPadicLatticeStabilizerReductionRangeDeterminant_range_eq_integralDeterminantRange
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hsep : (-1 : ZMod (p ^ k)) ≠ 1) :
    Nat.card
        (L.localPadicLatticeStabilizerReductionRangeDeterminant p k).range =
      Nat.card (L.localPadicLatticeStabilizerDeterminant p).range :=
  (Nat.card_congr
    (L.localPadicLatticeStabilizerDeterminantRangeReductionMulEquiv
      p k hsep).toEquiv).symm

/-- The finite determinant-image correction at the selected density-adapted
depth equals the integral p-adic determinant-image cardinal. -/
theorem
    natCard_localPadicLatticeStabilizerReductionRangeDeterminant_densityCongruenceRange_eq_integralDeterminantRange
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card
        (L.localPadicLatticeStabilizerReductionRangeDeterminant
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            p)).range =
      Nat.card (L.localPadicLatticeStabilizerDeterminant p).range :=
  L.natCard_localPadicLatticeStabilizerReductionRangeDeterminant_range_eq_integralDeterminantRange
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (L.neg_one_ne_one_zmod_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p)

/-- The balanced corrected stabilizer-volume identity with the orientation
factor expressed intrinsically as the integral p-adic determinant-image
cardinal. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_integralDeterminantRangeCard_eq_densityBallCard_mul_ordinaryReductionRangeCard
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ level : ℕ,
      ∃ balls : Finset (Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule),
        ∃ center :
            Set (skewAdjointMatricesLieSubalgebra
                (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
                p,
          (∀ B ∈ balls,
            B = skewAdjointPadicTranslatedUniformCoordinateBall
              L.rationalFormMatrix p level (center B)) ∧
          (↑balls : Set (Set (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map
              (algebraMap ℚ ℚ_[p]))).toSubmodule)).PairwiseDisjoint id ∧
          (⋃ B ∈ balls, B) =
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              p ∧
          L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
              (Nat.card
                (L.localPadicLatticeStabilizerDeterminant p).range :
                  ℝ≥0∞) =
            (‖(2 : ℚ_[p])‖₊ ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra
                  L.rationalFormMatrix) : ℝ≥0∞) *
              (balls.card : ℝ≥0∞) *
              ((p : ℝ≥0∞) ^
                (level * Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹ *
              (Nat.card
                (L.localPadicLatticeStabilizerReduction
                  p
                  (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                    p)).range : ℝ≥0∞) := by
  obtain
      ⟨level, balls, center, hcenter, hpairwise, hcover, hvolume⟩ :=
    L.exists_localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_determinantRangeCard_eq_densityBallCard_mul_ordinaryReductionRangeCard
      p
  refine
    ⟨level, balls, center, hcenter, hpairwise, hcover, ?_⟩
  rw [
    L.natCard_localPadicLatticeStabilizerReductionRangeDeterminant_densityCongruenceRange_eq_integralDeterminantRange
      p] at hvolume
  exact hvolume

end PositiveDefiniteIntegralLattice
