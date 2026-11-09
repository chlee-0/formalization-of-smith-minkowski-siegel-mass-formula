import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDoubledAttainedResidue

/-!
# Two-torsion fibers on attained dyadic residues

Doubling at the original dyadic residue level forgets exactly its final
binary layer.  This module defines the literal one-level restriction, proves
that its fibers are exactly the fibers of doubling on the original attained
residue subtype, and identifies attained two-torsion with canonical source
centers lying in the form-coordinate ball one level below the original
residue level.

The existing source translation theorem acts only by the ball at the full
original residue level.  It does not supply translation stability one level
higher in radius, so no uniform fiber cardinality, additive closure, quotient,
or gauge value is asserted here.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

/-- In a positive dyadic residue level, equality after doubling is exactly
equality after restriction by one level. -/
theorem zmod_two_nsmul_eq_two_nsmul_iff_castHom_pred_eq
    (m : ℕ) (hm : 1 ≤ m) (a b : ZMod (2 ^ m)) :
    2 • a = 2 • b ↔
      ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le m 1))
          (ZMod (2 ^ (m - 1))) a =
        ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le m 1))
          (ZMod (2 ^ (m - 1))) b := by
  calc
    2 • a = 2 • b ↔ 2 • (a - b) = 0 := by
      rw [nsmul_sub, sub_eq_zero]
    _ ↔
        ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le m 1))
            (ZMod (2 ^ (m - 1))) (a - b) = 0 :=
      zmod_two_nsmul_eq_zero_iff_castHom_pred_eq_zero m hm (a - b)
    _ ↔
        ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le m 1))
            (ZMod (2 ^ (m - 1))) a =
          ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le m 1))
            (ZMod (2 ^ (m - 1))) b := by
      rw [map_sub, sub_eq_zero]

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_attained_torsion : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Restriction of original dyadic form-coordinate residues by exactly one
level. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
    (L : PositiveDefiniteIntegralLattice n) :
    skewAdjointFormElementaryPadicCoordinateResidue
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix →+
      skewAdjointFormElementaryPadicCoordinateResidue
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2 - 1)
          L.rationalFormMatrix where
  toFun x i :=
    ZMod.castHom
      (pow_dvd_pow 2
        (Nat.sub_le
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2) 1))
      (ZMod
        (2 ^
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2 - 1))) (x i)
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    exact map_add _ (x i) (y i)

/-- Restricting the original reduction of an integral form coordinate by
one level gives its literal reduction at that predecessor level. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction_reduction
    (L : PositiveDefiniteIntegralLattice n)
    (x : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      2 L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
        (skewAdjointFormElementaryPadicCoordinateReduction
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero x) =
      skewAdjointFormElementaryPadicCoordinateReduction
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero x := by
  funext i
  exact
    PadicInt.cast_toZModPow
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2 - 1)
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        2)
      (Nat.sub_le
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2) 1) _

/-- Equality after doubling at the original form-coordinate residue level
is exactly equality after one-level restriction. -/
theorem
    two_nsmul_eq_two_nsmul_iff_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction_eq
    (L : PositiveDefiniteIntegralLattice n)
    (x y : skewAdjointFormElementaryPadicCoordinateResidue
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        2)
      L.rationalFormMatrix) :
    2 • x = 2 • y ↔
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
          x =
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
          y := by
  have hm : 1 ≤
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        2 := by
    unfold
      localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
    have hk :=
      L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
    omega
  constructor
  · intro h
    funext i
    exact
      (zmod_two_nsmul_eq_two_nsmul_iff_castHom_pred_eq
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2) hm (x i) (y i)).1 (congrFun h i)
  · intro h
    funext i
    exact
      (zmod_two_nsmul_eq_two_nsmul_iff_castHom_pred_eq
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2) hm (x i) (y i)).2 (congrFun h i)

/-- Original attained dyadic residues killed by multiplication by two in
the enlarged determinant-loss carrier. -/
abbrev
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicAttainedTwoTorsionIndex
    (L : PositiveDefiniteIntegralLattice n) :=
  {a :
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
        2 //
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDyadicDeterminantLossResidue
        a ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo.ker}

/-- An attained residue is killed by two in `T₂` exactly when its original
residue vanishes after one-level restriction. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndex_mem_dyadicAttainedTwoTorsion_iff_predRestriction_eq_zero
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDyadicDeterminantLossResidue
          a ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo.ker ↔
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
          a.1 = 0 := by
  change
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDyadicDeterminantLossResidue
            a) = 0 ↔ _
  constructor
  · intro h
    have hval := congrArg Subtype.val h
    change 2 • a.1 = 0 at hval
    have htwo : 2 • a.1 = 2 • (0 :
        skewAdjointFormElementaryPadicCoordinateResidue
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix) := by
      rw [nsmul_zero]
      exact hval
    have hpred :=
      (L.two_nsmul_eq_two_nsmul_iff_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction_eq
        a.1 0).1 htwo
    rw [map_zero] at hpred
    exact hpred
  · intro h
    apply Subtype.ext
    change 2 • a.1 = 0
    have hpred :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
            a.1 =
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
            0 := by
      rw [map_zero]
      exact h
    have htwo :=
      (L.two_nsmul_eq_two_nsmul_iff_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction_eq
        a.1 0).2 hpred
    rw [nsmul_zero] at htwo
    exact htwo

/-- The attained two-torsion condition is exactly membership of the canonical
source center in the form-coordinate ball one level below the original
residue level. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndex_mem_dyadicAttainedTwoTorsion_iff_center_mem_predBall
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDyadicDeterminantLossResidue
          a ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo.ker ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
          2 a).1 ∈
        skewAdjointFormElementaryPadicUniformCoordinateBall
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2 - 1)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero := by
  rw [L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndex_mem_dyadicAttainedTwoTorsion_iff_predRestriction_eq_zero]
  rw [←
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_reduction
      2 a]
  rw [L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction_reduction]
  exact
    (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2 - 1)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
        2 a)).symm

/-- Two original attained indices have the same doubled residue exactly
when their residues agree after one-level restriction. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue_eq_iff_predRestriction_eq
    (L : PositiveDefiniteIntegralLattice n)
    (a b : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue
          a =
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue
          b ↔
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
          a.1 =
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
          b.1 := by
  constructor
  · intro h
    apply
      (L.two_nsmul_eq_two_nsmul_iff_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction_eq
        a.1 b.1).1
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact
      (L.two_nsmul_eq_two_nsmul_iff_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction_eq
        a.1 b.1).2 h

/-- The fiber of doubling over an attained residue is literally the fiber of
one-level restriction on the attained residue subtype. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueFiberEquivPredRestrictionFiber
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2) :
    {b :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
          2 //
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue
          b =
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue
          a} ≃
      {b :
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
            2 //
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
            b.1 =
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
            a.1} where
  toFun b :=
    ⟨b.1,
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue_eq_iff_predRestriction_eq
        b.1 a).1 b.2⟩
  invFun b :=
    ⟨b.1,
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue_eq_iff_predRestriction_eq
        b.1 a).2 b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact finite cardinal of a doubling fiber is the cardinal of the
corresponding attained one-level restriction fiber.  No uniform value is
asserted. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueFiber_eq_predRestrictionFiber
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2) :
    Nat.card
        {b :
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
              2 //
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue
              b =
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue
              a} =
      Nat.card
        {b :
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
              2 //
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
              b.1 =
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
              a.1} :=
  Nat.card_congr
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueFiberEquivPredRestrictionFiber
      a)

end PositiveDefiniteIntegralLattice
