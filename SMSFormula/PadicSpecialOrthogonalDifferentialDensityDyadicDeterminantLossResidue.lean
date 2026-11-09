import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicResidueCardinalityBoundary
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue

/-!
# The one-power-enlarged dyadic determinant-loss residue carrier

The dyadic inverse-Cayley coordinate is known only through level `k - 1`,
where `k` is the selected density depth.  Accordingly the finite carrier
relevant to the dyadic gauge identity is the kernel of form-coordinate residue
restriction from level `k + v₂(pairingDeterminant)` to level `k - 1`.  Its loss is
`v₂(pairingDeterminant) + 1`, not merely `v₂(pairingDeterminant)`.

This module defines that carrier, proves its exact cardinality, and injects
the attained dyadic density residues into it using the outer
containment theorem.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The prescribed dyadic form-coordinate residue level is the one-power-
enlarged loss level above `densityDepth - 1`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinateResidueLevel_eq_pred_add_succ_pairingDeterminantVal
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        2 =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1) +
        (padicValInt 2 L.pairingDeterminant + 1) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold
    localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
  have hk :=
    L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  omega

/-- Restriction from the prescribed dyadic residue level to the certified
outer-coordinate depth `densityDepth - 1`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction
    (L : PositiveDefiniteIntegralLattice n) :
    skewAdjointFormElementaryPadicCoordinateResidue
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix →+
      skewAdjointFormElementaryPadicCoordinateResidue
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
          L.rationalFormMatrix := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle :
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1 ≤
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2 := by
    unfold
      localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
    omega
  exact
    { toFun := fun x i ↦
        ZMod.castHom (pow_dvd_pow 2 hle)
          (ZMod
            (2 ^
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                2 - 1))) (x i)
      map_zero' := by
        funext i
        simp
      map_add' := by
        intro x y
        funext i
        exact
          (ZMod.castHom (pow_dvd_pow 2 hle)
            (ZMod
              (2 ^
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                  2 - 1)))).map_add (x i) (y i) }

/-- Restricting an integral coordinate from the original dyadic residue
level gives literally its reduction at `densityDepth - 1`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction_reduction
    (L : PositiveDefiniteIntegralLattice n)
    (x : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      2 L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction
        (skewAdjointFormElementaryPadicCoordinateReduction
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero x) =
      skewAdjointFormElementaryPadicCoordinateReduction
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero x := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle :
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1 ≤
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2 := by
    unfold
      localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
    omega
  funext i
  exact
    PadicInt.cast_toZModPow
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        2)
      hle _

/-- The direct dyadic restriction from the original attained-residue level
to `densityDepth - 1` is surjective. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction_surjective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Surjective
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle :
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1 ≤
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2 := by
    unfold
      localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
    omega
  intro y
  choose x hx using fun i ↦
    ZMod.ringHom_surjective
      (ZMod.castHom (pow_dvd_pow 2 hle)
        (ZMod
          (2 ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              2 - 1))))
      (y i)
  refine ⟨x, ?_⟩
  funext i
  exact hx i

/-- The enlarged dyadic determinant-loss carrier is the zero fiber of
restriction from level `k + v₂(pairingDeterminant)` to level `k - 1`. -/
abbrev
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n) :=
  L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction.ker

/-- The enlarged dyadic determinant-loss carrier has exactly the prime-power
cardinality forced by the one-level inverse-Cayley loss. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n) :
    Nat.card
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue =
      2 ^
        ((padicValInt 2 L.pairingDeterminant + 1) *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction
  have hcard := AddSubgroup.card_mul_index f.ker
  have hindex : f.ker.index =
      Nat.card
        (skewAdjointFormElementaryPadicCoordinateResidue
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
          L.rationalFormMatrix) := by
    rw [AddSubgroup.index_ker]
    have hrange : f.range = ⊤ :=
      AddMonoidHom.range_eq_top.mpr
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction_surjective
    rw [hrange]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  rw [hindex,
    natCard_skewAdjointFormElementaryPadicCoordinateResidue,
    natCard_skewAdjointFormElementaryPadicCoordinateResidue] at hcard
  have hpow :
      (2 ^
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2) ^
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) =
        2 ^
            ((padicValInt 2 L.pairingDeterminant + 1) *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          (2 ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)) ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) := by
    calc
      (2 ^
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2) ^
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) =
        2 ^
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2 *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) := by
          rw [Nat.pow_mul]
      _ = 2 ^
          (((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1) +
              (padicValInt 2 L.pairingDeterminant + 1)) *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) := by
          rw [L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinateResidueLevel_eq_pred_add_succ_pairingDeterminantVal]
      _ = 2 ^
            ((padicValInt 2 L.pairingDeterminant + 1) *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          (2 ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)) ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) := by
          rw [Nat.add_mul, Nat.pow_add, Nat.pow_mul]
          ac_rfl
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_right
    (pow_pos
      (pow_pos (by norm_num : 0 < 2)
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1))
      (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))
    hcard

/-- Every attained dyadic density residue restricts to zero at the certified
outer-coordinate depth `densityDepth - 1`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex_dyadic_restrictsToZero
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction
        a.1 = 0 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let x :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
      2 a
  have hxsource : x.1 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_mem_source
      2 a
  have hxball : x.1 ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
    L.localPadicSpecialOrthogonalDifferentialDyadicDensityCongruenceSourceAmbientSet_subset_formElementaryUniformCoordinateBall_pred
      hxsource
  have hxzero :
      skewAdjointFormElementaryPadicCoordinateReduction
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero x = 0 :=
    (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero x).1 hxball
  rw [← L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_reduction
    2 a]
  rw [L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction_reduction,
    hxzero]

/-- The attained dyadic density residues inject canonically into the enlarged
determinant-loss zero fiber. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDyadicDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
        2 →
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue :=
  fun a ↦
    ⟨a.1,
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex_dyadic_restrictsToZero
        a⟩

theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDyadicDeterminantLossResidue_injective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Injective
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDyadicDeterminantLossResidue := by
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun z ↦ z.1) hab

/-- The attained dyadic residue count is bounded by the exact enlarged
determinant-loss prime power. -/
theorem
    ncard_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage_le_dyadicDeterminantLossPrimePow
    (L : PositiveDefiniteIntegralLattice n) :
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
        2).ncard ≤
      2 ^
        ((padicValInt 2 L.pairingDeterminant + 1) *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) := by
  rw [← Nat.card_coe_set_eq,
    ← L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue]
  exact Nat.card_le_card_of_injective
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDyadicDeterminantLossResidue
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDyadicDeterminantLossResidue_injective

end PositiveDefiniteIntegralLattice
