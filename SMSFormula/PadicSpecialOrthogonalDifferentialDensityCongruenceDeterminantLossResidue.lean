import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceResidueCardinalityPrimePower
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityQuotientFiber

/-!
# The determinant-loss residue carrier at an odd prime

Reduction of form-adapted coordinates from level `k + v` to level `k` is a
canonical surjective homomorphism.  Its zero fiber has cardinal
`p ^ (v * d)`, where `d` is the skew-adjoint tangent rank.

For the selected density depth and `v = padicValInt p L.pairingDeterminant`, every
attained odd-prime density residue lies in this zero fiber.  This gives an
injection from the attained density residues into the determinant-loss
carrier.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : ℕ}

/-- Coordinatewise restriction of form-adapted residues from level `k + v`
to level `k`. -/
def skewAdjointFormElementaryPadicCoordinateResidueRestriction
    (p k v : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    skewAdjointFormElementaryPadicCoordinateResidue p (k + v) F →+
      skewAdjointFormElementaryPadicCoordinateResidue p k F where
  toFun x i :=
    ZMod.castHom (pow_dvd_pow p (Nat.le_add_right k v)) (ZMod (p ^ k)) (x i)
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    exact
      (ZMod.castHom (pow_dvd_pow p (Nat.le_add_right k v))
        (ZMod (p ^ k))).map_add (x i) (y i)

/-- Restriction of form-coordinate residues is surjective. -/
theorem skewAdjointFormElementaryPadicCoordinateResidueRestriction_surjective
    (p k v : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Function.Surjective
      (skewAdjointFormElementaryPadicCoordinateResidueRestriction
        p k v F) := by
  intro y
  choose x hx using fun i ↦
    ZMod.ringHom_surjective
      (ZMod.castHom (pow_dvd_pow p (Nat.le_add_right k v)) (ZMod (p ^ k)))
      (y i)
  refine ⟨x, ?_⟩
  funext i
  exact hx i

/-- Reducing integral form coordinates at level `k + v` and then restricting
is literally the level-`k` reduction. -/
theorem skewAdjointFormElementaryPadicCoordinateResidueRestriction_reduction
    (p k v : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p F hF hdet) :
    skewAdjointFormElementaryPadicCoordinateResidueRestriction p k v F
        (skewAdjointFormElementaryPadicCoordinateReduction
          p (k + v) F hF hdet x) =
      skewAdjointFormElementaryPadicCoordinateReduction p k F hF hdet x := by
  funext i
  exact PadicInt.cast_toZModPow k (k + v) (Nat.le_add_right k v) _

/-- The canonical determinant-loss carrier is the zero fiber of residue
restriction from level `k + v` to level `k`. -/
abbrev skewAdjointFormElementaryPadicCoordinateDeterminantLossResidue
    (p k v : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :=
  (skewAdjointFormElementaryPadicCoordinateResidueRestriction
    p k v F).ker

/-- The determinant-loss zero fiber has the expected cardinality. -/
theorem natCard_skewAdjointFormElementaryPadicCoordinateDeterminantLossResidue
    (p k v : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Nat.card
        (skewAdjointFormElementaryPadicCoordinateDeterminantLossResidue
          p k v F) =
      p ^
        (v * Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra F)) := by
  let f :=
    skewAdjointFormElementaryPadicCoordinateResidueRestriction p k v F
  have hcard := AddSubgroup.card_mul_index f.ker
  have hindex : f.ker.index =
      Nat.card
        (skewAdjointFormElementaryPadicCoordinateResidue p k F) := by
    rw [AddSubgroup.index_ker]
    have hrange : f.range = ⊤ :=
      AddMonoidHom.range_eq_top.mpr
        (skewAdjointFormElementaryPadicCoordinateResidueRestriction_surjective
          p k v F)
    rw [hrange]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  rw [hindex,
    natCard_skewAdjointFormElementaryPadicCoordinateResidue,
    natCard_skewAdjointFormElementaryPadicCoordinateResidue] at hcard
  have hpow :
      (p ^ (k + v)) ^
          Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) =
        p ^
            (v * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra F)) *
          (p ^ k) ^
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra F) := by
    calc
      (p ^ (k + v)) ^
          Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) =
          p ^ ((k + v) *
            Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) := by
        rw [Nat.pow_mul]
      _ = p ^
            (k * Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra F) +
              v * Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra F)) := by
        rw [Nat.add_mul]
      _ = p ^
              (v * Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra F)) *
            (p ^ k) ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra F) := by
        rw [Nat.pow_add, Nat.pow_mul]
        ac_rfl
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_right
    (pow_pos (pow_pos (Fact.out : Nat.Prime p).pos k) _)
    hcard

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Restriction from the prescribed determinant-loss residue level to the
selected density depth. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossRestriction
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :=
  skewAdjointFormElementaryPadicCoordinateResidueRestriction
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (padicValInt p L.pairingDeterminant)
    L.rationalFormMatrix

/-- The selected determinant-loss residue carrier. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :=
  skewAdjointFormElementaryPadicCoordinateDeterminantLossResidue
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (padicValInt p L.pairingDeterminant)
    L.rationalFormMatrix

/-- The selected determinant-loss residue carrier has cardinality exactly
the Gram-determinant loss prime power. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
          p) =
      p ^
        (padicValInt p L.pairingDeterminant *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) :=
  natCard_skewAdjointFormElementaryPadicCoordinateDeterminantLossResidue
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
    (padicValInt p L.pairingDeterminant)
    L.rationalFormMatrix

/-- Every attained odd-prime density residue restricts to zero at the selected
density depth. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex_restrictsToZero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      p) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossRestriction
        p a.1 = 0 := by
  let x :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
      p a
  have hxsource : x.1 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_mem_source
      p a
  have hxball : x.1 ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_subset_formElementaryUniformCoordinateBall
      p hp2 hxsource
  have hxzero :
      skewAdjointFormElementaryPadicCoordinateReduction
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero x = 0 :=
    (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero x).1 hxball
  rw [← L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_reduction
    p a]
  change
    skewAdjointFormElementaryPadicCoordinateResidueRestriction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        (padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix
        (skewAdjointFormElementaryPadicCoordinateReduction
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
            padicValInt p L.pairingDeterminant)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero x) = 0
  rw [skewAdjointFormElementaryPadicCoordinateResidueRestriction_reduction,
    hxzero]

/-- The attained odd-prime density residues inject canonically into the
determinant-loss zero fiber. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
        p →
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
        p :=
  fun a ↦
    ⟨a.1,
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex_restrictsToZero
        p hp2 a⟩

theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDeterminantLossResidue_injective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Function.Injective
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDeterminantLossResidue
        p hp2) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun z ↦ z.1) hab

/-- The attained odd-prime density residue image has cardinality at most the
determinant-loss prime power. -/
theorem
    ncard_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage_le_pairingDeterminantPrimePow
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
        p).ncard ≤
      p ^
        (padicValInt p L.pairingDeterminant *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) := by
  rw [← Nat.card_coe_set_eq,
    ← L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue
      p]
  exact Nat.card_le_card_of_injective
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDeterminantLossResidue
      p hp2)
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDeterminantLossResidue_injective
      p hp2)

end PositiveDefiniteIntegralLattice
