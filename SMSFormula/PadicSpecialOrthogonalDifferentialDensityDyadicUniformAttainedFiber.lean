import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicPredecessorTranslation

/-!
# Uniform dyadic attained doubling fibers

The predecessor-level translation theorem makes the attained dyadic residue
image saturated under the one-layer kernel of residue restriction.  This
module packages that kernel, proves its cardinality, and constructs a
translation equivalence from it to every attained predecessor-restriction
fiber.  The equivalence between predecessor fibers and
doubling fibers then gives the uniform cardinal `2^d`.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_uniform_attained_fiber : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The one-layer kernel from the original dyadic residue level to its
predecessor. -/
abbrev
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredKernel
    (L : PositiveDefiniteIntegralLattice n) :=
  L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction.ker

/-- Direct predecessor restriction of the original dyadic form-coordinate
residue carrier is surjective. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction_surjective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Surjective
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction := by
  intro y
  choose x hx using fun i ↦
    ZMod.ringHom_surjective
      (ZMod.castHom
        (pow_dvd_pow 2
          (Nat.sub_le
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2) 1))
        (ZMod
          (2 ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
                2 - 1))))
      (y i)
  refine ⟨x, ?_⟩
  funext i
  exact hx i

/-- The one forgotten binary residue layer has cardinal `2^d`. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredKernel
    (L : PositiveDefiniteIntegralLattice n) :
    Nat.card
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredKernel =
      2 ^ Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) := by
  let m :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
      2
  let d := Module.finrank ℚ
    (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)
  let f :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
  have hm : 1 ≤ m := by
    dsimp [m]
    unfold
      localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
    have hk :=
      L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
    omega
  have hcard := AddSubgroup.card_mul_index f.ker
  have hindex : f.ker.index =
      Nat.card
        (skewAdjointFormElementaryPadicCoordinateResidue
          2 (m - 1) L.rationalFormMatrix) := by
    rw [AddSubgroup.index_ker]
    have hrange : f.range = ⊤ :=
      AddMonoidHom.range_eq_top.mpr
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction_surjective
    rw [hrange]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  change Nat.card f.ker = 2 ^ d
  rw [hindex,
    natCard_skewAdjointFormElementaryPadicCoordinateResidue,
    natCard_skewAdjointFormElementaryPadicCoordinateResidue] at hcard
  have hpow :
      (2 ^ m) ^ d = 2 ^ d * (2 ^ (m - 1)) ^ d := by
    calc
      (2 ^ m) ^ d = 2 ^ (m * d) := by rw [Nat.pow_mul]
      _ = 2 ^ (((m - 1) + 1) * d) := by rw [Nat.sub_add_cancel hm]
      _ = 2 ^ d * (2 ^ (m - 1)) ^ d := by
        rw [Nat.add_mul, Nat.pow_add, Nat.pow_mul]
        simp only [one_mul]
        ac_rfl
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_right
    (pow_pos
      (pow_pos (by norm_num : 0 < 2) (m - 1)) d)
    hcard

/-- Any residue with the same predecessor restriction as an attained dyadic
residue is itself attained. -/
theorem
    mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage_two_of_predRestriction_eq
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2)
    (b : skewAdjointFormElementaryPadicCoordinateResidue
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        2)
      L.rationalFormMatrix)
    (hpred :
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
          b =
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
          a.1) :
    b ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
        2 := by
  let m :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
      2
  obtain ⟨Y, hYred⟩ :=
    skewAdjointFormElementaryPadicCoordinateReduction_surjective
      2 m L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero (b - a.1)
  have hYpredzero :
      skewAdjointFormElementaryPadicCoordinateReduction
          2 (m - 1) L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero Y = 0 := by
    rw [←
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction_reduction,
      hYred, map_sub, hpred, sub_self]
  have hYball : Y.1 ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2 (m - 1) L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
    (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
      2 (m - 1) L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero Y).2 hYpredzero
  let X :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
      2 a
  have hXsource : X.1 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_mem_source
      2 a
  have hsumsource : X.1 + Y.1 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 := by
    apply
      (L.add_mem_dyadicDensityCongruenceSourceAmbientSet_iff_of_mem_formElementaryBall_pred_residueLevel
        X.1 Y.1 hYball).2
    exact hXsource
  refine ⟨X + Y, hsumsource, ?_⟩
  rw [map_add,
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_reduction,
    hYred]
  abel

/-- Translation by a fixed attained residue identifies the one-layer kernel
with its complete attained predecessor-restriction fiber. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredKernelEquivAttainedPredRestrictionFiber
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredKernel ≃
      {b :
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
            2 //
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
            b.1 =
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
            a.1} where
  toFun z := by
    have hpred :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
            (a.1 + z.1) =
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
            a.1 := by
      rw [map_add]
      have hz := z.2
      rw [AddMonoidHom.mem_ker] at hz
      rw [hz, add_zero]
    exact
      ⟨⟨a.1 + z.1,
          L.mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage_two_of_predRestriction_eq
            a (a.1 + z.1) hpred⟩,
        hpred⟩
  invFun b := by
    refine ⟨b.1.1 - a.1, ?_⟩
    rw [AddMonoidHom.mem_ker, map_sub, b.2, sub_self]
  left_inv z := by
    apply Subtype.ext
    change (a.1 + z.1) - a.1 = z.1
    abel
  right_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    change a.1 + (b.1.1 - a.1) = b.1.1
    abel

/-- Every attained predecessor-restriction fiber has the full one-layer
cardinality `2^d`. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicAttainedPredRestrictionFiber
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2) :
    Nat.card
        {b :
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
              2 //
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
              b.1 =
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredRestriction
              a.1} =
      2 ^ Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) := by
  rw [←
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredKernel]
  exact Nat.card_congr
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResiduePredKernelEquivAttainedPredRestrictionFiber
      a).symm

/-- Every fiber of doubling on the original attained dyadic residue carrier
has cardinal `2^d`. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueFiber
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
      2 ^ Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) := by
  rw [L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueFiber_eq_predRestrictionFiber]
  exact
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicAttainedPredRestrictionFiber
      a

end PositiveDefiniteIntegralLattice
