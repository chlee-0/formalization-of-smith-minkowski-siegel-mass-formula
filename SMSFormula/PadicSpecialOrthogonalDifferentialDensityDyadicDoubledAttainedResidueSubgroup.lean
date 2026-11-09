import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDoubledAttainedResidueCardinality

/-!
# The doubled attained dyadic residues as an additive subgroup

The scaled dyadic Cayley residue map from the shifted denominator subgroup
`H₂` onto the enlarged determinant-loss carrier `T₂` is surjective.  Its
relative depth-`k` principal-kernel relation is exactly membership of the
difference of two scaled residues in the literal doubled original attained
image.

This module transports reflexivity, composition, and symmetry of that actual
group relation through surjectivity to prove that the doubled attained image
is an additive subgroup of `T₂`.  It then identifies equality of the absolute
scaled-residue classes modulo this subgroup with the same literal relative
principal-kernel condition.  No quotient equivalence, cardinality identity,
or gauge value is asserted.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_doubled_attained_subgroup : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The doubled original attained residues, packaged as an additive
subgroup of the enlarged dyadic determinant-loss carrier.  Closure is
transported from the actual relative principal-kernel relation; the
original density source is not assumed to be additively closed. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    AddSubgroup
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue where
  carrier :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueSet
  zero_mem' := by
    obtain ⟨g, hg⟩ :=
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue_surjective
        0
    have hk : g * g⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence := by
      simp
    have hm :=
      (L.mul_inv_mem_dyadicDensityPrincipalKernel_iff_scaledDifferenceResidue_mem_doubledAttainedResidueSet
        g g).1 hk
    simpa only [
      localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue,
      hg, sub_self] using hm
  add_mem' := by
    intro a b ha hb
    obtain ⟨g, hg⟩ :=
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue_surjective
        a
    obtain ⟨h, hh⟩ :=
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue_surjective
        0
    obtain ⟨j, hj⟩ :=
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue_surjective
        (-b)
    have hgk : g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence :=
      (L.mul_inv_mem_dyadicDensityPrincipalKernel_iff_scaledDifferenceResidue_mem_doubledAttainedResidueSet
        g h).2 (by
          simpa only [
            localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue,
            hg, hh, sub_zero] using ha)
    have hhk : h * j⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence :=
      (L.mul_inv_mem_dyadicDensityPrincipalKernel_iff_scaledDifferenceResidue_mem_doubledAttainedResidueSet
        h j).2 (by
          simpa only [
            localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue,
            hh, hj, zero_sub, neg_neg] using hb)
    have hprod :=
      L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence.mul_mem
        hgk hhk
    have hgj : g * j⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence := by
      have heq : (g * h⁻¹) * (h * j⁻¹) = g * j⁻¹ := by group
      rw [heq] at hprod
      exact hprod
    have hm :=
      (L.mul_inv_mem_dyadicDensityPrincipalKernel_iff_scaledDifferenceResidue_mem_doubledAttainedResidueSet
        g j).1 hgj
    simpa only [
      localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue,
      hg, hj, sub_neg_eq_add] using hm
  neg_mem' := by
    intro a ha
    obtain ⟨g, hg⟩ :=
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue_surjective
        a
    obtain ⟨h, hh⟩ :=
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue_surjective
        0
    have hk : g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence :=
      (L.mul_inv_mem_dyadicDensityPrincipalKernel_iff_scaledDifferenceResidue_mem_doubledAttainedResidueSet
        g h).2 (by
          simpa only [
            localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue,
            hg, hh, sub_zero] using ha)
    have hreverse : h * g⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence := by
      change
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction
            (h * g⁻¹) = 1
      change
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction
            (g * h⁻¹) = 1 at hk
      simp only [map_mul, map_inv] at hk ⊢
      exact mul_inv_eq_one.mpr (mul_inv_eq_one.mp hk).symm
    have hm :=
      (L.mul_inv_mem_dyadicDensityPrincipalKernel_iff_scaledDifferenceResidue_mem_doubledAttainedResidueSet
        h g).1 hreverse
    simpa only [
      localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue,
      hh, hg, zero_sub] using hm

/-- Membership in the newly packaged subgroup is definitionally membership in
the literal doubled attained residue set. -/
theorem mem_dyadicDoubledAttainedResidueAddSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n)
    (t :
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue) :
    t ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup ↔
      t ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueSet :=
  Iff.rfl

/-- The additive subgroup carrier is explicitly equivalent to the original
doubled attained image subtype. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndexEquivAddSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex ≃
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup where
  toFun t := ⟨t.1, t.2⟩
  invFun t := ⟨t.1, t.2⟩
  left_inv t := by
    apply Subtype.ext
    rfl
  right_inv t := by
    apply Subtype.ext
    rfl

/-- The finite additive quotient of `T₂` by the doubled original attained
residue subgroup. -/
abbrev
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) :=
  L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue ⧸
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup

/-- The absolute scaled dyadic residue followed by the quotient map
`T₂ -> T₂/N₂'`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceToDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup →
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossQuotient :=
  fun g ↦
    QuotientAddGroup.mk'
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue
        g)

/-- The absolute scaled-residue class remains surjective after quotienting by
the doubled attained subgroup. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceToDeterminantLossQuotient_surjective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Surjective
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceToDeterminantLossQuotient := by
  intro q
  refine Quotient.inductionOn q ?_
  intro t
  obtain ⟨g, hg⟩ :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue_surjective
      t
  refine ⟨g, ?_⟩
  change
    (QuotientAddGroup.mk'
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup)
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue
          g) =
      (QuotientAddGroup.mk'
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup)
        t
  rw [hg]

/-- Equality of absolute scaled Cayley residues modulo the doubled attained
subgroup is exactly relative depth-`k` principal-kernel membership. -/
theorem
    dyadicDenominatorCongruenceToDeterminantLossQuotient_eq_iff_mul_inv_mem_principalKernel
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceToDeterminantLossQuotient
        g =
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceToDeterminantLossQuotient
        h ↔
      g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence := by
  let A :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue
      g
  let B :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue
      h
  have hneg :
      -A + B ∈
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup ↔
        A - B ∈
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup := by
    constructor
    · intro hab
      have :=
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup.neg_mem
          hab
      simpa only [neg_add_rev, neg_neg, sub_eq_add_neg, add_comm] using this
    · intro hab
      have :=
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup.neg_mem
          hab
      simpa only [neg_add_rev, neg_neg, sub_eq_add_neg, add_comm] using this
  have hrelative :
      A - B ∈
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup ↔
        g * h⁻¹ ∈
          L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence := by
    change
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
            g h ∈
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueSet ↔
        _
    exact
      (L.mul_inv_mem_dyadicDensityPrincipalKernel_iff_scaledDifferenceResidue_mem_doubledAttainedResidueSet
        g h).symm
  dsimp only [
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceToDeterminantLossQuotient,
    A, B]
  change
    (QuotientAddGroup.mk'
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup) A =
      (QuotientAddGroup.mk'
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup) B ↔
      _
  exact
    (show
        (QuotientAddGroup.mk'
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup) A =
          (QuotientAddGroup.mk'
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup) B ↔
          -A + B ∈
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueAddSubgroup from
      QuotientAddGroup.eq).trans
      (hneg.trans hrelative)

end PositiveDefiniteIntegralLattice
