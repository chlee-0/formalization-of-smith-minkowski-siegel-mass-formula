import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeResidue

/-!
# The attained density residues as a determinant-loss subgroup

At an odd prime, this module packages the attained density-residue image as
an additive subgroup of the determinant-loss carrier.  Closure is transported
from the actual principal kernel through the surjective absolute Cayley
residue map; the density source itself is not assumed to be additively closed.

It also identifies equality of the absolute residues modulo this subgroup
with the literal relative principal-kernel relation.  No quotient equivalence,
cardinality, or gauge value is asserted.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- The prescribed residue of one absolute denominator-Cayley coordinate. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteFormCoordinateResidue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    Matrix.skewAdjointFormElementaryPadicCoordinateResidue
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel p)
      L.rationalFormMatrix :=
  Matrix.skewAdjointFormElementaryPadicCoordinateReduction
    p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel p)
    L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
      p hp2 g)

/-- Every absolute denominator-Cayley residue restricts to zero at the
selected density depth. -/
theorem
    absoluteFormCoordinateResidue_restrictsToZero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossRestriction p
        (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteFormCoordinateResidue
          p hp2 g) = 0 := by
  let x :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
      p hp2 g
  have hxball : x.1 ∈
      Matrix.skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_mem_formElementaryUniformCoordinateBall
      p hp2 g
  have hxzero :=
    (Matrix.mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero x).1 hxball
  change
    Matrix.skewAdjointFormElementaryPadicCoordinateResidueRestriction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        (padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix
        (Matrix.skewAdjointFormElementaryPadicCoordinateReduction
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
            padicValInt p L.pairingDeterminant)
          L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero x) = 0
  rw [Matrix.skewAdjointFormElementaryPadicCoordinateResidueRestriction_reduction,
    hxzero]

/-- The absolute coordinate residue as an element of the determinant-loss
zero fiber. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue p :=
  ⟨L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteFormCoordinateResidue
      p hp2 g,
    L.absoluteFormCoordinateResidue_restrictsToZero p hp2 g⟩

/-- The relative determinant-loss residue is the difference of the two
absolute determinant-loss residues. -/
theorem
    relativeDeterminantLossResidue_eq_sub_absolute
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeDeterminantLossResidue
        p hp2 g h =
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteDeterminantLossResidue
          p hp2 g -
        L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteDeterminantLossResidue
          p hp2 h := by
  apply Subtype.ext
  change
    Matrix.skewAdjointFormElementaryPadicCoordinateReduction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel p)
        L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
            p hp2 g -
          L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
            p hp2 h) = _
  exact map_sub _ _ _

/-- Every determinant-loss residue is the absolute residue of an element of
`H_k`. -/
theorem
    surjective_absoluteDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Function.Surjective
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteDeterminantLossResidue
        p hp2) := by
  intro t
  obtain ⟨x, hx⟩ :=
    Matrix.skewAdjointFormElementaryPadicCoordinateReduction_surjective
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel p)
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero t.1
  change
    Matrix.skewAdjointFormElementaryPadicCoordinateReduction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
          padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero x = t.1 at hx
  have hxzero :
      Matrix.skewAdjointFormElementaryPadicCoordinateReduction
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
          L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero x = 0 := by
    calc
      _ =
          Matrix.skewAdjointFormElementaryPadicCoordinateResidueRestriction
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
            (padicValInt p L.pairingDeterminant)
            L.rationalFormMatrix
            (Matrix.skewAdjointFormElementaryPadicCoordinateReduction
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
                padicValInt p L.pairingDeterminant)
              L.rationalFormMatrix (L.form_symm.map _)
              L.rationalFormMatrix_det_ne_zero x) :=
        (Matrix.skewAdjointFormElementaryPadicCoordinateResidueRestriction_reduction
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
          (padicValInt p L.pairingDeterminant)
          L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero x).symm
      _ =
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossRestriction
            p t.1 := by rw [hx]
      _ = 0 := t.2
  have hxball : x.1 ∈
      Matrix.skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero :=
    (Matrix.mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero x).2 hxzero
  let xb :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceFormCoordinateBall p :=
    ⟨x.1, hxball⟩
  let g :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceForwardCayley
      p hp2 xb
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change
    Matrix.skewAdjointFormElementaryPadicCoordinateReduction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel p)
        L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
          p hp2 g) = t.1
  have hinv :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_forwardCayley
      p hp2 xb
  have hpoint :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyFormCoordinatePoint
          p hp2 g = x := by
    apply Subtype.ext
    exact hinv
  rw [hpoint]
  change
    Matrix.skewAdjointFormElementaryPadicCoordinateReduction
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
          padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero x = t.1
  exact hx

/-- Relative principal-kernel membership is exactly attained-image membership
of the difference of the two absolute determinant-loss residues. -/
theorem
    mul_inv_mem_densityPrincipalKernel_iff_absoluteResidue_sub_mem_image
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteDeterminantLossResidue
            p hp2 g -
          L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteDeterminantLossResidue
            p hp2 h).1 ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage p := by
  rw [L.mul_inv_mem_densityPrincipalKernel_iff_relativeFormCoordinateResidue_mem_image
    p hp2 g h]
  rw [← L.relativeDeterminantLossResidue_eq_sub_absolute p hp2 g h]
  rfl

/-- The attained density residues, as an additive subgroup of the selected
determinant-loss carrier. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    AddSubgroup
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue p) where
  carrier := {t | t.1 ∈
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage p}
  zero_mem' := by
    obtain ⟨g, hg⟩ := L.surjective_absoluteDeterminantLossResidue p hp2 0
    have hk : g * g⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p := by
      simp
    have hm :=
      (L.mul_inv_mem_densityPrincipalKernel_iff_absoluteResidue_sub_mem_image
        p hp2 g g).1 hk
    simpa only [hg, sub_self] using hm
  add_mem' := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := L.surjective_absoluteDeterminantLossResidue p hp2 a
    obtain ⟨h, hh⟩ := L.surjective_absoluteDeterminantLossResidue p hp2 0
    obtain ⟨j, hj⟩ := L.surjective_absoluteDeterminantLossResidue p hp2 (-b)
    have hgk : g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p :=
      (L.mul_inv_mem_densityPrincipalKernel_iff_absoluteResidue_sub_mem_image
        p hp2 g h).2 (by simpa only [hg, hh, sub_zero] using ha)
    have hhk : h * j⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p :=
      (L.mul_inv_mem_densityPrincipalKernel_iff_absoluteResidue_sub_mem_image
        p hp2 h j).2 (by simpa only [hh, hj, zero_sub, neg_neg] using hb)
    have hprod :=
      (L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p).mul_mem
        hgk hhk
    have hgj : g * j⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p := by
      have heq : (g * h⁻¹) * (h * j⁻¹) = g * j⁻¹ := by group
      rw [heq] at hprod
      exact hprod
    have hm :=
      (L.mul_inv_mem_densityPrincipalKernel_iff_absoluteResidue_sub_mem_image
        p hp2 g j).1 hgj
    simpa only [hg, hj, sub_neg_eq_add] using hm
  neg_mem' := by
    intro a ha
    obtain ⟨g, hg⟩ := L.surjective_absoluteDeterminantLossResidue p hp2 a
    obtain ⟨h, hh⟩ := L.surjective_absoluteDeterminantLossResidue p hp2 0
    have hk : g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p :=
      (L.mul_inv_mem_densityPrincipalKernel_iff_absoluteResidue_sub_mem_image
        p hp2 g h).2 (by simpa only [hg, hh, sub_zero] using ha)
    have hreverse : h * g⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p := by
      change
        L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p
            (h * g⁻¹) = 1
      change
        L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p
            (g * h⁻¹) = 1 at hk
      simp only [map_mul, map_inv] at hk ⊢
      exact mul_inv_eq_one.mpr (mul_inv_eq_one.mp hk).symm
    have hm :=
      (L.mul_inv_mem_densityPrincipalKernel_iff_absoluteResidue_sub_mem_image
        p hp2 h g).1 hreverse
    simpa only [hh, hg, zero_sub] using hm

/-- The subgroup membership predicate is definitionally the original attained
residue-image predicate. -/
theorem mem_attainedResidueAddSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (t : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue p) :
    t ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
          p hp2 ↔
      t.1 ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage p :=
  Iff.rfl

/-- The newly packaged subgroup has exactly the existing attained-residue
subtype as its carrier. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexEquivAttainedResidueAddSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex p ≃
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
        p hp2 where
  toFun a :=
    ⟨L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDeterminantLossResidue
        p hp2 a,
      a.2⟩
  invFun t := ⟨t.1.1, t.2⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The finite additive quotient `T/N` determined by the attained density
residues. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :=
  L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossResidue p ⧸
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
      p hp2

/-- The absolute Cayley residue followed by the quotient map `T → T/N`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceToDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p →
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDeterminantLossQuotient p hp2 :=
  fun g ↦
    QuotientAddGroup.mk'
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
        p hp2)
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteDeterminantLossResidue
        p hp2 g)

/-- The absolute Cayley residue map is still surjective after passing to the
attained-residue quotient. -/
theorem
    surjective_denominatorCongruenceToDeterminantLossQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Function.Surjective
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceToDeterminantLossQuotient
        p hp2) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro t
  obtain ⟨g, hg⟩ := L.surjective_absoluteDeterminantLossResidue p hp2 t
  refine ⟨g, ?_⟩
  change
    (QuotientAddGroup.mk'
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
          p hp2))
        (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteDeterminantLossResidue
          p hp2 g) =
      (QuotientAddGroup.mk'
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
          p hp2)) t
  rw [hg]

/-- Equality of absolute Cayley residues modulo the attained subgroup is
exactly relative principal-kernel membership. -/
theorem
    denominatorCongruenceToDeterminantLossQuotient_eq_iff_mul_inv_mem_principalKernel
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceToDeterminantLossQuotient
        p hp2 g =
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceToDeterminantLossQuotient
        p hp2 h ↔
      g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p := by
  let A :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteDeterminantLossResidue
      p hp2 g
  let B :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceAbsoluteDeterminantLossResidue
      p hp2 h
  have hneg :
      -A + B ∈
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
            p hp2 ↔
        A - B ∈
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
            p hp2 := by
    constructor
    · intro hab
      have :=
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
          p hp2).neg_mem hab
      simpa only [neg_add_rev, neg_neg, sub_eq_add_neg, add_comm] using this
    · intro hab
      have :=
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
          p hp2).neg_mem hab
      simpa only [neg_add_rev, neg_neg, sub_eq_add_neg, add_comm] using this
  dsimp only [
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceToDeterminantLossQuotient,
    A, B]
  change
    (QuotientAddGroup.mk'
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
          p hp2)) A =
      (QuotientAddGroup.mk'
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
          p hp2)) B ↔ _
  exact
    (show
        (QuotientAddGroup.mk'
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
              p hp2)) A =
          (QuotientAddGroup.mk'
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
              p hp2)) B ↔
            -A + B ∈
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAttainedResidueAddSubgroup
                p hp2 from
      QuotientAddGroup.eq).trans
      (hneg.trans
        (L.mul_inv_mem_densityPrincipalKernel_iff_absoluteResidue_sub_mem_image
          p hp2 g h).symm)

end PositiveDefiniteIntegralLattice
