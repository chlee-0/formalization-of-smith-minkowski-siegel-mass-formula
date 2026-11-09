import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup

/-!
# The shifted dyadic denominator-congruence fiber torsor

This module restricts the complete selected-depth dyadic stabilizer reduction
to the shifted denominator-congruence subgroup `H₂`.  Its kernel is the
original principal congruence subgroup at the unreduced depth `k`, and the
resulting quotient is identified explicitly with every ordinary reduction
fiber over the associated-bilinear quotient family.

No attained-residue subgroup, enlarged determinant-loss quotient,
cardinality, or dyadic gauge value is constructed here.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Complete depth-`k` dyadic reduction restricted to the shifted subgroup
defined by the local-dual denominator at depth `k - 1`. -/
def localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup →*
      GL (Fin n)
        (ZMod
          (2 ^ L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)) :=
  (L.localPadicLatticeStabilizerReduction 2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)).comp
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup.subtype

/-- The complete depth-`k` principal kernel inside the shifted dyadic
denominator-congruence subgroup. -/
def
    localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence
    (L : PositiveDefiniteIntegralLattice n) :
    Subgroup
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup :=
  L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction.ker

/-- Membership in the restricted kernel is literally membership of the
underlying stabilizer in the original principal subgroup at depth `k`. -/
theorem
    mem_localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    g ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence ↔
      g.1 ∈ L.localPadicPrincipalCongruenceSubgroup 2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2) :=
  Iff.rfl

/-- Every complete depth-`k` dyadic principal-congruence element belongs to
the shifted subgroup `H₂`; the ordinary reduction depth is not lowered. -/
theorem
    localPadicPrincipalCongruenceSubgroup_le_densityDyadicDenominatorCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicPrincipalCongruenceSubgroup 2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2) ≤
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup := by
  intro g hg
  rw [localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup,
    L.mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff]
  intro j
  rw [←
    L.associatedBilinearDualPadicDenominator_densityDepth_eq_localDualPadicDenominator_pred_dyadic]
  apply L.mem_associatedBilinearDualPadicDenominator_of_forall_coord_primePow_dvd
  intro i
  rw [L.mem_localPadicPrincipalCongruenceSubgroup_iff] at hg
  have hij := hg i j
  apply Ideal.mem_span_singleton.mp
  rw [← PadicInt.ker_toZModPow
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2),
    RingHom.mem_ker]
  rw [map_sub]
  exact sub_eq_zero.mpr (hij.trans (by
    by_cases hii : i = j
    · subst j
      simp
    · simp [hii]))

local instance
    localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence_normal
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence.Normal := by
  change
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction.ker.Normal
  infer_instance

/-- The shifted dyadic quotient `H₂/K₂`, with normality inherited from the
kernel of complete depth-`k` reduction. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotient
    (L : PositiveDefiniteIntegralLattice n) :=
  L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup ⧸
    L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence

/-- The quotient `H₂/K₂` is canonically the range of complete depth-`k`
reduction restricted to `H₂`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientEquivReductionRange
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotient ≃*
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction.range :=
  QuotientGroup.quotientKerEquivRange
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction

/-- Translation by the selected dyadic Hensel basepoint identifies the range
of `H₂` reduction with the complete ordinary reduction fiber over `Y`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReductionRangeEquivOrdinaryReductionFiber
    (L : PositiveDefiniteIntegralLattice n)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        2) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction.range ≃
      {u :
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange 2 //
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            2 u = Y} where
  toFun x := by
    let b :=
      L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
        2 Y
    let hY :=
      L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyHenselStabilizer 2 Y
    let t := Classical.choose x.2
    have ht :
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction t =
          x.1 :=
      Classical.choose_spec x.2
    let u : L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange 2 :=
      ⟨x.1 * b.1, by
        refine ⟨t.1 * hY, ?_⟩
        simp only [map_mul]
        change
          L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction t *
              L.localPadicLatticeStabilizerReduction 2
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2) hY =
            x.1 * b.1
        rw [ht]
        rfl⟩
    refine ⟨u, ?_⟩
    have huval :
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer 2
            (t.1 * hY) = u := by
      apply Subtype.ext
      simp only [localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer,
        map_mul]
      change
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReduction t *
            L.localPadicLatticeStabilizerReduction 2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2) hY =
          x.1 * b.1
      rw [ht]
      rfl
    rw [←
      L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_apply_lift
        2 Y]
    rw [← huval]
    apply
      (L.mul_inv_mem_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup_iff_quotient_eq
        (t.1 * hY) hY).mp
    convert t.2 using 1
    simp
  invFun u := by
    let b :=
      L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
        2 Y
    refine ⟨u.1.1 * b.1⁻¹, ?_⟩
    rcases u.1.2 with ⟨g, hg⟩
    let hY :=
      L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyHenselStabilizer 2 Y
    have hquot :
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            2
            (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer 2 g) =
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            2
            (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer 2 hY) := by
      rw [show
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer 2 g =
            u.1 by
          apply Subtype.ext
          exact hg]
      rw [u.2]
      exact
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_apply_lift
          2 Y).symm
    have ht : g * hY⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup :=
      (L.mul_inv_mem_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup_iff_quotient_eq
        g hY).2 hquot
    refine ⟨⟨g * hY⁻¹, ht⟩, ?_⟩
    change
      L.localPadicLatticeStabilizerReduction 2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)
          (g * hY⁻¹) = u.1.1 * b.1⁻¹
    simp only [map_mul, map_inv]
    rw [hg]
    rfl
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- Every complete ordinary dyadic quotient fiber is explicitly the torsor
carrier `H₂/K₂`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientEquivOrdinaryReductionFiber
    (L : PositiveDefiniteIntegralLattice n)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        2) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotient ≃
      {u :
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange 2 //
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            2 u = Y} :=
  L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceQuotientEquivReductionRange.toEquiv.trans
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceReductionRangeEquivOrdinaryReductionFiber
      Y)

end PositiveDefiniteIntegralLattice
