import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup

/-!
# Principal kernel and denominator-congruence fiber torsor

At an odd prime, this module places the selected-depth principal congruence
kernel inside the denominator-congruence subgroup `H_k`.  It then identifies
the quotient by that kernel with every ordinary reduction fiber over the
selected associated-bilinear quotient family, using the selected Hensel lift
as basepoint.

No Cayley-coordinate description of this quotient, determinant-loss residue
comparison, cardinality value, or gauge formula is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The selected-depth reduction homomorphism restricted to the
denominator-congruence subgroup. -/
def localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p →*
      GL (Fin n)
        (ZMod
          (p ^ L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)) :=
  (L.localPadicLatticeStabilizerReduction p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)).comp
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p).subtype

/-- The selected principal kernel, regarded as a normal subgroup of `H_k`. -/
def localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Subgroup
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :=
  (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p).ker

/-- Membership in the principal kernel inside `H_k` is exactly membership of
the underlying stabilizer in the original selected-depth principal
congruence subgroup. -/
theorem
    mem_localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    g ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p ↔
      g.1 ∈ L.localPadicPrincipalCongruenceSubgroup p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) :=
  Iff.rfl

/-- At an odd prime, every selected-depth principal-congruence element belongs
to the denominator-congruence subgroup. -/
theorem localPadicPrincipalCongruenceSubgroup_le_densityDenominatorCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicPrincipalCongruenceSubgroup p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) ≤
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p := by
  intro g hg
  rw [localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup,
    L.mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff]
  intro j
  apply L.mem_localDualPadicDenominator_of_forall_coord_primePow_dvd
  intro i
  rw [L.mem_localPadicPrincipalCongruenceSubgroup_iff] at hg
  have hij := hg i j
  apply Ideal.mem_span_singleton.mp
  rw [← PadicInt.ker_toZModPow
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p),
    RingHom.mem_ker]
  rw [map_sub]
  exact sub_eq_zero.mpr (hij.trans (by
    by_cases hii : i = j
    · subst j
      simp
    · simp [hii]))

local instance
    localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence_normal
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p).Normal := by
  change
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p).ker.Normal
  infer_instance

/-- The quotient `H_k/K_k`, with normality inherited literally from the
kernel of the restricted reduction homomorphism. -/
abbrev localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :=
  L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p ⧸
    L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDenominatorCongruence p

/-- The quotient `H_k/K_k` is canonically the range of selected-depth
reduction restricted to `H_k`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientEquivReductionRange
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotient p ≃*
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p).range :=
  QuotientGroup.quotientKerEquivRange
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p)

/-- The range of `H_k` reduction, translated by the selected Hensel
basepoint, is exactly the ordinary reduction fiber over `Y`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReductionRangeEquivOrdinaryReductionFiber
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p).range ≃
      {u :
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p //
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            p u = Y} where
  toFun x := by
    let b :=
      L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
        p Y
    let hY :=
      L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyHenselStabilizer p Y
    let t := Classical.choose x.2
    have ht :
        L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p t =
          x.1 :=
      Classical.choose_spec x.2
    let u : L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p :=
      ⟨x.1 * b.1, by
        refine ⟨t.1 * hY, ?_⟩
        simp only [map_mul]
        change
          L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p t *
              L.localPadicLatticeStabilizerReduction p
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) hY =
            x.1 * b.1
        rw [ht]
        rfl⟩
    refine ⟨u, ?_⟩
    have huval :
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer p
            (t.1 * hY) = u := by
      apply Subtype.ext
      simp only [localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer,
        map_mul]
      change
        L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReduction p t *
            L.localPadicLatticeStabilizerReduction p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) hY =
          x.1 * b.1
      rw [ht]
      rfl
    rw [← L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_apply_lift
      p Y]
    rw [← huval]
    apply
      (L.mul_inv_mem_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup_iff_quotient_eq
        p hp2 (t.1 * hY) hY).mp
    convert t.2 using 1
    simp
  invFun u := by
    let b :=
      L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyToOrdinaryReductionRange
        p Y
    refine ⟨u.1.1 * b.1⁻¹, ?_⟩
    rcases u.1.2 with ⟨g, hg⟩
    let hY :=
      L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyHenselStabilizer p Y
    have hquot :
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer p g) =
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer p hY) := by
      rw [show
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionOfStabilizer p g =
            u.1 by
          apply Subtype.ext
          exact hg]
      rw [u.2]
      exact
        (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily_apply_lift
          p Y).symm
    have ht : g * hY⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p :=
      (L.mul_inv_mem_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup_iff_quotient_eq
        p hp2 g hY).2 hquot
    refine ⟨⟨g * hY⁻¹, ht⟩, ?_⟩
    change
      L.localPadicLatticeStabilizerReduction p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
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

/-- Every ordinary selected quotient fiber is explicitly a torsor carrier for
the quotient `H_k/K_k`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientEquivOrdinaryReductionFiber
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotient p ≃
      {u :
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p //
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            p u = Y} :=
  (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientEquivReductionRange
      p).toEquiv.trans
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceReductionRangeEquivOrdinaryReductionFiber
      p hp2 Y)

/-- The exact liftable fiber is explicitly equivalent to `H_k/K_k`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiberEquivDenominatorCongruenceQuotient
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p) :
    L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber p hp2 Y ≃
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotient p :=
  (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiberEquivOrdinaryReductionFiber
      p hp2 Y).trans
    (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientEquivOrdinaryReductionFiber
      p hp2 Y).symm

end PositiveDefiniteIntegralLattice
