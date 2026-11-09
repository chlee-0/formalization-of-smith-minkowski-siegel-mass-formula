import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRelativeDenominatorCongruence

/-!
# P-adic denominator stability for relative quotient fibers

This module lifts the literal finite-ring denominator congruence on an
associated-bilinear quotient fiber to the actual integral p-adic matrices.
It also proves that the integral matrix of every local lattice stabilizer
preserves the local-dual denominator under `mulVec`; away from two this is the
associated-bilinear denominator used by the selected quotient family.

These are the two inputs needed before defining the intermediate
denominator-congruence subgroup `H_k`.  No such subgroup, quotient, torsor, or
Cayley equivalence is defined here.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The integral matrix of a local lattice stabilizer preserves the depth-`k`
local-dual p-adic denominator. -/
theorem localPadicLatticeStabilizerIntegralGL_mulVec_mem_localDualPadicDenominator_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) (d : Fin n → ℤ_[p]) :
    (L.localPadicLatticeStabilizerIntegralGL p g).1.mulVec d ∈
        localDualPadicDenominator L p k ↔
      d ∈ localDualPadicDenominator L p k := by
  exact
    localDualPadicDenominator_mulVec_iff_of_local_isometry_matrix
      (L₀ := L) (L₁ := L) p k
      (L.localPadicLatticeStabilizerIntegralGL p g).isUnit
      (L.localPadicLatticeStabilizerIntegralGL_preserves_form p g) d

/-- Away from two, the same stabilizer matrix preserves the selected
associated-bilinear p-adic denominator. -/
theorem
    localPadicLatticeStabilizerIntegralGL_mulVec_mem_associatedBilinearDualPadicDenominator_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g : L.localPadicLatticeStabilizerSubgroup p) (d : Fin n → ℤ_[p]) :
    (L.localPadicLatticeStabilizerIntegralGL p g).1.mulVec d ∈
        associatedBilinearDualPadicDenominator L p k ↔
      d ∈ associatedBilinearDualPadicDenominator L p k := by
  rw [L.associatedBilinearDualPadicDenominator_eq_localDualPadicDenominator_of_ne_two
    p k hp2]
  exact
    L.localPadicLatticeStabilizerIntegralGL_mulVec_mem_localDualPadicDenominator_iff
      p k g d

/-- A p-adic integer differs from the standard natural representative of its
reduction modulo `p^k` by a multiple of `p^k`. -/
theorem padicInt_sub_standardRepresentative_toZModPow_mem_span_primePow
    (p k : ℕ) [Fact (Nat.Prime p)] (a : ℤ_[p]) :
    a - (((PadicInt.toZModPow k a).val : ℕ) : ℤ_[p]) ∈
      (Ideal.span {((p : ℤ_[p]) ^ k)} : Ideal ℤ_[p]) := by
  rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker]
  rw [map_sub]
  exact sub_eq_zero.mpr (by
    rw [map_natCast]
    exact_mod_cast (ZMod.natCast_zmod_val (PadicInt.toZModPow k a)).symm)

/-- The difference of two p-adic integers differs from the difference of the
standard representatives of their reductions by a multiple of `p^k`. -/
theorem padicInt_sub_sub_standardRepresentativeDifference_mem_span_primePow
    (p k : ℕ) [Fact (Nat.Prime p)] (a b : ℤ_[p]) :
    (a - b) -
          ((((PadicInt.toZModPow k a).val : ℕ) : ℤ) -
            (((PadicInt.toZModPow k b).val : ℕ) : ℤ) : ℤ_[p]) ∈
      (Ideal.span {((p : ℤ_[p]) ^ k)} : Ideal ℤ_[p]) := by
  have ha := padicInt_sub_standardRepresentative_toZModPow_mem_span_primePow
    p k a
  have hb := padicInt_sub_standardRepresentative_toZModPow_mem_span_primePow
    p k b
  have hsub :=
    (Ideal.span {((p : ℤ_[p]) ^ k)} : Ideal ℤ_[p]).sub_mem ha hb
  convert hsub using 1
  push_cast
  ring

/-- A standard-representative column congruence in the integral denominator
integral model lifts to membership of the actual p-adic column difference in the
associated-bilinear denominator. -/
theorem
    padicVector_sub_mem_associatedBilinearDualPadicDenominator_of_standardRepresentativeDifference_mem
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (a b : Fin n → ℤ_[p])
    (h :
      (fun i ↦
          (((PadicInt.toZModPow k (a i)).val : ℕ) : ℤ) -
            (((PadicInt.toZModPow k (b i)).val : ℕ) : ℤ)) ∈
        associatedBilinearDualPadicDenominatorIntegralPreimage L p k) :
    (fun i ↦ a i - b i) ∈
      associatedBilinearDualPadicDenominator L p k := by
  let z : Fin n → ℤ := fun i ↦
    (((PadicInt.toZModPow k (a i)).val : ℕ) : ℤ) -
      (((PadicInt.toZModPow k (b i)).val : ℕ) : ℤ)
  have hz : integralVectorToPadic (n := n) p z ∈
      associatedBilinearDualPadicDenominator L p k := by
    exact h
  have herr :
      (fun i ↦ (a i - b i) - integralVectorToPadic (n := n) p z i) ∈
        associatedBilinearDualPadicDenominator L p k := by
    apply
      L.mem_associatedBilinearDualPadicDenominator_of_forall_coord_primePow_dvd
    intro i
    have hi := Ideal.mem_span_singleton.mp
      (padicInt_sub_sub_standardRepresentativeDifference_mem_span_primePow
        p k (a i) (b i))
    simpa [z, integralVectorToPadic] using hi
  have hadd :=
    (associatedBilinearDualPadicDenominator L p k).add_mem herr hz
  convert hadd using 1
  funext i
  simp only [Pi.add_apply]
  ring

/-- Membership of an actual p-adic column difference in the selected
associated-bilinear denominator is equivalent to membership of its standard
finite-representative difference in the integral integral model. -/
theorem
    padicVector_sub_mem_associatedBilinearDualPadicDenominator_iff_standardRepresentativeDifference_mem
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (a b : Fin n → ℤ_[p]) :
    (fun i ↦ a i - b i) ∈
        associatedBilinearDualPadicDenominator L p k ↔
      (fun i ↦
          (((PadicInt.toZModPow k (a i)).val : ℕ) : ℤ) -
            (((PadicInt.toZModPow k (b i)).val : ℕ) : ℤ)) ∈
        associatedBilinearDualPadicDenominatorIntegralPreimage L p k := by
  let z : Fin n → ℤ := fun i ↦
    (((PadicInt.toZModPow k (a i)).val : ℕ) : ℤ) -
      (((PadicInt.toZModPow k (b i)).val : ℕ) : ℤ)
  constructor
  · intro hab
    have herr :
        (fun i ↦ (a i - b i) - integralVectorToPadic (n := n) p z i) ∈
          associatedBilinearDualPadicDenominator L p k := by
      apply
        L.mem_associatedBilinearDualPadicDenominator_of_forall_coord_primePow_dvd
      intro i
      have hi := Ideal.mem_span_singleton.mp
        (padicInt_sub_sub_standardRepresentativeDifference_mem_span_primePow
          p k (a i) (b i))
      simpa [z, integralVectorToPadic] using hi
    have hz :=
      (associatedBilinearDualPadicDenominator L p k).sub_mem hab herr
    change integralVectorToPadic (n := n) p z ∈
      associatedBilinearDualPadicDenominator L p k
    convert hz using 1
    funext i
    simp only [Pi.sub_apply]
    ring
  · exact
      L.padicVector_sub_mem_associatedBilinearDualPadicDenominator_of_standardRepresentativeDifference_mem
        p k a b

/-- In one liftable quotient fiber, the actual p-adic columns of the retained
coherent-branch and Hensel stabilizers differ by vectors in the selected
associated-bilinear denominator. -/
theorem
    infinitelyLiftableRawGramFiber_padicStabilizerColumnDifference_mem_denominator
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (Y :
      L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
        p)
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramFiber
        p hp2 Y) :
    ∀ j : Fin n,
      (fun i ↦
          L.localPadicLatticeStabilizerIntegralGL p
                (L.localPadicSpecialOrthogonalDifferentialDensityInfinitelyLiftableRawGramStabilizer
                  p X.1) i j -
            L.localPadicLatticeStabilizerIntegralGL p
                (L.localPadicSpecialOrthogonalDifferentialDensityQuotientFamilyHenselStabilizer
                  p Y) i j) ∈
        associatedBilinearDualPadicDenominator L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) := by
  intro j
  apply
    L.padicVector_sub_mem_associatedBilinearDualPadicDenominator_of_standardRepresentativeDifference_mem
      p (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  simpa only [localPadicLatticeStabilizerReduction_apply] using
    L.infinitelyLiftableRawGramFiber_stabilizerReductionColumnDifference_mem_denominator
      p hp2 Y X j

end PositiveDefiniteIntegralLattice
