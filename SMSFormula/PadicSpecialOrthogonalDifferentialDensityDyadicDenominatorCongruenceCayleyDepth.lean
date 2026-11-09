import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceFiberTorsor
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicCayleyDepth

/-!
# Cayley depth of the shifted dyadic denominator subgroup

For `g : H₂`, the matrix difference `G - 1` has columns in the local-dual
denominator at depth `k - 1`.  The selected Hensel depth forces sufficiently
strong coordinate divisibility to divide this difference by two and retain an
integral residual denominator.  Exact division in the denominator tower,
however, places the half-difference at depth `k - 2`, not `k - 1`.

This module records that depth bound for the chart domain.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_cayley_depth : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Exact local lattice depth persists after increasing the exponent. -/
theorem IsHenselLatticeDepth.add
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsHenselLatticeDepth p k) :
    ∀ r : ℕ, L.IsHenselLatticeDepth p (k + r)
  | 0 => by simpa using h
  | r + 1 => by
      rw [Nat.add_succ]
      exact (h.add L p k r).succ L p (k + r)

/-- At depth `k+r`, the local-dual denominator is coordinatewise contained in
`p^(r+1)` once `k` is strictly beyond the form-determinant valuation. -/
theorem localDualPadicDenominator_add_coordinate_primePow_dvd_of_pairingDeterminantVal_lt
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hval : padicValInt p L.pairingDeterminant < k) :
    ∀ (r : ℕ) (d : Fin n → ℤ_[p]),
      d ∈ localDualPadicDenominator L p (k + r) →
      ∀ i : Fin n, (p : ℤ_[p]) ^ (r + 1) ∣ d i
  | 0, d, hd => by
      let y : Fin n → ℚ_[p] :=
        fun i ↦ (d i : ℚ_[p]) / (p : ℚ_[p]) ^ k
      have hy : L.IsLocalDualPadicVector p y :=
        isLocalDualPadicVector_div_primePow_of_mem_localDualPadicDenominator
          L p k d hd
      obtain ⟨u, hu⟩ :=
        L.exists_padicIntVector_prime_mul_eq_primePow_mul_of_isLocalDual
          p k hval y hy
      intro i
      refine ⟨u i, ?_⟩
      apply PadicInt.ext
      change (d i : ℚ_[p]) =
        (p : ℚ_[p]) ^ (0 + 1) * (u i : ℚ_[p])
      have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
      calc
        (d i : ℚ_[p]) =
            (p : ℚ_[p]) ^ k *
              ((d i : ℚ_[p]) / (p : ℚ_[p]) ^ k) := by field_simp
        _ = (((p : ℤ_[p]) * u i : ℤ_[p]) : ℚ_[p]) := hu i
        _ = (p : ℚ_[p]) ^ (0 + 1) * (u i : ℚ_[p]) := by
          push_cast
          ring
  | r + 1, d, hd => by
      intro i
      have hdepth :=
        (L.isHenselLatticeDepth_of_pairingDeterminant_val_lt p k hval).add L p k r
      obtain ⟨e, he, hpe⟩ :=
        exists_prime_smul_eq_of_mem_localDualPadicDenominator_succ
          L p (k + r) hdepth d (by simpa [Nat.add_assoc] using hd)
      obtain ⟨a, ha⟩ :=
        L.localDualPadicDenominator_add_coordinate_primePow_dvd_of_pairingDeterminantVal_lt
          p k hval r e he i
      refine ⟨a, ?_⟩
      have hi := congr_fun hpe i
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      rw [← hi, ha]
      ring

/-- The selected dyadic density depth is at least three beyond the
form-determinant valuation. -/
theorem padicValInt_pairingDeterminant_add_three_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth_dyadic
    (L : PositiveDefiniteIntegralLattice n) :
    padicValInt 2 L.pairingDeterminant + 3 ≤
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 := by
  calc
    padicValInt 2 L.pairingDeterminant + 3 ≤ padicValInt 2 L.polarDeterminant + 3 :=
      Nat.add_le_add_right (L.padicValInt_pairingDeterminant_le_polarDeterminant 2) 3
    _ = localDensityHenselExponent L 2 := by
      rfl
    _ ≤ L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 :=
      L.localDensityHenselExponent_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
        2

/-- The certified entrywise divisibility exponent of `G-1` for `g : H₂`. -/
def localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceCayleyDivisibilityExponent
    (L : PositiveDefiniteIntegralLattice n) : ℕ :=
  L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 -
    padicValInt 2 L.pairingDeterminant - 1

/-- The shifted subgroup still forces at least two powers of two in every
matrix-difference entry. -/
theorem two_le_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceCayleyDivisibilityExponent
    (L : PositiveDefiniteIntegralLattice n) :
    2 ≤
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceCayleyDivisibilityExponent := by
  unfold
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceCayleyDivisibilityExponent
  have hdepth :=
    L.padicValInt_pairingDeterminant_add_three_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth_dyadic
  omega

/-- Every entry of `G-1` for `g : H₂` is divisible by the full certified
power `2^(k-v₂(pairingDeterminant)-1)`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceIntegralGL_sub_one_primePow_dvd
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    ∀ i j : Fin n,
      (2 : ℤ_[2]) ^
          L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceCayleyDivisibilityExponent ∣
        L.localPadicLatticeStabilizerIntegralGL 2 g.1 i j -
          (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j := by
  let k := L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  let v := padicValInt 2 L.pairingDeterminant
  have hdepth : v + 3 ≤ k := by
    exact
      L.padicValInt_pairingDeterminant_add_three_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth_dyadic
  have hlevel : (v + 1) + (k - v - 2) = k - 1 := by omega
  intro i j
  have hcol :
      (fun a ↦
        L.localPadicLatticeStabilizerIntegralGL 2 g.1 a j -
          (1 : Matrix (Fin n) (Fin n) ℤ_[2]) a j) ∈
        localDualPadicDenominator L 2 (k - 1) := by
    exact g.2 j
  rw [← hlevel] at hcol
  have hdiv :=
    L.localDualPadicDenominator_add_coordinate_primePow_dvd_of_pairingDeterminantVal_lt
      2 (v + 1) (by omega) (k - v - 2) _ hcol i
  change (2 : ℤ_[2]) ^ (k - v - 1) ∣
    L.localPadicLatticeStabilizerIntegralGL 2 g.1 i j -
      (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j
  simpa only [show k - v - 2 + 1 = k - v - 1 by omega] using hdiv

/-- The exact dyadic half-difference factorization for `g : H₂`.  The common
factor two can be cancelled integrally and the residual denominator is a
matrix unit, but the half-difference columns lie at depth `k-2`. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    ∃ E : Matrix (Fin n) (Fin n) ℤ_[2],
      (2 : ℤ_[2]) • E =
          (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1 - 1 ∧
      (∀ j : Fin n,
        (fun i ↦ E i j) ∈
          localDualPadicDenominator L 2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 2)) ∧
      IsUnit (1 + E) := by
  let k := L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  let v := padicValInt 2 L.pairingDeterminant
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let D : Matrix (Fin n) (Fin n) ℤ_[2] := G - 1
  have hdepth : v + 3 ≤ k := by
    exact
      L.padicValInt_pairingDeterminant_add_three_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth_dyadic
  have hsucc : (k - 2) + 1 = k - 1 := by omega
  have hcols : ∀ j : Fin n, (fun i ↦ D i j) ∈
      localDualPadicDenominator L 2 (k - 1) := by
    intro j
    simpa only [D, G, Matrix.sub_apply] using g.2 j
  choose e he htwo using fun j ↦
    exists_prime_smul_eq_of_mem_localDualPadicDenominator_succ
      L 2 (k - 2)
        (L.isHenselLatticeDepth_of_pairingDeterminant_val_lt 2 (k - 2) (by omega))
        (fun i ↦ D i j) (by simpa [hsucc] using hcols j)
  let E : Matrix (Fin n) (Fin n) ℤ_[2] := fun i j ↦ e j i
  have htwoE : (2 : ℤ_[2]) • E = D := by
    ext i j
    have hij := congr_fun (htwo j) i
    simpa only [E, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] using hij
  have hEcols : ∀ j : Fin n, (fun i ↦ E i j) ∈
      localDualPadicDenominator L 2 (k - 2) := by
    intro j
    exact he j
  have hlevel : (v + 1) + (k - v - 3) = k - 2 := by omega
  have hEdiv : ∀ i j, (2 : ℤ_[2]) ∣ E i j := by
    intro i j
    have hcol := hEcols j
    rw [← hlevel] at hcol
    have hdiv :=
      L.localDualPadicDenominator_add_coordinate_primePow_dvd_of_pairingDeterminantVal_lt
        2 (v + 1) (by omega) (k - v - 3) _ hcol i
    obtain ⟨a, ha⟩ := hdiv
    refine ⟨(2 : ℤ_[2]) ^ (k - v - 3) * a, ?_⟩
    rw [ha]
    ring
  have hEmod : ∀ i j, PadicInt.toZMod (E i j) = 0 := by
    intro i j
    have hmax : E i j ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton.mpr (hEdiv i j)
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hmax
    exact hmax
  have hAmod : ∀ i j, PadicInt.toZMod ((1 + E) i j) =
      (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j := by
    intro i j
    rw [Matrix.add_apply, map_add, hEmod]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine ⟨E, ?_, ?_, padicIntMatrix_isUnit_of_toZMod_eq_one (1 + E) hAmod⟩
  · simpa only [D, G] using htwoE
  · simpa only [k] using hEcols

end PositiveDefiniteIntegralLattice
