import SMSFormula.RationalLatticeCosetClassCount
import SMSFormula.RationalLatticeCosetSingularSeries
import SMSFormula.RationalAdeleStandardFactorTubeLimit

/-!
# Tube limits of the adjugate residue classes are coset singular series (dual test)

For `u ∈ ℤⁿ` let `U_u = {x ∈ Ẑⁿ : x ≡ adj(S) u (mod d)}`, `d = |det S|`.

* `finiteTubeMass_adjugateClass_eq`: at the width `d · (d K)` and the target `q(adj(S)u) + d² λ`
  (`cosetStandardTarget`), the tube mass of `1_{U_u}` is `d²/dⁿ · R^{cos}_K(u, λ)` (coset residue count),
  by the restricted congruence measure and `card_adjugateClass_congruence`.
* `tendsto_finiteTubeMass_adjugateClass` (rank four): along `j!` these masses converge to
  `d²/d⁴ · ∏'_p δ^{cos}_p(u, λ)`: the counts are the divisor sums of the coset Gauss–Ramanujan coefficients,
  whose sum is the coset singular series (`hasSum_cosetGRCoeff`).
* `eventually_finiteTubeMass_adjugateClass_eq_zero`: at a target not `≡ q(adj(S)u) (mod d²)` they vanish.
* `finiteTubeMass_adjugateClass_re_le`: the class masses are real, nonnegative and bounded by the standard
  tube masses.
Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology Finset RationalQuadraticSpaceMatrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

theorem finiteTubeMass_residueRestrictedIndicator_eq (L : PositiveDefiniteIntegralLattice n) {N₀ w : ℕ} [NeZero N₀]
    (hw : w ≠ 0) (hdvd : N₀ ∣ w) (R : Set (Fin n → ZMod N₀)) (M : ℤ) :
    L.finiteTubeMass (residueRestrictedIndicator n N₀ R) w M =
      (w : ℂ) * (((w : ℝ) ^ n : ℂ))⁻¹ *
        (Nat.card {z : Fin n → ZMod w // L.zmodQuadForm w z = ((M : ℤ) : ZMod w) ∧
          (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ R} : ℂ) := by
  unfold finiteTubeMass
  rw [L.measure_restrictedCongruenceSet_eq_residueCount hw hdvd R M, mul_assoc]

/-- The class tube identity: `T_{d(dK)}(1_{U_u})(q(adj(S)u) + d²λ) = d²/dⁿ · R^{cos}_K(u, λ)`. -/
theorem finiteTubeMass_adjugateClass_eq (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ) (lam : ℤ)
    {K : ℕ} (hK : K ≠ 0) :
    L.finiteTubeMass (residueRestrictedIndicator (n + 1) L.polarGramMatrix.det.natAbs {L.adjugateResidue u})
        (L.polarGramMatrix.det.natAbs * (L.polarGramMatrix.det.natAbs * K)) (L.cosetStandardTarget u lam) =
      (L.polarGramMatrix.det.natAbs : ℂ) ^ 2 / (L.polarGramMatrix.det.natAbs : ℂ) ^ (n + 1) *
        (L.cosetResidueCount u lam K : ℂ) := by
  have hd0 := L.natAbs_det_ne_zero
  have hw : L.polarGramMatrix.det.natAbs * (L.polarGramMatrix.det.natAbs * K) ≠ 0 :=
    mul_ne_zero hd0 (mul_ne_zero hd0 hK)
  rw [L.finiteTubeMass_residueRestrictedIndicator_eq hw (dvd_mul_right _ _)]
  have hcard := L.card_adjugateClass_congruence u lam hK
  change (_ : ℂ) * _ * ((Nat.card {z // _ ∧ L.reduceToDet _ z = L.adjugateResidue u} : ℕ) : ℂ) = _
  rw [hcard, cosetResidueCount]
  have hdC : (L.polarGramMatrix.det.natAbs : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hKC : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  push_cast
  set D : ℂ := (L.polarGramMatrix.det.natAbs : ℂ)
  set c : ℂ := ((Nat.card {y : Fin (n + 1) → ZMod K // L.zmodCosetPoly u K y = ((lam : ℤ) : ZMod K)} : ℕ) : ℂ)
  rw [mul_pow, mul_pow, pow_succ D, pow_succ (K : ℂ)]
  field_simp

/-- The widths `j!` are eventually of the form `d · (d K_j)` with `K_j = j!/d²`. -/
theorem eventually_factorial_eq_det_mul (L : PositiveDefiniteIntegralLattice n) :
    ∀ᶠ j in atTop, L.polarGramMatrix.det.natAbs * (L.polarGramMatrix.det.natAbs *
      (Nat.factorial j / (L.polarGramMatrix.det.natAbs * L.polarGramMatrix.det.natAbs))) = Nat.factorial j := by
  have hd0 := L.natAbs_det_ne_zero
  filter_upwards [eventually_ge_atTop (L.polarGramMatrix.det.natAbs * L.polarGramMatrix.det.natAbs)] with j hj
  rw [← mul_assoc, Nat.mul_div_cancel' (Nat.dvd_factorial (Nat.pos_of_ne_zero (mul_ne_zero hd0 hd0)) hj)]

/-- The quotients `j!/d²` are divisibility-cofinal. -/
theorem tendsto_insert_zero_divisors_factorial_div (L : PositiveDefiniteIntegralLattice n) :
    Tendsto (fun j ↦ insert 0 (Nat.factorial j / (L.polarGramMatrix.det.natAbs *
      L.polarGramMatrix.det.natAbs)).divisors) atTop atTop := by
  have hd0 := L.natAbs_det_ne_zero
  set e := L.polarGramMatrix.det.natAbs * L.polarGramMatrix.det.natAbs with he
  have he0 : e ≠ 0 := mul_ne_zero hd0 hd0
  refine tendsto_atTop.2 fun s ↦ ?_
  have hq : ∀ q ∈ s, ∀ᶠ j in atTop, q ∈ insert 0 (Nat.factorial j / e).divisors := by
    intro q _
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact Eventually.of_forall fun j ↦ mem_insert_self _ _
    · filter_upwards [eventually_ge_atTop (q * e)] with j hj
      have hdvd : q * e ∣ Nat.factorial j :=
        Nat.dvd_factorial (Nat.pos_of_ne_zero (mul_ne_zero hq.ne' he0)) hj
      refine mem_insert_of_mem (Nat.mem_divisors.2 ⟨?_, ?_⟩)
      · obtain ⟨c, hc⟩ := hdvd
        rw [hc, show q * e * c = e * (q * c) by ring, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)]
        exact dvd_mul_right q c
      · intro h0
        have hle : e ≤ Nat.factorial j := Nat.le_of_dvd (Nat.factorial_pos j) (dvd_trans
          (dvd_mul_left e q) hdvd)
        exact absurd h0 (Nat.div_ne_zero_iff_of_dvd (dvd_trans (dvd_mul_left e q) hdvd) |>.2
          ⟨Nat.factorial_ne_zero j, he0⟩)
  filter_upwards [(eventually_all_finset s).2 hq] with j hj
  exact fun q hqs ↦ hj q hqs

set_option maxHeartbeats 1600000 in
/-- The class tube limit is the coset singular series (rank four):
`T_{j!}(1_{U_u})(q(adj(S)u) + d²λ) → d²/d⁴ · ∏'_p δ^{cos}_p(u, λ)`. -/
theorem tendsto_finiteTubeMass_adjugateClass (L : PositiveDefiniteIntegralLattice 4) (u : Fin 4 → ℤ) (lam : ℤ)
    (hM : L.cosetStandardTarget u lam ≠ 0) :
    Tendsto (fun j ↦ L.finiteTubeMass
        (residueRestrictedIndicator 4 L.polarGramMatrix.det.natAbs {L.adjugateResidue u}) (Nat.factorial j)
        (L.cosetStandardTarget u lam)) atTop
      (𝓝 ((L.polarGramMatrix.det.natAbs : ℂ) ^ 2 / (L.polarGramMatrix.det.natAbs : ℂ) ^ 4 *
        ∏' p : Nat.Primes, ((L.cosetLocalDensity u lam p : ℝ) : ℂ))) := by
  have hd0 := L.natAbs_det_ne_zero
  set e := L.polarGramMatrix.det.natAbs * L.polarGramMatrix.det.natAbs with he
  have hS := L.hasSum_cosetGRCoeff u lam hM
  have hlim := (hS.comp (L.tendsto_insert_zero_divisors_factorial_div)).const_mul
    ((L.polarGramMatrix.det.natAbs : ℂ) ^ 2 / (L.polarGramMatrix.det.natAbs : ℂ) ^ 4)
  refine hlim.congr' ?_
  filter_upwards [L.eventually_factorial_eq_det_mul, eventually_ge_atTop e] with j hj hje
  have hK : Nat.factorial j / e ≠ 0 :=
    (Nat.div_ne_zero_iff_of_dvd (Nat.dvd_factorial (Nat.pos_of_ne_zero (mul_ne_zero hd0 hd0)) hje)).2
      ⟨Nat.factorial_ne_zero j, mul_ne_zero hd0 hd0⟩
  simp only [Function.comp_apply]
  rw [sum_insert fun h ↦ hK (Nat.eq_zero_of_zero_dvd (Nat.mem_divisors.1 h).1),
    L.cosetGRCoeff_zero u lam, zero_add, L.sum_divisors_cosetGRCoeff u lam hK]
  have h := L.finiteTubeMass_adjugateClass_eq (n := 3) u lam hK
  rw [hj] at h
  exact h.symm

/-- At a target not `≡ q(adj(S) u) (mod d²)` the class tube masses vanish at every width divisible by `d²`. -/
theorem finiteTubeMass_adjugateClass_eq_zero (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) {M : ℤ}
    (hM : ∀ lam : ℤ, M ≠ L.cosetStandardTarget u lam) {m : ℕ} (hm : m ≠ 0) :
    L.finiteTubeMass (residueRestrictedIndicator n L.polarGramMatrix.det.natAbs {L.adjugateResidue u})
        (L.polarGramMatrix.det.natAbs * (L.polarGramMatrix.det.natAbs * m)) M = 0 := by
  have hd0 := L.natAbs_det_ne_zero
  rw [L.finiteTubeMass_residueRestrictedIndicator_eq (mul_ne_zero hd0 (mul_ne_zero hd0 hm))
    (dvd_mul_right _ _)]
  have hcard := L.card_adjugateClass_congruence_eq_zero u hM hm
  change (_ : ℂ) * _ * ((Nat.card {z // _ ∧ L.reduceToDet _ z = L.adjugateResidue u} : ℕ) : ℂ) = _
  rw [hcard, Nat.cast_zero, mul_zero]

theorem eventually_finiteTubeMass_adjugateClass_eq_zero (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ)
    {M : ℤ} (hM : ∀ lam : ℤ, M ≠ L.cosetStandardTarget u lam) :
    ∀ᶠ j in atTop, L.finiteTubeMass
      (residueRestrictedIndicator n L.polarGramMatrix.det.natAbs {L.adjugateResidue u}) (Nat.factorial j) M = 0 := by
  have hd0 := L.natAbs_det_ne_zero
  filter_upwards [L.eventually_factorial_eq_det_mul, eventually_ge_atTop
    (L.polarGramMatrix.det.natAbs * L.polarGramMatrix.det.natAbs)] with j hj hje
  have hK : Nat.factorial j / (L.polarGramMatrix.det.natAbs * L.polarGramMatrix.det.natAbs) ≠ 0 :=
    (Nat.div_ne_zero_iff_of_dvd (Nat.dvd_factorial (Nat.pos_of_ne_zero (mul_ne_zero hd0 hd0)) hje)).2
      ⟨Nat.factorial_ne_zero j, mul_ne_zero hd0 hd0⟩
  have h := L.finiteTubeMass_adjugateClass_eq_zero u hM hK
  rwa [hj] at h

/-- Residue-restricted tube masses are real, nonnegative and at most the standard tube masses. -/
theorem finiteTubeMass_residueRestricted_eq_ofReal_le (L : PositiveDefiniteIntegralLattice n) {N₀ w : ℕ} [NeZero N₀]
    (hw : w ≠ 0) (hdvd : N₀ ∣ w) (R : Set (Fin n → ZMod N₀)) (M : ℤ) :
    ∃ r s : ℝ, 0 ≤ r ∧ r ≤ s ∧ L.finiteTubeMass (residueRestrictedIndicator n N₀ R) w M = r ∧
      L.finiteTubeMass rationalFiniteAdeleVectorIntegralIndicator w M = s := by
  classical
  haveI : NeZero w := ⟨hw⟩
  have hR := L.finiteTubeMass_residueRestrictedIndicator_eq hw hdvd R M
  have hU := L.finiteTubeMass_residueRestrictedIndicator_eq hw hdvd Set.univ M
  rw [residueRestrictedIndicator_univ] at hU
  set c₁ := Nat.card {z : Fin n → ZMod w // L.zmodQuadForm w z = ((M : ℤ) : ZMod w) ∧
    (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ R}
  set c₂ := Nat.card {z : Fin n → ZMod w // L.zmodQuadForm w z = ((M : ℤ) : ZMod w) ∧
    (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ (Set.univ : Set (Fin n → ZMod N₀))}
  have hle : c₁ ≤ c₂ := by
    refine Nat.card_mono (Set.toFinite _) fun z hz ↦ ⟨hz.1, Set.mem_univ _⟩
  refine ⟨(w : ℝ) * ((w : ℝ) ^ n)⁻¹ * c₁, (w : ℝ) * ((w : ℝ) ^ n)⁻¹ * c₂, by positivity,
    mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by positivity), ?_, ?_⟩
  · rw [hR]; push_cast; ring
  · rw [hU]; push_cast; ring

end PositiveDefiniteIntegralLattice
