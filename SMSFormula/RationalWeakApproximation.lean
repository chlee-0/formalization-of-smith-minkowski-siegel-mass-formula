import SMSFormula.RationalTernaryHasseMinkowski
import Mathlib.Algebra.Order.Round
import Mathlib.NumberTheory.LSeries.PrimesInAP

noncomputable section

namespace Rat

private lemma exists_int_div_int_real_near_of_modEq
    (M A B : ℕ) (hM : 0 < M) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N L : ℤ, L ≠ 0 ∧
      Int.ModEq M N A ∧ Int.ModEq M L B ∧
      |((N : ℚ) / L : ℝ) - x| < ε := by
  obtain ⟨k : ℕ, hk : (M : ℝ) / (2 * ε) < k⟩ :=
    exists_nat_gt ((M : ℝ) / (2 * ε))
  let L : ℤ := B + k * M
  let y : ℝ := (x * L - A) / M
  let z : ℤ := round y
  let N : ℤ := A + z * M
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hkpos : 0 < k := by
    have hfracpos : (0 : ℝ) < (M : ℝ) / (2 * ε) := by positivity
    exact_mod_cast hfracpos.trans hk
  have hLpos : (0 : ℝ) < L := by
    dsimp [L]
    positivity
  have hL0 : L ≠ 0 := by exact_mod_cast hLpos.ne'
  refine ⟨N, L, hL0, ?_, ?_, ?_⟩
  · rw [Int.modEq_iff_dvd]
    dsimp [N]
    refine ⟨-z, by ring⟩
  · rw [Int.modEq_iff_dvd]
    dsimp [L]
    refine ⟨-k, by ring⟩
  · have hround : |(z : ℝ) - y| ≤ 1 / 2 := by
      simpa [abs_sub_comm] using abs_sub_round y
    have hLlarge : (M : ℝ) / (2 * ε) < L := by
      have hk' : (M : ℝ) / (2 * ε) < (k : ℝ) := by exact_mod_cast hk
      have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
      calc
        (M : ℝ) / (2 * ε) < (k : ℝ) := hk'
        _ ≤ (L : ℝ) := by
          norm_num [L]
          nlinarith [mul_le_mul_of_nonneg_left hMone (Nat.cast_nonneg k)]
    have hratio : (M : ℝ) / (2 * L) < ε := by
      have htwoeps : 0 < 2 * ε := by positivity
      have htwoL : (0 : ℝ) < 2 * L := by positivity
      rw [div_lt_iff₀ htwoL]
      rw [div_lt_iff₀ htwoeps] at hLlarge
      nlinarith
    have heq : (N : ℝ) / L - x =
        (M : ℝ) / L * ((z : ℝ) - y) := by
      dsimp only [N, y]
      push_cast
      field_simp [hL0, hM.ne']
      ring
    change |(N : ℝ) / L - x| < ε
    rw [heq, abs_mul]
    calc
      |(M : ℝ) / L| * |(z : ℝ) - y| ≤
          ((M : ℝ) / L) * (1 / 2) := by
        rw [abs_of_pos (div_pos hMreal hLpos)]
        exact mul_le_mul_of_nonneg_left hround
          (div_nonneg hMreal.le hLpos.le)
      _ = (M : ℝ) / (2 * L) := by ring
      _ < ε := hratio

private lemma exists_int_div_int_real_near_of_primePower_modEq
    (S : Finset {p : ℕ // p.Prime})
    (e : {p : ℕ // p.Prime} → ℕ)
    (a b : {p : ℕ // p.Prime} → ℤ)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N L : ℤ, L ≠ 0 ∧ |(N : ℝ) / L - x| < ε ∧
      ∀ p ∈ S,
        Int.ModEq (p.1 ^ e p) N (a p) ∧
          Int.ModEq (p.1 ^ e p) L (b p) := by
  classical
  let modulus : {p : ℕ // p.Prime} → ℕ := fun p => p.1 ^ e p
  have hmod_ne (p : {p : ℕ // p.Prime}) : modulus p ≠ 0 := by
    exact pow_ne_zero _ p.2.ne_zero
  have hpair : Set.Pairwise (S : Set {p : ℕ // p.Prime})
      (Function.onFun Nat.Coprime modulus) := by
    intro p hp q hq hpq
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes p.2 q.2).2 fun hval =>
      hpq (Subtype.ext hval)
  let residue (v : {p : ℕ // p.Prime} → ℤ)
      (p : {p : ℕ // p.Prime}) : ℕ :=
    (v p % (modulus p : ℤ)).toNat
  have hresidue (v : {p : ℕ // p.Prime} → ℤ)
      (p : {p : ℕ // p.Prime}) :
      Int.ModEq (modulus p) (residue v p) (v p) := by
    have hmodpos : (0 : ℤ) < modulus p := by
      exact_mod_cast Nat.pos_of_ne_zero (hmod_ne p)
    have hnonneg : 0 ≤ v p % (modulus p : ℤ) :=
      Int.emod_nonneg _ hmodpos.ne'
    have hcast : ((residue v p : ℕ) : ℤ) =
        v p % (modulus p : ℤ) := by
      simpa [residue] using Int.toNat_of_nonneg hnonneg
    rw [hcast]
    exact Int.mod_modEq _ _
  let R : ℕ :=
    Nat.chineseRemainderOfFinset (residue a) modulus S
      (fun p _ => hmod_ne p) hpair
  let T : ℕ :=
    Nat.chineseRemainderOfFinset (residue b) modulus S
      (fun p _ => hmod_ne p) hpair
  let M : ℕ := ∏ p ∈ S, modulus p
  have hM : 0 < M := by
    apply Finset.prod_pos
    intro p hp
    exact Nat.pos_of_ne_zero (hmod_ne p)
  obtain ⟨N, L, hL, hNM, hLM, hreal⟩ :=
    exists_int_div_int_real_near_of_modEq M R T hM x hε
  refine ⟨N, L, hL, hreal, ?_⟩
  intro p hp
  have hmod_dvd : (modulus p : ℤ) ∣ M := by
    exact_mod_cast Finset.dvd_prod_of_mem modulus hp
  have hRnat : R ≡ residue a p [MOD modulus p] :=
    (Nat.chineseRemainderOfFinset (residue a) modulus S
      (fun q _ => hmod_ne q) hpair).prop p hp
  have hRint : Int.ModEq (modulus p) R (residue a p) := by
    exact_mod_cast hRnat
  have hTnat : T ≡ residue b p [MOD modulus p] :=
    (Nat.chineseRemainderOfFinset (residue b) modulus S
      (fun q _ => hmod_ne q) hpair).prop p hp
  have hTint : Int.ModEq (modulus p) T (residue b p) := by
    exact_mod_cast hTnat
  exact ⟨(hNM.of_dvd hmod_dvd).trans (hRint.trans (hresidue a p)),
    (hLM.of_dvd hmod_dvd).trans (hTint.trans (hresidue b p))⟩

local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩

private lemma padic_norm_int_le_norm_p_pow_of_dvd
    (p : {p : ℕ // p.Prime}) (k : ℤ) (n : ℕ)
    (h : (p.1 ^ n : ℤ) ∣ k) :
    ‖(k : ℚ_[p.1])‖ ≤ ‖(p.1 : ℚ_[p.1])‖ ^ n := by
  calc
    ‖(k : ℚ_[p.1])‖ ≤ (p.1 : ℝ) ^ (-(n : ℤ)) :=
      (Padic.norm_int_le_pow_iff_dvd k n).2 h
    _ = ‖(p.1 ^ n : ℚ_[p.1])‖ := (Padic.norm_p_pow n).symm
    _ = ‖(p.1 : ℚ_[p.1])‖ ^ n := norm_pow _ _

/-- A rational number can simultaneously approximate one real number and
finitely many p-adic numbers. This is the finite-place weak approximation
statement needed below; it imposes no valuation conditions at other primes. -/
theorem exists_rat_near_real_and_finitely_many_padic
    (S : Finset {p : ℕ // p.Prime})
    (xReal : ℝ) (xPadic : ∀ p : {p : ℕ // p.Prime}, ℚ_[p.1])
    (εReal : ℝ) (εPadic : {p : ℕ // p.Prime} → ℝ)
    (hεReal : 0 < εReal) (hεPadic : ∀ p, 0 < εPadic p) :
    ∃ q : ℚ, |(q : ℝ) - xReal| < εReal ∧
      ∀ p ∈ S, ‖(q : ℚ_[p.1]) - xPadic p‖ < εPadic p := by
  classical
  let r : {p : ℕ // p.Prime} → ℚ := fun p =>
    Classical.choose (Padic.rat_dense p.1 (xPadic p) (hεPadic p))
  have hr (p : {p : ℕ // p.Prime}) :
      ‖xPadic p - (r p : ℚ_[p.1])‖ < εPadic p :=
    Classical.choose_spec (Padic.rat_dense p.1 (xPadic p) (hεPadic p))
  let bound (p : {p : ℕ // p.Prime}) : ℝ :=
    min ‖((r p).den : ℚ_[p.1])‖
      (εPadic p * ‖((r p).den : ℚ_[p.1])‖ ^ 2)
  have hbound (p : {p : ℕ // p.Prime}) : 0 < bound p := by
    have hden : ((r p).den : ℚ_[p.1]) ≠ 0 := by
      exact_mod_cast (r p).den_nz
    exact lt_min (norm_pos_iff.mpr hden)
      (mul_pos (hεPadic p) (sq_pos_of_pos (norm_pos_iff.mpr hden)))
  let exponent (p : {p : ℕ // p.Prime}) : ℕ :=
    Classical.choose (exists_pow_lt_of_lt_one (y := ‖(p.1 : ℚ_[p.1])‖)
      (hbound p) Padic.norm_p_lt_one)
  have hexponent (p : {p : ℕ // p.Prime}) :
      ‖(p.1 : ℚ_[p.1])‖ ^ exponent p < bound p :=
    Classical.choose_spec
      (exists_pow_lt_of_lt_one (y := ‖(p.1 : ℚ_[p.1])‖)
        (hbound p) Padic.norm_p_lt_one)
  obtain ⟨N, L, hL, hReal, hcongr⟩ :=
    exists_int_div_int_real_near_of_primePower_modEq S exponent
      (fun p => (r p).num) (fun p => (r p).den)
      xReal hεReal
  let q : ℚ := (N : ℚ) / L
  refine ⟨q, ?_, ?_⟩
  · simpa [q] using hReal
  · intro p hp
    obtain ⟨hN, hLp⟩ := hcongr p hp
    have hpow_den : ‖(p.1 : ℚ_[p.1])‖ ^ exponent p <
        ‖((r p).den : ℚ_[p.1])‖ :=
      (hexponent p).trans_le (min_le_left _ _)
    have hpow_error : ‖(p.1 : ℚ_[p.1])‖ ^ exponent p <
        εPadic p * ‖((r p).den : ℚ_[p.1])‖ ^ 2 :=
      (hexponent p).trans_le (min_le_right _ _)
    have hL_dvd : (p.1 ^ exponent p : ℤ) ∣ (r p).den - L :=
      Int.modEq_iff_dvd.mp hLp
    have hL_near : ‖(L : ℚ_[p.1]) - (r p).den‖ <
        ‖((r p).den : ℚ_[p.1])‖ := by
      have hnear := (padic_norm_int_le_norm_p_pow_of_dvd p (L - (r p).den)
        (exponent p) (by simpa [sub_eq_neg_add, add_comm] using dvd_neg.mpr hL_dvd)).trans_lt
          hpow_den
      simpa only [Int.cast_sub, Int.cast_natCast] using hnear
    have hLnorm : ‖(L : ℚ_[p.1])‖ = ‖((r p).den : ℚ_[p.1])‖ :=
      Padic.norm_eq_of_norm_sub_lt_right hL_near
    have hcommon : Int.ModEq (p.1 ^ exponent p)
        (N * (r p).den) (L * (r p).num) := by
      calc
        N * (r p).den ≡ (r p).num * (r p).den [ZMOD (p.1 ^ exponent p)] :=
          hN.mul Int.ModEq.rfl
        _ = (r p).den * (r p).num := mul_comm _ _
        _ ≡ L * (r p).num [ZMOD (p.1 ^ exponent p)] :=
          (hLp.mul Int.ModEq.rfl).symm
    have hnum_dvd : (p.1 ^ exponent p : ℤ) ∣
        N * (r p).den - L * (r p).num := by
      have hd := dvd_neg.mpr (Int.modEq_iff_dvd.mp hcommon)
      simpa only [neg_sub] using hd
    have hq_r : ‖(q : ℚ_[p.1]) - (r p : ℚ_[p.1])‖ < εPadic p := by
      have hdiff : (q : ℚ_[p.1]) - (r p : ℚ_[p.1]) =
          ((N * (r p).den - L * (r p).num : ℤ) : ℚ_[p.1]) /
            ((L * (r p).den : ℤ) : ℚ_[p.1]) := by
        dsimp only [q]
        push_cast
        rw [Rat.cast_def]
        field_simp [hL, (r p).den_nz]
      rw [hdiff, norm_div]
      push_cast
      rw [norm_mul, hLnorm]
      have hnum_le := padic_norm_int_le_norm_p_pow_of_dvd p
        (N * (r p).den - L * (r p).num) (exponent p) hnum_dvd
      have hnum_le' :
          ‖(N : ℚ_[p.1]) * (r p).den - (L : ℚ_[p.1]) * (r p).num‖ ≤
            ‖(p.1 : ℚ_[p.1])‖ ^ exponent p := by
        simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hnum_le
      have hdenpos : 0 < ‖((r p).den : ℚ_[p.1])‖ ^ 2 := by
        have hden : ((r p).den : ℚ_[p.1]) ≠ 0 := by
          exact_mod_cast (r p).den_nz
        positivity
      rw [← pow_two, div_lt_iff₀ hdenpos]
      exact hnum_le'.trans_lt hpow_error
    have hr' : ‖(r p : ℚ_[p.1]) - xPadic p‖ < εPadic p := by
      simpa [norm_sub_rev] using hr p
    calc
      ‖(q : ℚ_[p.1]) - xPadic p‖ =
          ‖((q : ℚ_[p.1]) - r p + (r p - xPadic p))‖ := by ring_nf
      _ ≤ max ‖(q : ℚ_[p.1]) - r p‖ ‖r p - xPadic p‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      _ < εPadic p := max_lt hq_r hr'

/-- Every nonempty open real set and finite family of nonempty open p-adic
sets contain the images of one rational number. No assertion is made about
the valuations of that rational number outside the supplied finite set. -/
theorem exists_rat_mem_real_and_finitely_many_padic_opens
    (S : Finset {p : ℕ // p.Prime})
    (UReal : Set ℝ)
    (UPadic : ∀ p : {p : ℕ // p.Prime}, Set ℚ_[p.1])
    (hUReal : IsOpen UReal) (hneReal : UReal.Nonempty)
    (hUPadic : ∀ p ∈ S, IsOpen (UPadic p))
    (hnePadic : ∀ p ∈ S, (UPadic p).Nonempty) :
    ∃ q : ℚ, (q : ℝ) ∈ UReal ∧
      ∀ p ∈ S, (q : ℚ_[p.1]) ∈ UPadic p := by
  classical
  obtain ⟨xReal, hxReal⟩ := hneReal
  obtain ⟨εReal, hεReal, hballReal⟩ :=
    Metric.isOpen_iff.mp hUReal xReal hxReal
  let xPadic (p : {p : ℕ // p.Prime}) : ℚ_[p.1] :=
    if hp : p ∈ S then Classical.choose (hnePadic p hp) else 0
  have hxPadic (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      xPadic p ∈ UPadic p := by
    simpa only [xPadic, dif_pos hp] using Classical.choose_spec (hnePadic p hp)
  let padicBall (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :=
    Metric.isOpen_iff.mp (hUPadic p hp) (xPadic p) (hxPadic p hp)
  let εPadic (p : {p : ℕ // p.Prime}) : ℝ :=
    if hp : p ∈ S then Classical.choose (padicBall p hp) else 1
  have hεPadic (p : {p : ℕ // p.Prime}) : 0 < εPadic p := by
    by_cases hp : p ∈ S
    · simpa only [εPadic, dif_pos hp] using
        (Classical.choose_spec (padicBall p hp)).1
    · simp only [εPadic, dif_neg hp, zero_lt_one]
  have hballPadic (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      Metric.ball (xPadic p) (εPadic p) ⊆ UPadic p := by
    simpa only [εPadic, dif_pos hp] using
      (Classical.choose_spec (padicBall p hp)).2
  obtain ⟨q, hqReal, hqPadic⟩ :=
    exists_rat_near_real_and_finitely_many_padic S xReal xPadic
      εReal εPadic hεReal hεPadic
  refine ⟨q, hballReal ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq]
    exact hqReal
  · intro p hp
    apply hballPadic p hp
    rw [Metric.mem_ball, dist_eq_norm]
    exact hqPadic p hp

private def auxiliaryPrimeExponent (p : {p : ℕ // p.Prime}) : ℕ :=
  if p.1 = 2 then 3 else 1

private lemma auxiliaryPrimeExponent_pos (p : {p : ℕ // p.Prime}) :
    0 < auxiliaryPrimeExponent p := by
  unfold auxiliaryPrimeExponent
  split <;> norm_num

private def rationalPadicUnit
    (p : {p : ℕ // p.Prime}) (a : ℚ) (ha : a ≠ 0)
    (hval : padicValRat p.1 a = 0) : ℤ_[p.1] :=
  ⟨(a : ℚ_[p.1]), by
    rw [Padic.norm_eq_zpow_neg_valuation]
    · simp [Padic.valuation_ratCast, hval]
    · exact_mod_cast ha⟩

private lemma rationalPadicUnit_isUnit
    (p : {p : ℕ // p.Prime}) (a : ℚ) (ha : a ≠ 0)
    (hval : padicValRat p.1 a = 0) :
    IsUnit (rationalPadicUnit p a ha hval) := by
  rw [PadicInt.isUnit_iff]
  change ‖(a : ℚ_[p.1])‖ = 1
  rw [Padic.norm_eq_zpow_neg_valuation]
  · simp [Padic.valuation_ratCast, hval]
  · exact_mod_cast ha

private lemma padicValRat_prime_zpow_aux
    (p : {p : ℕ // p.Prime}) (k : ℤ) :
    padicValRat p.1 ((p.1 : ℚ) ^ k) = k := by
  cases k with
  | ofNat n =>
      change padicValRat p.1 ((p.1 : ℚ) ^ n) = (n : ℤ)
      rw [padicValRat.pow]
      · rw [padicValRat.of_nat, padicValNat.self p.2.one_lt]
        simp
      · exact_mod_cast p.2.ne_zero
  | negSucc n =>
      change padicValRat p.1 ((p.1 : ℚ) ^ (Int.negSucc n)) = -(n + 1 : ℕ)
      rw [zpow_negSucc, padicValRat.inv, padicValRat.pow]
      · rw [padicValRat.of_nat, padicValNat.self p.2.one_lt]
        simp
      · exact_mod_cast p.2.ne_zero

private lemma padicValRat_other_prime_zpow_aux
    (p r : {p : ℕ // p.Prime}) (hpr : p ≠ r) (k : ℤ) :
    padicValRat p.1 ((r.1 : ℚ) ^ k) = 0 := by
  have hnat : padicValNat p.1 r.1 = 0 :=
    padicValNat_primes (fun h => hpr (Subtype.ext h))
  cases k with
  | ofNat n =>
      change padicValRat p.1 ((r.1 : ℚ) ^ n) = 0
      rw [padicValRat.pow]
      · rw [padicValRat.of_nat, hnat]
        simp
      · exact_mod_cast r.2.ne_zero
  | negSucc n =>
      change padicValRat p.1 ((r.1 : ℚ) ^ (Int.negSucc n)) = 0
      rw [zpow_negSucc, padicValRat.inv, padicValRat.pow]
      · rw [padicValRat.of_nat, hnat]
        simp
      · exact_mod_cast r.2.ne_zero

private def auxiliaryPrimeValuationBase
    (S : Finset {p : ℕ // p.Prime})
    (a : {p : ℕ // p.Prime} → ℚ) (aReal : ℚ) : ℚ :=
  (if 0 < aReal then 1 else -1) *
    ∏ p ∈ S, (p.1 : ℚ) ^ padicValRat p.1 (a p)

private lemma auxiliaryPrimeValuationBase_ne_zero
    (S : Finset {p : ℕ // p.Prime})
    (a : {p : ℕ // p.Prime} → ℚ) (aReal : ℚ) :
    auxiliaryPrimeValuationBase S a aReal ≠ 0 := by
  apply mul_ne_zero
  · split <;> norm_num
  · apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact zpow_ne_zero _ (by exact_mod_cast p.2.ne_zero)

private lemma padicValRat_auxiliaryPrimeValuationBase
    (S : Finset {p : ℕ // p.Prime})
    (a : {p : ℕ // p.Prime} → ℚ) (aReal : ℚ)
    (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
    padicValRat p.1 (auxiliaryPrimeValuationBase S a aReal) =
      padicValRat p.1 (a p) := by
  let f : {p : ℕ // p.Prime} → ℚ := fun r =>
    (r.1 : ℚ) ^ padicValRat r.1 (a r)
  have hf (r : {p : ℕ // p.Prime}) : f r ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast r.2.ne_zero)
  have hprod_all : ∀ T : Finset {p : ℕ // p.Prime},
      padicValRat p.1 (∏ r ∈ T, f r) =
        ∑ r ∈ T, padicValRat p.1 (f r) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert r T hr ih =>
        rw [Finset.prod_insert hr, padicValRat.mul (hf r)
          (Finset.prod_ne_zero_iff.mpr fun q _ => hf q),
          Finset.sum_insert hr, ih]
  have hprod := hprod_all S
  have hsum : (∑ r ∈ S, padicValRat p.1 (f r)) =
      padicValRat p.1 (a p) := by
    rw [Finset.sum_eq_single p]
    · exact padicValRat_prime_zpow_aux p _
    · intro r hr hrp
      exact padicValRat_other_prime_zpow_aux p r (Ne.symm hrp) _
    · exact fun hnot => False.elim (hnot hp)
  rw [auxiliaryPrimeValuationBase,
    padicValRat.mul (by split <;> norm_num)
      (Finset.prod_ne_zero_iff.mpr fun r _ => hf r)]
  have hsign : padicValRat p.1 (if 0 < aReal then 1 else -1) = 0 := by
    split <;> simp
  rw [hsign, zero_add, show (∏ r ∈ S,
    (r.1 : ℚ) ^ padicValRat r.1 (a r)) = ∏ r ∈ S, f r by rfl,
    hprod, hsum]

private lemma padicValRat_auxiliaryPrimeValuationBase_of_not_mem
    (S : Finset {p : ℕ // p.Prime})
    (a : {p : ℕ // p.Prime} → ℚ) (aReal : ℚ)
    (p : {p : ℕ // p.Prime}) (hp : p ∉ S) :
    padicValRat p.1 (auxiliaryPrimeValuationBase S a aReal) = 0 := by
  let f : {p : ℕ // p.Prime} → ℚ := fun r =>
    (r.1 : ℚ) ^ padicValRat r.1 (a r)
  have hf (r : {p : ℕ // p.Prime}) : f r ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast r.2.ne_zero)
  have hprod_all : ∀ T : Finset {p : ℕ // p.Prime},
      padicValRat p.1 (∏ r ∈ T, f r) =
        ∑ r ∈ T, padicValRat p.1 (f r) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert r T hr ih =>
        rw [Finset.prod_insert hr, padicValRat.mul (hf r)
          (Finset.prod_ne_zero_iff.mpr fun q _ => hf q),
          Finset.sum_insert hr, ih]
  have hsum : (∑ r ∈ S, padicValRat p.1 (f r)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    exact padicValRat_other_prime_zpow_aux p r (fun h => hp (h ▸ hr)) _
  rw [auxiliaryPrimeValuationBase,
    padicValRat.mul (by split <;> norm_num)
      (Finset.prod_ne_zero_iff.mpr fun r _ => hf r)]
  have hsign : padicValRat p.1 (if 0 < aReal then 1 else -1) = 0 := by
    split <;> simp
  rw [hsign, zero_add, show (∏ r ∈ S,
    (r.1 : ℚ) ^ padicValRat r.1 (a r)) = ∏ r ∈ S, f r by rfl,
    hprod_all S, hsum]

/-- A fresh prime can simultaneously realize prescribed rational p-adic unit
square classes at finitely many places. Modulus eight is used at the dyadic
place and modulus `p` at every odd place. -/
theorem exists_fresh_prime_with_prescribed_local_unit_squareClasses
    (S : Finset {p : ℕ // p.Prime})
    (a : {p : ℕ // p.Prime} → ℚ)
    (ha : ∀ p ∈ S, a p ≠ 0)
    (hval : ∀ p ∈ S, padicValRat p.1 (a p) = 0) :
    ∃ ell : ℕ, ell.Prime ∧ (∀ p ∈ S, ell ≠ p.1) ∧
      ∀ p ∈ S, IsSquare (((ell : ℚ) / a p : ℚ) : ℚ_[p.1]) := by
  classical
  let exponent := auxiliaryPrimeExponent
  let modulus : {p : ℕ // p.Prime} → ℕ := fun p => p.1 ^ exponent p
  let unit (p : {p : ℕ // p.Prime}) (hp : p ∈ S) : ℤ_[p.1] :=
    rationalPadicUnit p (a p) (ha p hp) (hval p hp)
  let residue (p : {p : ℕ // p.Prime}) : ℕ :=
    if hp : p ∈ S then (unit p hp).appr (exponent p) else 1
  have hmod_ne (p : {p : ℕ // p.Prime}) : modulus p ≠ 0 := by
    exact pow_ne_zero _ p.2.ne_zero
  have hpair : Set.Pairwise (S : Set {p : ℕ // p.Prime})
      (Function.onFun Nat.Coprime modulus) := by
    intro p hp q hq hpq
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes p.2 q.2).2 fun h =>
      hpq (Subtype.ext h)
  let R : ℕ :=
    Nat.chineseRemainderOfFinset residue modulus S
      (fun p _ => hmod_ne p) hpair
  let M : ℕ := ∏ p ∈ S, modulus p
  have hM : M ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact hmod_ne p
  have hRcoprime : R.Coprime M := by
    apply Nat.Coprime.prod_right
    intro p hp
    rw [← ZMod.isUnit_iff_coprime]
    have hRmod : R ≡ residue p [MOD modulus p] :=
      (Nat.chineseRemainderOfFinset residue modulus S
        (fun q _ => hmod_ne q) hpair).prop p hp
    have hcast : (R : ZMod (modulus p)) = residue p :=
      (ZMod.natCast_eq_natCast_iff R (residue p) (modulus p)).2 hRmod
    rw [hcast]
    have hu : IsUnit (unit p hp) :=
      rationalPadicUnit_isUnit p (a p) (ha p hp) (hval p hp)
    have hmap := hu.map (PadicInt.toZModPow (exponent p))
    simpa [residue, hp, unit, modulus] using hmap
  obtain ⟨ell, hellM, hellPrime, hellCongr⟩ :=
    Nat.forall_exists_prime_gt_and_modEq M hM hRcoprime
  refine ⟨ell, hellPrime, ?_, ?_⟩
  · intro p hp hellp
    subst ell
    have hpdvd : p.1 ∣ M := by
      apply dvd_trans (dvd_pow_self p.1 (auxiliaryPrimeExponent_pos p).ne')
      exact Finset.dvd_prod_of_mem modulus hp
    exact (not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hpdvd)) hellM
  · intro p hp
    have hmod_dvd : modulus p ∣ M :=
      Finset.dvd_prod_of_mem modulus hp
    have hellLocal : ell ≡ residue p [MOD modulus p] :=
      (hellCongr.of_dvd hmod_dvd).trans
        ((Nat.chineseRemainderOfFinset residue modulus S
          (fun q _ => hmod_ne q) hpair).prop p hp)
    let u : ℤ_[p.1] := unit p hp
    have huNorm : ‖(a p : ℚ_[p.1])‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation]
      · simp [Padic.valuation_ratCast, hval p hp]
      · exact_mod_cast ha p hp
    have hmap : PadicInt.toZModPow (exponent p) (ell : ℤ_[p.1]) =
        PadicInt.toZModPow (exponent p) u := by
      calc
        PadicInt.toZModPow (exponent p) (ell : ℤ_[p.1]) =
            (ell : ZMod (modulus p)) := by simp
        _ = (residue p : ZMod (modulus p)) :=
          (ZMod.natCast_eq_natCast_iff ell (residue p)
            (modulus p)).2 hellLocal
        _ = ((u.appr (exponent p) : ℕ) : ZMod (modulus p)) := by
          simp [residue, hp, u]
        _ = PadicInt.toZModPow (exponent p) u := rfl
    have hmem : (ell : ℤ_[p.1]) - u ∈
        (Ideal.span {(p.1 : ℤ_[p.1]) ^ exponent p} : Ideal ℤ_[p.1]) := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
      simpa only [map_sub, sub_eq_zero] using hmap
    have hnormInt : ‖(ell : ℤ_[p.1]) - u‖ ≤
        (p.1 : ℝ) ^ (-(exponent p : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 hmem
    have hnormDiff : ‖(ell : ℚ_[p.1]) - (a p : ℚ_[p.1])‖ ≤
        (p.1 : ℝ) ^ (-(exponent p : ℤ)) := by
      simpa [u, unit, rationalPadicUnit] using hnormInt
    have hthreshold : (p.1 : ℝ) ^ (-(exponent p : ℤ)) <
        ‖(2 : ℚ_[p.1])‖ ^ 2 := by
      by_cases hp2 : p.1 = 2
      · have hnormTwo : ‖(2 : ℚ_[p.1])‖ = (2 : ℝ)⁻¹ := by
          have hcast : (2 : ℚ_[p.1]) = (p.1 : ℚ_[p.1]) := by
            exact_mod_cast hp2.symm
          calc
            ‖(2 : ℚ_[p.1])‖ = ‖(p.1 : ℚ_[p.1])‖ := congrArg norm hcast
            _ = (p.1 : ℝ)⁻¹ := Padic.norm_p
            _ = (2 : ℝ)⁻¹ := congrArg Inv.inv (by exact_mod_cast hp2)
        have hpReal : (p.1 : ℝ) = 2 := by exact_mod_cast hp2
        rw [show exponent p = 3 by simp [exponent, auxiliaryPrimeExponent, hp2],
          hpReal, hnormTwo]
        norm_num
      · have hnormTwo : ‖(2 : ℚ_[p.1])‖ = 1 := by
          change ‖((2 : ℕ) : ℚ_[p.1])‖ = 1
          rw [Padic.norm_natCast_eq_one_iff]
          exact (Nat.coprime_primes p.2 Nat.prime_two).2 hp2
        rw [show exponent p = 1 by simp [exponent, auxiliaryPrimeExponent, hp2],
          hnormTwo]
        simp only [one_pow]
        simpa only [zpow_neg, zpow_natCast, pow_one] using
          (inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt :
            (1 : ℝ) < p.1))
    apply padic_isSquare_of_norm_sub_one_lt_norm_two_sq
    have hratioNorm :
        ‖((((ell : ℚ) / a p : ℚ) : ℚ_[p.1])) - 1‖ =
          ‖(ell : ℚ_[p.1]) - (a p : ℚ_[p.1])‖ := by
      have hap : (a p : ℚ_[p.1]) ≠ 0 := by exact_mod_cast ha p hp
      push_cast
      rw [div_sub_one hap, norm_div, huNorm, div_one]
    rw [hratioNorm]
    exact hnormDiff.trans_lt hthreshold

/-- The finite set of primes where a rational number has odd valuation parity.
It is the prime support of the canonical signed squarefree representative. -/
def rationalOddValuationPrimeSet (q : ℚ) : Finset ℕ :=
  (hilbertSignedSquarefreeInteger q).natAbs.primeFactors

/-- Membership in the canonical odd-valuation support is exactly p-adic
valuation parity one. -/
theorem prime_mem_rationalOddValuationPrimeSet_iff
    {q : ℚ} (hq : q ≠ 0) {p : ℕ} [Fact p.Prime] :
    p ∈ rationalOddValuationPrimeSet q ↔ valuationParity p q = 1 := by
  let z : ℤ := hilbertSignedSquarefreeInteger q
  let s : ℚ := (hilbertSquareClassRootPart q : ℚ) / q.den
  have hz : z ≠ 0 := hilbertSignedSquarefreeInteger_ne_zero hq
  have hsq : Squarefree z.natAbs :=
    hilbertSignedSquarefreeInteger_natAbs_squarefree hq
  have hs : s ≠ 0 := hilbertSquareClassRootPart_div_den_ne_zero hq
  have hqeq : q = (z : ℚ) * s ^ 2 :=
    eq_signedSquarefreeInteger_mul_rootPart_div_den_sq hq
  have hpar : valuationParity p q = valuationParity p (z : ℚ) := by
    rw [hqeq]
    exact valuationParity_mul_sq (z : ℚ) s (by exact_mod_cast hz) hs
  rw [hpar]
  constructor
  · intro hp
    apply valuationParity_intCast_eq_one_of_squarefree_dvd p z hz hsq
    exact Nat.dvd_of_mem_primeFactors hp
  · intro hp
    by_contra hnot
    have hpndvd : ¬p ∣ z.natAbs := by
      intro hpd
      apply hnot
      exact (Fact.out : p.Prime).mem_primeFactors hpd
        (Int.natAbs_ne_zero.mpr hz)
    have hzero := valuationParity_intCast_eq_zero_of_not_dvd p z hpndvd
    omega

/-- A finite collection of rational local square classes can be realized by a
rational whose odd valuation support introduces at most one fresh prime. This
applies in particular when the finite set contains the dyadic place. -/
theorem exists_rat_with_prescribed_local_squareClasses_and_one_auxiliary_prime
    (S : Finset {p : ℕ // p.Prime})
    (aReal : ℚ) (haReal : aReal ≠ 0)
    (a : {p : ℕ // p.Prime} → ℚ)
    (ha : ∀ p ∈ S, a p ≠ 0) :
    ∃ ell : ℕ, ∃ q : ℚ,
      ell.Prime ∧ (∀ p ∈ S, ell ≠ p.1) ∧ q ≠ 0 ∧
      IsSquare ((q / aReal : ℚ) : ℝ) ∧
      (∀ p ∈ S, IsSquare ((q / a p : ℚ) : ℚ_[p.1])) ∧
      rationalOddValuationPrimeSet q ⊆
        S.image (fun p => p.1) ∪ {ell} := by
  classical
  let d := auxiliaryPrimeValuationBase S a aReal
  have hd : d ≠ 0 := auxiliaryPrimeValuationBase_ne_zero S a aReal
  have hunit_ne (p : {p : ℕ // p.Prime}) (hp : p ∈ S) : a p / d ≠ 0 :=
    div_ne_zero (ha p hp) hd
  have hunit_val (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      padicValRat p.1 (a p / d) = 0 := by
    rw [padicValRat.div (ha p hp) hd,
      padicValRat_auxiliaryPrimeValuationBase S a aReal p hp]
    simp
  obtain ⟨ell, hellPrime, hellFresh, hellSquare⟩ :=
    exists_fresh_prime_with_prescribed_local_unit_squareClasses S
      (fun p => a p / d) hunit_ne hunit_val
  let q : ℚ := d * ell
  have hellQ : (ell : ℚ) ≠ 0 := by exact_mod_cast hellPrime.ne_zero
  have hq : q ≠ 0 := mul_ne_zero hd hellQ
  refine ⟨ell, q, hellPrime, hellFresh, hq, ?_, ?_, ?_⟩
  · rw [Real.isSquare_iff]
    have hprodpos : 0 < ∏ p ∈ S,
        (p.1 : ℚ) ^ padicValRat p.1 (a p) := by
      apply Finset.prod_pos
      intro p hp
      exact zpow_pos (by exact_mod_cast p.2.pos) _
    have hddiv : 0 < d / aReal := by
      by_cases hpos : 0 < aReal
      · simp only [d, auxiliaryPrimeValuationBase, if_pos hpos, one_mul]
        exact div_pos hprodpos hpos
      · have hneg : aReal < 0 := lt_of_le_of_ne (le_of_not_gt hpos)
          haReal
        simp only [d, auxiliaryPrimeValuationBase, if_neg hpos, neg_one_mul]
        exact div_pos_of_neg_of_neg (neg_neg_of_pos hprodpos) hneg
    have hellPos : (0 : ℚ) < ell := by exact_mod_cast hellPrime.pos
    have hrat : 0 < q / aReal := by
      rw [show q / aReal = (d / aReal) * ell by simp [q]; ring]
      positivity
    exact_mod_cast hrat.le
  · intro p hp
    have hsquare := hellSquare p hp
    have heq : q / a p = (ell : ℚ) / (a p / d) := by
      field_simp [q, ha p hp, hd]; ring
    rw [heq]
    exact hsquare
  · intro k hk
    have hkPrime : k.Prime := by
      have hk' : k ∈ (hilbertSignedSquarefreeInteger q).natAbs.primeFactors := by
        simpa only [rationalOddValuationPrimeSet] using hk
      exact (Nat.mem_primeFactors.mp hk').1
    by_cases hkell : k = ell
    · exact Finset.mem_union_right _ (by simp [hkell])
    by_cases hkS : ∃ p ∈ S, p.1 = k
    · obtain ⟨p, hp, hpk⟩ := hkS
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, hpk⟩)
    · let p : {p : ℕ // p.Prime} := ⟨k, hkPrime⟩
      have hpnot : p ∉ S := by
        intro hp
        exact hkS ⟨p, hp, rfl⟩
      have hdval : padicValRat k d = 0 := by
        simpa [p, d] using
          padicValRat_auxiliaryPrimeValuationBase_of_not_mem S a aReal p hpnot
      letI : Fact k.Prime := ⟨hkPrime⟩
      letI : Fact ell.Prime := ⟨hellPrime⟩
      have hellval : padicValRat k (ell : ℚ) = 0 := by
        rw [padicValRat.of_nat, padicValNat_primes hkell]
        simp
      have hpar0 : valuationParity k q = 0 := by
        rw [valuationParity, show q = d * (ell : ℚ) by rfl,
          padicValRat.mul hd hellQ, hdval, hellval]
        norm_num
      have hpar1 := (prime_mem_rationalOddValuationPrimeSet_iff hq).1 hk
      omega

lemma valuationParity_eq_zero_of_not_mem_rationalOddValuationPrimeSet
    {q : ℚ} (hq : q ≠ 0) {p : ℕ} [Fact p.Prime]
    (hp : p ∉ rationalOddValuationPrimeSet q) :
    valuationParity p q = 0 := by
  rcases valuationParity_eq_zero_or_one p q with h | h
  · exact h
  · exact False.elim
      (hp ((prime_mem_rationalOddValuationPrimeSet_iff hq).2 h))

/-- Away from its odd-valuation support, a nonzero rational is a p-adic
integral unit times a nonzero square. -/
theorem exists_padicInt_unit_sq_mul_eq_of_not_mem_rationalOddValuationPrimeSet
    {q : ℚ} (hq : q ≠ 0) {p : ℕ} [Fact p.Prime]
    (hp : p ∉ rationalOddValuationPrimeSet q) :
    ∃ C : ℤ_[p], IsUnit C ∧ ∃ s : ℚ_[p], s ≠ 0 ∧
      (q : ℚ_[p]) = s ^ 2 * (C : ℚ_[p]) := by
  have hpar :=
    valuationParity_eq_zero_of_not_mem_rationalOddValuationPrimeSet hq hp
  obtain ⟨x, hx, C, hCunit, hCeq, _htransport⟩ :=
    PositiveDefiniteIntegralLattice.exists_padicInt_unit_target_square_normalization hq hpar
  have hxp : (x : ℚ_[p]) ≠ 0 := by exact_mod_cast hx
  refine ⟨C, hCunit, (x : ℚ_[p])⁻¹, inv_ne_zero hxp, ?_⟩
  rw [hCeq]
  push_cast
  field_simp

/-- At a prime outside both finite supports, the fixed rational binary forms
commonly represent a nonzero rational target. -/
theorem binaryCommonRepresents_rat_of_not_mem_binaryPairBadPrimeSet_of_not_mem_rationalOddValuationPrimeSet
    (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    {q : ℚ} (hq : q ≠ 0) {p : ℕ} [Fact p.Prime]
    (hpbad : p ∉ binaryPairBadPrimeSet A B)
    (hpodd : p ∉ rationalOddValuationPrimeSet q) :
    PositiveDefiniteIntegralLattice.BinaryCommonRepresents
      (A.map (algebraMap ℚ ℚ_[p])) (B.map (algebraMap ℚ ℚ_[p]))
      (q : ℚ_[p]) := by
  obtain ⟨C, hCunit, s, _hs, hqeq⟩ :=
    exists_padicInt_unit_sq_mul_eq_of_not_mem_rationalOddValuationPrimeSet
      hq hpodd
  have hcommon :=
    binaryCommonRepresents_padic_unit_of_not_mem_binaryPairBadPrimeSet
      A B hA_symm hA_det hB_symm hB_det hpbad hCunit
  rw [hqeq]
  exact hcommon.sq_mul s

/-- Equivalently, common representation holds outside the union of the fixed
binary bad-prime support and the target's odd-valuation support. -/
theorem binaryCommonRepresents_rat_of_not_mem_badPrime_union_oddValuation
    (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    {q : ℚ} (hq : q ≠ 0) {p : ℕ} [Fact p.Prime]
    (hp : p ∉ binaryPairBadPrimeSet A B ∪ rationalOddValuationPrimeSet q) :
    PositiveDefiniteIntegralLattice.BinaryCommonRepresents
      (A.map (algebraMap ℚ ℚ_[p])) (B.map (algebraMap ℚ ℚ_[p]))
      (q : ℚ_[p]) := by
  apply
    binaryCommonRepresents_rat_of_not_mem_binaryPairBadPrimeSet_of_not_mem_rationalOddValuationPrimeSet
      A B hA_symm hA_det hB_symm hB_det hq
  · exact fun hmem ↦ hp (Finset.mem_union_left _ hmem)
  · exact fun hmem ↦ hp (Finset.mem_union_right _ hmem)

/-- A nonzero rational target that is commonly represented over the reals and
at every fixed bad prime is commonly represented over the rationals, provided
all of its odd-valuation primes lie in that fixed bad-prime set. -/
theorem binaryCommonRepresents_rat_of_real_and_badPrimes_of_oddValuationPrimeSet_subset
    (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    {q : ℚ} (hq : q ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.BinaryCommonRepresents
      (A.map (algebraMap ℚ ℝ)) (B.map (algebraMap ℚ ℝ)) (q : ℝ))
    (hbad : ∀ (p : ℕ) [Fact p.Prime], p ∈ binaryPairBadPrimeSet A B →
      PositiveDefiniteIntegralLattice.BinaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p])) (B.map (algebraMap ℚ ℚ_[p]))
        (q : ℚ_[p]))
    (hsupport : rationalOddValuationPrimeSet q ⊆ binaryPairBadPrimeSet A B) :
    PositiveDefiniteIntegralLattice.BinaryCommonRepresents A B q := by
  have hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.BinaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p])) (B.map (algebraMap ℚ ℚ_[p]))
        (q : ℚ_[p]) := by
    intro p hp
    by_cases hpbad : p ∈ binaryPairBadPrimeSet A B
    · exact hbad p hpbad
    · apply
        binaryCommonRepresents_rat_of_not_mem_binaryPairBadPrimeSet_of_not_mem_rationalOddValuationPrimeSet
          A B hA_symm hA_det hB_symm hB_det hq hpbad
      exact fun hpodd ↦ hpbad (hsupport hpodd)
  constructor
  · exact exists_binary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det q hq hreal.1 (fun p _ ↦ (hpadic p).1)
  · exact exists_binary_gramQuadraticValue_eq_rat_of_real_and_padic
      B hB_symm hB_det q hq hreal.2 (fun p _ ↦ (hpadic p).2)

private def binaryPairBadPrimes
    (A B : Matrix (Fin 2) (Fin 2) ℚ) : Finset {p : ℕ // p.Prime} :=
  ((binaryPairBadPrimeSet A B).attach).map
    ⟨fun p => ⟨p.1, by
        exact (Nat.mem_primeFactors.mp
          (show p.1 ∈ (binaryPairBadPrimeSupportNat A B).primeFactors from p.2)).1⟩,
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun z : {p : ℕ // p.Prime} => z.1) hpq⟩

private lemma mem_binaryPairBadPrimes_iff
    (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (p : {p : ℕ // p.Prime}) :
    p ∈ binaryPairBadPrimes A B ↔
      p.1 ∈ binaryPairBadPrimeSet A B := by
  rw [binaryPairBadPrimes, Finset.mem_map]
  constructor
  · rintro ⟨q, _hq, rfl⟩
    exact q.property
  · intro hp
    refine ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, ?_⟩
    rfl

private lemma binaryCommonRepresents_of_div_isSquare
    {K : Type*} [Field K]
    {A B : Matrix (Fin 2) (Fin 2) K} {c q : K}
    (hc : c ≠ 0)
    (hcommon : PositiveDefiniteIntegralLattice.BinaryCommonRepresents A B c)
    (hsquare : IsSquare (q / c)) :
    PositiveDefiniteIntegralLattice.BinaryCommonRepresents A B q := by
  obtain ⟨s, hs⟩ := hsquare
  have hq : q = s ^ 2 * c := by
    rw [div_eq_iff hc] at hs
    simpa [pow_two] using hs
  rw [hq]
  exact hcommon.sq_mul s

/-- Two fixed nonsingular symmetric rational binary forms with a common
nonzero represented value at every completion have a common nonzero rational
represented value. -/
theorem exists_binaryCommonRepresents_rat_of_real_and_padic
    (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : ∃ c : ℝ, c ≠ 0 ∧
      PositiveDefiniteIntegralLattice.BinaryCommonRepresents
        (A.map (algebraMap ℚ ℝ)) (B.map (algebraMap ℚ ℝ)) c)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
      PositiveDefiniteIntegralLattice.BinaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p])) (B.map (algebraMap ℚ ℚ_[p])) c) :
    ∃ q : ℚ, q ≠ 0 ∧ PositiveDefiniteIntegralLattice.BinaryCommonRepresents A B q := by
  classical
  let S := binaryPairBadPrimes A B
  obtain ⟨cReal, hcReal, hcommonReal⟩ := hreal
  obtain ⟨UReal, hURealOpen, hcRealU, hURealSub⟩ :=
    exists_isOpen_mem_subset_real_binaryCommonRepresents hcReal hcommonReal
  have hpadic' (p : {p : ℕ // p.Prime}) : ∃ c : ℚ_[p.1], c ≠ 0 ∧
      PositiveDefiniteIntegralLattice.BinaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1])) c :=
    hpadic p.1
  choose cPadic hcPadic hcommonPadic using hpadic'
  have hopenPadic (p : {p : ℕ // p.Prime}) : ∃ U : Set ℚ_[p.1],
      IsOpen U ∧ cPadic p ∈ U ∧ U ⊆
        {y | PositiveDefiniteIntegralLattice.BinaryCommonRepresents
          (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1])) y} :=
    exists_isOpen_mem_subset_padic_binaryCommonRepresents
      (hcPadic p) (hcommonPadic p)
  choose UPadic hUPadicOpen hcPadicU hUPadicSub using hopenPadic
  obtain ⟨r, hrReal, hrPadic⟩ :=
    exists_rat_mem_real_and_finitely_many_padic_opens S
      (UReal \ {0}) (fun p => UPadic p \ {0})
      (hURealOpen.sdiff isClosed_singleton)
      ⟨cReal, hcRealU, by simpa using hcReal⟩
      (fun p _ => (hUPadicOpen p).sdiff isClosed_singleton)
      (fun p _ => ⟨cPadic p, hcPadicU p, by simpa using hcPadic p⟩)
  have hr : r ≠ 0 := by
    intro hrzero
    apply hrReal.2
    simp [hrzero]
  have hcommonRealR : PositiveDefiniteIntegralLattice.BinaryCommonRepresents
      (A.map (algebraMap ℚ ℝ)) (B.map (algebraMap ℚ ℝ)) (r : ℝ) :=
    hURealSub hrReal.1
  have hcommonPadicR (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      PositiveDefiniteIntegralLattice.BinaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1]))
        (r : ℚ_[p.1]) :=
    hUPadicSub p (hrPadic p hp).1
  obtain ⟨ell, q, hellPrime, _hellFresh, hq, hqRealSquare,
      hqPadicSquare, hsupport⟩ :=
    exists_rat_with_prescribed_local_squareClasses_and_one_auxiliary_prime
      S r hr (fun _ => r) (fun _ _ => hr)
  let ell' : {p : ℕ // p.Prime} := ⟨ell, hellPrime⟩
  have hcommonRealQ : PositiveDefiniteIntegralLattice.BinaryCommonRepresents
      (A.map (algebraMap ℚ ℝ)) (B.map (algebraMap ℚ ℝ)) (q : ℝ) :=
    binaryCommonRepresents_of_div_isSquare
      (by exact_mod_cast hr) hcommonRealR (by simpa using hqRealSquare)
  have hcommonBadQ (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      PositiveDefiniteIntegralLattice.BinaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1]))
        (q : ℚ_[p.1]) :=
    binaryCommonRepresents_of_div_isSquare
      (by exact_mod_cast hr) (hcommonPadicR p hp)
      (by simpa using hqPadicSquare p hp)
  have hcommonExcept (p : {p : ℕ // p.Prime}) (hpell : p ≠ ell') :
      PositiveDefiniteIntegralLattice.BinaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1]))
        (q : ℚ_[p.1]) := by
    by_cases hpS : p ∈ S
    · exact hcommonBadQ p hpS
    · apply
        binaryCommonRepresents_rat_of_not_mem_binaryPairBadPrimeSet_of_not_mem_rationalOddValuationPrimeSet
          A B hA_symm hA_det hB_symm hB_det hq
      · exact fun hpbad => hpS ((mem_binaryPairBadPrimes_iff A B p).2 hpbad)
      · intro hpodd
        rcases Finset.mem_union.mp (hsupport hpodd) with hpimage | hpaux
        · obtain ⟨p', hp'S, hp'eq⟩ := Finset.mem_image.mp hpimage
          apply hpS
          exact (Subtype.ext hp'eq) ▸ hp'S
        · apply hpell
          apply Subtype.ext
          simpa using hpaux
  have hrepEllA :=
    exists_binary_gramQuadraticValue_eq_padic_of_real_and_all_but_one
      A hA_symm hA_det q hq ell' hcommonRealQ.1
      (fun p hp => (hcommonExcept p hp).1)
  have hrepEllB :=
    exists_binary_gramQuadraticValue_eq_padic_of_real_and_all_but_one
      B hB_symm hB_det q hq ell' hcommonRealQ.2
      (fun p hp => (hcommonExcept p hp).2)
  have hcommonAll (p : {p : ℕ // p.Prime}) :
      PositiveDefiniteIntegralLattice.BinaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1]))
        (q : ℚ_[p.1]) := by
    by_cases hpell : p = ell'
    · subst p
      exact ⟨hrepEllA, hrepEllB⟩
    · exact hcommonExcept p hpell
  refine ⟨q, hq, ?_, ?_⟩
  · exact exists_binary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det q hq hcommonRealQ.1
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).1)
  · exact exists_binary_gramQuadraticValue_eq_rat_of_real_and_padic
      B hB_symm hB_det q hq hcommonRealQ.2
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).2)

private def binaryTernaryBadPrimes
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (B : Matrix (Fin 3) (Fin 3) ℚ) : Finset {p : ℕ // p.Prime} :=
  ((binaryTernaryBadPrimeSet A B).attach).map
    ⟨fun p => ⟨p.1, by
        exact (Nat.mem_primeFactors.mp
          (show p.1 ∈ (binaryTernaryBadPrimeSupportNat A B).primeFactors from
            p.2)).1⟩,
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun z : {p : ℕ // p.Prime} => z.1) hpq⟩

private lemma mem_binaryTernaryBadPrimes_iff
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (B : Matrix (Fin 3) (Fin 3) ℚ)
    (p : {p : ℕ // p.Prime}) :
    p ∈ binaryTernaryBadPrimes A B ↔
      p.1 ∈ binaryTernaryBadPrimeSet A B := by
  rw [binaryTernaryBadPrimes, Finset.mem_map]
  constructor
  · rintro ⟨q, _hq, rfl⟩
    exact q.property
  · intro hp
    refine ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, ?_⟩
    rfl

private lemma binaryTernaryCommonRepresents_of_div_isSquare
    {K : Type*} [Field K]
    {A : Matrix (Fin 2) (Fin 2) K}
    {B : Matrix (Fin 3) (Fin 3) K} {c q : K}
    (hc : c ≠ 0)
    (hcommon : PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents A B c)
    (hsquare : IsSquare (q / c)) :
    PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents A B q := by
  obtain ⟨s, hs⟩ := hsquare
  have hq : q = s ^ 2 * c := by
    rw [div_eq_iff hc] at hs
    simpa [pow_two] using hs
  rw [hq]
  exact hcommon.sq_mul s

private theorem binaryTernaryCommonRepresents_rat_of_good_even_place
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (B : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    {q : ℚ} (hq : q ≠ 0) {p : ℕ} [Fact p.Prime]
    (hpbad : p ∉ binaryTernaryBadPrimeSet A B)
    (hpodd : p ∉ rationalOddValuationPrimeSet q) :
    PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
      (A.map (algebraMap ℚ ℚ_[p])) (B.map (algebraMap ℚ ℚ_[p]))
      (q : ℚ_[p]) := by
  obtain ⟨C, hCunit, s, _hs, hqeq⟩ :=
    exists_padicInt_unit_sq_mul_eq_of_not_mem_rationalOddValuationPrimeSet
      hq hpodd
  have hcommon : PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
      (A.map (algebraMap ℚ ℚ_[p])) (B.map (algebraMap ℚ ℚ_[p]))
      (C : ℚ_[p]) :=
    binaryTernaryCommonRepresents_padic_unit_of_not_mem_badPrimeSet
      A B hA_symm hA_det hB_symm hB_det hpbad hCunit
  rw [hqeq]
  exact hcommon.sq_mul s

/-- A nonsingular symmetric rational rank-four Gram matrix that is isotropic
over the reals and every p-adic field is isotropic over the rationals. -/
theorem rankFourGramIsotropic_rat_of_real_and_padic
    (M : Matrix (Fin 4) (Fin 4) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    PositiveDefiniteIntegralLattice.GramIsotropic M := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP,
      hcommonReal, hcommonPadic⟩ :=
    exists_binaryPairDifferenceGramBlock_common_values_of_rankFour_real_and_padic
      M hM_symm hM_det hreal hpadic
  obtain ⟨q, hq, hcommon⟩ :=
    exists_binaryCommonRepresents_rat_of_real_and_padic
      A B hA_symm hA_det hB_symm hB_det hcommonReal hcommonPadic
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.binaryPairDifferenceGramBlock A B) :=
    (PositiveDefiniteIntegralLattice.gramIsotropic_binaryPairDifferenceGramBlock_iff_exists_common_value
      A B hA_symm hA_det hB_symm hB_det (by norm_num)).2
      ⟨q, hq, hcommon⟩
  exact PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
    (show (PositiveDefiniteIntegralLattice.binaryPairDifferenceGramBlock A B).IsCongruent M from
      (show M.IsCongruent
        (PositiveDefiniteIntegralLattice.binaryPairDifferenceGramBlock A B) from ⟨P, hP⟩).symm)
    hblock

/-- Rank-four Hasse--Minkowski for arbitrary nonsingular symmetric rational
Gram matrices. -/
theorem rankFourGramIsotropic_iff_real_and_padic
    (M : Matrix (Fin 4) (Fin 4) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic M ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℝ)) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          PositiveDefiniteIntegralLattice.GramIsotropic
            (M.map (algebraMap ℚ ℚ_[p])) := by
  constructor
  · intro hM
    exact ⟨gramIsotropic_scalarExtension_of_rat (K := ℝ) hM,
      fun p _ => gramIsotropic_scalarExtension_of_rat (K := ℚ_[p]) hM⟩
  · rintro ⟨hreal, hpadic⟩
    exact rankFourGramIsotropic_rat_of_real_and_padic
      M hM_symm hM_det hreal hpadic

/-- A nonzero scalar locally represented by a nonsingular symmetric rational
ternary form is represented over the rationals. -/
theorem exists_ternary_gramQuadraticValue_eq_rat_of_real_and_padic
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0)
    (hreal : ∃ v : Fin 3 → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 3 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p])) :
    ∃ v : Fin 3 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c := by
  let B : Matrix (Fin 4) (Fin 4) ℚ :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock (-c) A
  have hB_symm : B.IsSymm :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock_isSymm (-c) A hA_symm
  have hB_det : B.det ≠ 0 := by
    simp only [B, PositiveDefiniteIntegralLattice.finSuccGramBlock_det]
    exact mul_ne_zero (neg_ne_zero.mpr hc) hA_det
  have hB_real : PositiveDefiniteIntegralLattice.GramIsotropic
      (B.map (algebraMap ℚ ℝ)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℝ) (A.map (algebraMap ℚ ℝ)) hreal
    simpa [B] using h
  have hB_padic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic (B.map (algebraMap ℚ ℚ_[p])) := by
    intro p hp
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℚ_[p]) (A.map (algebraMap ℚ ℚ_[p])) (hpadic p)
    simpa [B] using h
  have hB : PositiveDefiniteIntegralLattice.GramIsotropic B :=
    rankFourGramIsotropic_rat_of_real_and_padic
      B hB_symm hB_det hB_real hB_padic
  rcases PositiveDefiniteIntegralLattice.gramIsotropic_or_exists_value_of_finSuccGramBlock
      c A hB with hA | hrep
  · exact PositiveDefiniteIntegralLattice.exists_ternary_gramQuadraticValue_eq_of_gramIsotropic
      A hA_symm hA_det (by norm_num) hA c
  · exact hrep

/-- Nonzero scalar representation by a nonsingular symmetric rational ternary
form is equivalent to representation over the real and every p-adic field. -/
theorem exists_ternary_gramQuadraticValue_eq_iff_real_and_padic
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0) :
    (∃ v : Fin 3 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c) ↔
      (∃ v : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 3 → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p]) := by
  constructor
  · intro hrep
    exact ⟨exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℝ) hrep,
      fun p _ => exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℚ_[p]) hrep⟩
  · rintro ⟨hreal, hpadic⟩
    exact exists_ternary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det c hc hreal hpadic

/-- Fixed nonsingular symmetric rational binary and ternary forms with a
common nonzero represented value at every completion have a common nonzero
rational represented value. -/
theorem exists_binaryTernaryCommonRepresents_rat_of_real_and_padic
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (B : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : ∃ c : ℝ, c ≠ 0 ∧
      PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
        (A.map (algebraMap ℚ ℝ)) (B.map (algebraMap ℚ ℝ)) c)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
      PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p])) (B.map (algebraMap ℚ ℚ_[p])) c) :
    ∃ q : ℚ, q ≠ 0 ∧
      PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents A B q := by
  classical
  let S := binaryTernaryBadPrimes A B
  obtain ⟨cReal, hcReal, hcommonReal⟩ := hreal
  obtain ⟨UReal, hURealOpen, hcRealU, hURealSq⟩ :=
    exists_isOpen_mem_subset_real_nonzeroSqOrbit hcReal
  have hpadic' (p : {p : ℕ // p.Prime}) : ∃ c : ℚ_[p.1], c ≠ 0 ∧
      PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1])) c :=
    hpadic p.1
  choose cPadic hcPadic hcommonPadic using hpadic'
  have hopenPadic (p : {p : ℕ // p.Prime}) : ∃ U : Set ℚ_[p.1],
      IsOpen U ∧ cPadic p ∈ U ∧
        U ⊆ {y | ∃ s : ℚ_[p.1], s ≠ 0 ∧ y = s ^ 2 * cPadic p} :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit (hcPadic p)
  choose UPadic hUPadicOpen hcPadicU hUPadicSq using hopenPadic
  obtain ⟨r, hrReal, hrPadic⟩ :=
    exists_rat_mem_real_and_finitely_many_padic_opens S
      (UReal \ {0}) (fun p => UPadic p \ {0})
      (hURealOpen.sdiff isClosed_singleton)
      ⟨cReal, hcRealU, by simpa using hcReal⟩
      (fun p _ => (hUPadicOpen p).sdiff isClosed_singleton)
      (fun p _ => ⟨cPadic p, hcPadicU p, by simpa using hcPadic p⟩)
  have hr : r ≠ 0 := by
    intro hrzero
    apply hrReal.2
    simp [hrzero]
  have hcommonRealR : PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
      (A.map (algebraMap ℚ ℝ)) (B.map (algebraMap ℚ ℝ)) (r : ℝ) := by
    obtain ⟨s, _hs, hrs⟩ := hURealSq hrReal.1
    rw [hrs]
    exact hcommonReal.sq_mul s
  have hcommonPadicR (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1]))
        (r : ℚ_[p.1]) := by
    obtain ⟨s, _hs, hrs⟩ := hUPadicSq p (hrPadic p hp).1
    rw [hrs]
    exact (hcommonPadic p).sq_mul s
  obtain ⟨ell, q, hellPrime, hellFresh, hq, hqRealSquare,
      hqPadicSquare, hsupport⟩ :=
    exists_rat_with_prescribed_local_squareClasses_and_one_auxiliary_prime
      S r hr (fun _ => r) (fun _ _ => hr)
  let ell' : {p : ℕ // p.Prime} := ⟨ell, hellPrime⟩
  have hellNotS : ell' ∉ S := by
    intro hellS
    exact (hellFresh ell' hellS) rfl
  have hellNotBad : ell ∉ binaryTernaryBadPrimeSet A B := by
    intro hellBad
    exact hellNotS ((mem_binaryTernaryBadPrimes_iff A B ell').2 hellBad)
  have hcommonRealQ : PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
      (A.map (algebraMap ℚ ℝ)) (B.map (algebraMap ℚ ℝ)) (q : ℝ) :=
    binaryTernaryCommonRepresents_of_div_isSquare
      (by exact_mod_cast hr) hcommonRealR (by simpa using hqRealSquare)
  have hcommonBadQ (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1]))
        (q : ℚ_[p.1]) :=
    binaryTernaryCommonRepresents_of_div_isSquare
      (by exact_mod_cast hr) (hcommonPadicR p hp)
      (by simpa using hqPadicSquare p hp)
  have hcommonExcept (p : {p : ℕ // p.Prime}) (hpell : p ≠ ell') :
      PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1]))
        (q : ℚ_[p.1]) := by
    by_cases hpS : p ∈ S
    · exact hcommonBadQ p hpS
    · apply binaryTernaryCommonRepresents_rat_of_good_even_place
        A B hA_symm hA_det hB_symm hB_det hq
      · exact fun hpbad =>
          hpS ((mem_binaryTernaryBadPrimes_iff A B p).2 hpbad)
      · intro hpodd
        rcases Finset.mem_union.mp (hsupport hpodd) with hpimage | hpaux
        · obtain ⟨p', hp'S, hp'eq⟩ := Finset.mem_image.mp hpimage
          apply hpS
          exact (Subtype.ext hp'eq) ▸ hp'S
        · apply hpell
          apply Subtype.ext
          simpa using hpaux
  have hrepEllA :=
    exists_binary_gramQuadraticValue_eq_padic_of_real_and_all_but_one
      A hA_symm hA_det q hq ell' hcommonRealQ.1
      (fun p hp => (hcommonExcept p hp).1)
  letI : Fact ell.Prime := ⟨hellPrime⟩
  obtain ⟨hellOdd, _hAden, hBden, _hAnum, _hAdenDet,
      hBnum, hBdenDet⟩ :=
    matrixPairGoodPrimeData A B hA_det hB_det hellPrime hellNotBad
  let Bp := rationalMatrixPadicInt B hBden
  have hBpMap : Bp.map PadicInt.Coe.ringHom =
      B.map (algebraMap ℚ ℚ_[ell]) :=
    rationalMatrixPadicInt_map B hBden
  have hrepEllB : ∃ v : Fin 3 → ℚ_[ell],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[ell])) v = (q : ℚ_[ell]) := by
    simpa [hBpMap] using
      PositiveDefiniteIntegralLattice.exists_ternary_gramQuadraticValue_eq_padic_of_integral
        hellOdd Bp
          (rationalMatrixPadicInt_isSymm B hB_symm hBden)
          (rationalMatrixPadicInt_det_isUnit
            B hB_det hBden hBnum hBdenDet) (q : ℚ_[ell])
  have hcommonAll (p : {p : ℕ // p.Prime}) :
      PositiveDefiniteIntegralLattice.BinaryTernaryCommonRepresents
        (A.map (algebraMap ℚ ℚ_[p.1])) (B.map (algebraMap ℚ ℚ_[p.1]))
        (q : ℚ_[p.1]) := by
    by_cases hpell : p = ell'
    · subst p
      exact ⟨hrepEllA, hrepEllB⟩
    · exact hcommonExcept p hpell
  refine ⟨q, hq, ?_, ?_⟩
  · exact exists_binary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det q hq hcommonRealQ.1
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).1)
  · exact exists_ternary_gramQuadraticValue_eq_rat_of_real_and_padic
      B hB_symm hB_det q hq hcommonRealQ.2
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).2)

/-- A nonsingular symmetric rational rank-five Gram matrix that is isotropic
over the reals and every p-adic field is isotropic over the rationals. -/
theorem rankFiveGramIsotropic_rat_of_real_and_padic
    (M : Matrix (Fin 5) (Fin 5) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    PositiveDefiniteIntegralLattice.GramIsotropic M := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP,
      hcommonReal, hcommonPadic⟩ :=
    exists_binaryTernaryDifferenceGramBlock_common_values_of_rankFive_real_and_padic
      M hM_symm hM_det hreal hpadic
  obtain ⟨q, hq, hcommon⟩ :=
    exists_binaryTernaryCommonRepresents_rat_of_real_and_padic
      A B hA_symm hA_det hB_symm hB_det hcommonReal hcommonPadic
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.binaryTernaryDifferenceGramBlock A B) :=
    (PositiveDefiniteIntegralLattice.gramIsotropic_binaryTernaryDifferenceGramBlock_iff_exists_common_value
      A B hA_symm hA_det hB_symm hB_det (by norm_num)).2
      ⟨q, hq, hcommon⟩
  exact PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
    (show (PositiveDefiniteIntegralLattice.binaryTernaryDifferenceGramBlock A B).IsCongruent M from
      (show M.IsCongruent
        (PositiveDefiniteIntegralLattice.binaryTernaryDifferenceGramBlock A B) from
          ⟨P, hP⟩).symm)
    hblock

/-- Rank-five Hasse--Minkowski for arbitrary nonsingular symmetric rational
Gram matrices. -/
theorem rankFiveGramIsotropic_iff_real_and_padic
    (M : Matrix (Fin 5) (Fin 5) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic M ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℝ)) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          PositiveDefiniteIntegralLattice.GramIsotropic
            (M.map (algebraMap ℚ ℚ_[p])) := by
  constructor
  · intro hM
    exact ⟨gramIsotropic_scalarExtension_of_rat (K := ℝ) hM,
      fun p _ => gramIsotropic_scalarExtension_of_rat (K := ℚ_[p]) hM⟩
  · rintro ⟨hreal, hpadic⟩
    exact rankFiveGramIsotropic_rat_of_real_and_padic
      M hM_symm hM_det hreal hpadic

/-- A nonzero scalar locally represented by a nonsingular symmetric rational
quaternary form is represented over the rationals. -/
theorem exists_quaternary_gramQuadraticValue_eq_rat_of_real_and_padic
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0)
    (hreal : ∃ v : Fin 4 → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 4 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p])) :
    ∃ v : Fin 4 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c := by
  let B : Matrix (Fin 5) (Fin 5) ℚ :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock (-c) A
  have hB_symm : B.IsSymm :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock_isSymm (-c) A hA_symm
  have hB_det : B.det ≠ 0 := by
    simp only [B, PositiveDefiniteIntegralLattice.finSuccGramBlock_det]
    exact mul_ne_zero (neg_ne_zero.mpr hc) hA_det
  have hB_real : PositiveDefiniteIntegralLattice.GramIsotropic
      (B.map (algebraMap ℚ ℝ)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℝ) (A.map (algebraMap ℚ ℝ)) hreal
    simpa [B] using h
  have hB_padic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic (B.map (algebraMap ℚ ℚ_[p])) := by
    intro p hp
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℚ_[p]) (A.map (algebraMap ℚ ℚ_[p])) (hpadic p)
    simpa [B] using h
  have hB : PositiveDefiniteIntegralLattice.GramIsotropic B :=
    rankFiveGramIsotropic_rat_of_real_and_padic
      B hB_symm hB_det hB_real hB_padic
  rcases PositiveDefiniteIntegralLattice.gramIsotropic_or_exists_value_of_finSuccGramBlock
      c A hB with hA | hrep
  · exact PositiveDefiniteIntegralLattice.exists_quaternary_gramQuadraticValue_eq_of_gramIsotropic
      A hA_symm hA_det (by norm_num) hA c
  · exact hrep

/-- Nonzero scalar representation by a nonsingular symmetric rational
quaternary form is equivalent to representation over the real and every
p-adic field. -/
theorem exists_quaternary_gramQuadraticValue_eq_iff_real_and_padic
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0) :
    (∃ v : Fin 4 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c) ↔
      (∃ v : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 4 → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p]) := by
  constructor
  · intro hrep
    exact ⟨exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℝ) hrep,
      fun p _ => exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℚ_[p]) hrep⟩
  · rintro ⟨hreal, hpadic⟩
    exact exists_quaternary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det c hc hreal hpadic

private def ternaryPairBadPrimes
    (A B : Matrix (Fin 3) (Fin 3) ℚ) : Finset {p : ℕ // p.Prime} :=
  ((matrixPairBadPrimeSet A B).attach).map
    ⟨fun p => ⟨p.1, by
        exact (Nat.mem_primeFactors.mp
          (show p.1 ∈ (matrixPairBadPrimeSupportNat A B).primeFactors from
            p.2)).1⟩,
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun z : {p : ℕ // p.Prime} => z.1) hpq⟩

private lemma mem_ternaryPairBadPrimes_iff
    (A B : Matrix (Fin 3) (Fin 3) ℚ)
    (p : {p : ℕ // p.Prime}) :
    p ∈ ternaryPairBadPrimes A B ↔ p.1 ∈ matrixPairBadPrimeSet A B := by
  rw [ternaryPairBadPrimes, Finset.mem_map]
  constructor
  · rintro ⟨q, _hq, rfl⟩
    exact q.property
  · intro hp
    refine ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, ?_⟩
    rfl

private lemma ternaryPairCommonRepresents_sq_mul
    {K : Type*} [Field K]
    {A B : Matrix (Fin 3) (Fin 3) K} {c : K}
    (hcommon :
      (∃ u : Fin 3 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = c) ∧
      ∃ v : Fin 3 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = c)
    (s : K) :
    (∃ u : Fin 3 → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue A u = s ^ 2 * c) ∧
    ∃ v : Fin 3 → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue B v = s ^ 2 * c := by
  rcases hcommon with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  refine ⟨⟨s • u, ?_⟩, ⟨s • v, ?_⟩⟩
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hu]
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hv]

private theorem ternaryPairCommonRepresents_rat_of_good_place
    (A B : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (q : ℚ) {p : ℕ} [Fact p.Prime]
    (hpnot : p ∉ matrixPairBadPrimeSet A B) :
    (∃ u : Fin 3 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
      (A.map (algebraMap ℚ ℚ_[p])) u = (q : ℚ_[p])) ∧
    ∃ v : Fin 3 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
      (B.map (algebraMap ℚ ℚ_[p])) v = (q : ℚ_[p]) := by
  obtain ⟨hpodd, hAden, hBden, hAnum, hAdenDet, hBnum, hBdenDet⟩ :=
    matrixPairGoodPrimeData A B hA_det hB_det
      (Fact.out : p.Prime) hpnot
  let Ap := rationalMatrixPadicInt A hAden
  let Bp := rationalMatrixPadicInt B hBden
  have hApMap : Ap.map PadicInt.Coe.ringHom =
      A.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map A hAden
  have hBpMap : Bp.map PadicInt.Coe.ringHom =
      B.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map B hBden
  constructor
  · simpa [hApMap] using
      PositiveDefiniteIntegralLattice.exists_ternary_gramQuadraticValue_eq_padic_of_integral
        hpodd Ap
          (rationalMatrixPadicInt_isSymm A hA_symm hAden)
          (rationalMatrixPadicInt_det_isUnit
            A hA_det hAden hAnum hAdenDet) (q : ℚ_[p])
  · simpa [hBpMap] using
      PositiveDefiniteIntegralLattice.exists_ternary_gramQuadraticValue_eq_padic_of_integral
        hpodd Bp
          (rationalMatrixPadicInt_isSymm B hB_symm hBden)
          (rationalMatrixPadicInt_det_isUnit
            B hB_det hBden hBnum hBdenDet) (q : ℚ_[p])

/-- Fixed nonsingular symmetric rational ternary forms with a common nonzero
represented value at every completion have a common nonzero rational
represented value. -/
theorem exists_ternaryPairCommonRepresents_rat_of_real_and_padic
    (A B : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : ∃ c : ℝ, c ≠ 0 ∧
      (∃ u : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = c) ∧
      ∃ v : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = c)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
      (∃ u : Fin 3 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
      ∃ v : Fin 3 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) v = c) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∃ u : Fin 3 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = q) ∧
      ∃ v : Fin 3 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = q := by
  classical
  let S := ternaryPairBadPrimes A B
  obtain ⟨cReal, hcReal, hcommonReal⟩ := hreal
  obtain ⟨UReal, hURealOpen, hcRealU, hURealSq⟩ :=
    exists_isOpen_mem_subset_real_nonzeroSqOrbit hcReal
  have hpadic' (p : {p : ℕ // p.Prime}) : ∃ c : ℚ_[p.1], c ≠ 0 ∧
      (∃ u : Fin 3 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = c) ∧
      ∃ v : Fin 3 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = c :=
    hpadic p.1
  choose cPadic hcPadic hcommonPadic using hpadic'
  have hopenPadic (p : {p : ℕ // p.Prime}) : ∃ U : Set ℚ_[p.1],
      IsOpen U ∧ cPadic p ∈ U ∧
        U ⊆ {y | ∃ s : ℚ_[p.1], s ≠ 0 ∧ y = s ^ 2 * cPadic p} :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit (hcPadic p)
  choose UPadic hUPadicOpen hcPadicU hUPadicSq using hopenPadic
  obtain ⟨q, hqReal, hqPadic⟩ :=
    exists_rat_mem_real_and_finitely_many_padic_opens S
      (UReal \ {0}) (fun p => UPadic p \ {0})
      (hURealOpen.sdiff isClosed_singleton)
      ⟨cReal, hcRealU, by simpa using hcReal⟩
      (fun p _ => (hUPadicOpen p).sdiff isClosed_singleton)
      (fun p _ => ⟨cPadic p, hcPadicU p, by simpa using hcPadic p⟩)
  have hq : q ≠ 0 := by
    intro hqzero
    apply hqReal.2
    simp [hqzero]
  have hcommonRealQ :
      (∃ u : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = (q : ℝ)) ∧
      ∃ v : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = (q : ℝ) := by
    obtain ⟨s, _hs, hqs⟩ := hURealSq hqReal.1
    rw [hqs]
    exact ternaryPairCommonRepresents_sq_mul hcommonReal s
  have hcommonPadicQ (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      (∃ u : Fin 3 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin 3 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    obtain ⟨s, _hs, hqs⟩ := hUPadicSq p (hqPadic p hp).1
    rw [hqs]
    exact ternaryPairCommonRepresents_sq_mul (hcommonPadic p) s
  have hcommonAll (p : {p : ℕ // p.Prime}) :
      (∃ u : Fin 3 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin 3 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    by_cases hp : p ∈ S
    · exact hcommonPadicQ p hp
    · apply ternaryPairCommonRepresents_rat_of_good_place
        A B hA_symm hA_det hB_symm hB_det q
      exact fun hpbad => hp ((mem_ternaryPairBadPrimes_iff A B p).2 hpbad)
  refine ⟨q, hq, ?_, ?_⟩
  · exact exists_ternary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det q hq hcommonRealQ.1
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).1)
  · exact exists_ternary_gramQuadraticValue_eq_rat_of_real_and_padic
      B hB_symm hB_det q hq hcommonRealQ.2
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).2)

/-- A nonsingular symmetric rational rank-six Gram matrix that is isotropic
over the reals and every p-adic field is isotropic over the rationals. -/
theorem rankSixGramIsotropic_rat_of_real_and_padic
    (M : Matrix (Fin 6) (Fin 6) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    PositiveDefiniteIntegralLattice.GramIsotropic M := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP,
      hcommonReal, hcommonPadic⟩ :=
    exists_ternaryPairDifferenceGramBlock_common_values_of_rankSix_real_and_padic
      M hM_symm hM_det hreal hpadic
  obtain ⟨q, hq, hcommon⟩ :=
    exists_ternaryPairCommonRepresents_rat_of_real_and_padic
      A B hA_symm hA_det hB_symm hB_det hcommonReal hcommonPadic
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.ternaryPairDifferenceGramBlock A B) :=
    (PositiveDefiniteIntegralLattice.gramIsotropic_ternaryPairDifferenceGramBlock_iff_exists_common_value
      A B hA_symm hA_det hB_symm hB_det (by norm_num)).2
      ⟨q, hq, hcommon⟩
  exact PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
    (show (PositiveDefiniteIntegralLattice.ternaryPairDifferenceGramBlock A B).IsCongruent M from
      (show M.IsCongruent
        (PositiveDefiniteIntegralLattice.ternaryPairDifferenceGramBlock A B) from
          ⟨P, hP⟩).symm)
    hblock

/-- Rank-six Hasse--Minkowski for arbitrary nonsingular symmetric rational
Gram matrices. -/
theorem rankSixGramIsotropic_iff_real_and_padic
    (M : Matrix (Fin 6) (Fin 6) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic M ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℝ)) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          PositiveDefiniteIntegralLattice.GramIsotropic
            (M.map (algebraMap ℚ ℚ_[p])) := by
  constructor
  · intro hM
    exact ⟨gramIsotropic_scalarExtension_of_rat (K := ℝ) hM,
      fun p _ => gramIsotropic_scalarExtension_of_rat (K := ℚ_[p]) hM⟩
  · rintro ⟨hreal, hpadic⟩
    exact rankSixGramIsotropic_rat_of_real_and_padic
      M hM_symm hM_det hreal hpadic

/-- A nonzero scalar locally represented by a nonsingular symmetric rational
quinary form is represented over the rationals. -/
theorem exists_quinary_gramQuadraticValue_eq_rat_of_real_and_padic
    (A : Matrix (Fin 5) (Fin 5) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0)
    (hreal : ∃ v : Fin 5 → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 5 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p])) :
    ∃ v : Fin 5 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c := by
  let B : Matrix (Fin 6) (Fin 6) ℚ :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock (-c) A
  have hB_symm : B.IsSymm :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock_isSymm (-c) A hA_symm
  have hB_det : B.det ≠ 0 := by
    simp only [B, PositiveDefiniteIntegralLattice.finSuccGramBlock_det]
    exact mul_ne_zero (neg_ne_zero.mpr hc) hA_det
  have hB_real : PositiveDefiniteIntegralLattice.GramIsotropic
      (B.map (algebraMap ℚ ℝ)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℝ) (A.map (algebraMap ℚ ℝ)) hreal
    simpa [B] using h
  have hB_padic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic (B.map (algebraMap ℚ ℚ_[p])) := by
    intro p hp
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℚ_[p]) (A.map (algebraMap ℚ ℚ_[p])) (hpadic p)
    simpa [B] using h
  have hB : PositiveDefiniteIntegralLattice.GramIsotropic B :=
    rankSixGramIsotropic_rat_of_real_and_padic
      B hB_symm hB_det hB_real hB_padic
  rcases PositiveDefiniteIntegralLattice.gramIsotropic_or_exists_value_of_finSuccGramBlock
      c A hB with hA | hrep
  · exact PositiveDefiniteIntegralLattice.exists_quinary_gramQuadraticValue_eq_of_gramIsotropic
      A hA_symm hA_det (by norm_num) hA c
  · exact hrep

/-- Nonzero scalar representation by a nonsingular symmetric rational
quinary form is equivalent to representation over the real and every p-adic
field. -/
theorem exists_quinary_gramQuadraticValue_eq_iff_real_and_padic
    (A : Matrix (Fin 5) (Fin 5) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0) :
    (∃ v : Fin 5 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c) ↔
      (∃ v : Fin 5 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 5 → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p]) := by
  constructor
  · intro hrep
    exact ⟨exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℝ) hrep,
      fun p _ => exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℚ_[p]) hrep⟩
  · rintro ⟨hreal, hpadic⟩
    exact exists_quinary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det c hc hreal hpadic

private def ternaryQuaternaryBadPrimes
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (B : Matrix (Fin 4) (Fin 4) ℚ) : Finset {p : ℕ // p.Prime} :=
  ((ternaryQuaternaryBadPrimeSet A B).attach).map
    ⟨fun p => ⟨p.1, by
        exact (Nat.mem_primeFactors.mp
          (show p.1 ∈
            (ternaryQuaternaryBadPrimeSupportNat A B).primeFactors from
              p.2)).1⟩,
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun z : {p : ℕ // p.Prime} => z.1) hpq⟩

private lemma mem_ternaryQuaternaryBadPrimes_iff
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (B : Matrix (Fin 4) (Fin 4) ℚ)
    (p : {p : ℕ // p.Prime}) :
    p ∈ ternaryQuaternaryBadPrimes A B ↔
      p.1 ∈ ternaryQuaternaryBadPrimeSet A B := by
  rw [ternaryQuaternaryBadPrimes, Finset.mem_map]
  constructor
  · rintro ⟨q, _hq, rfl⟩
    exact q.property
  · intro hp
    refine ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, ?_⟩
    rfl

private lemma ternaryQuaternaryCommonRepresents_sq_mul
    {K : Type*} [Field K]
    {A : Matrix (Fin 3) (Fin 3) K}
    {B : Matrix (Fin 4) (Fin 4) K} {c : K}
    (hcommon :
      (∃ u : Fin 3 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = c) ∧
      ∃ v : Fin 4 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = c)
    (s : K) :
    (∃ u : Fin 3 → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue A u = s ^ 2 * c) ∧
    ∃ v : Fin 4 → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue B v = s ^ 2 * c := by
  rcases hcommon with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  refine ⟨⟨s • u, ?_⟩, ⟨s • v, ?_⟩⟩
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hu]
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hv]

/-- Fixed nonsingular symmetric rational ternary and quaternary forms with a
common nonzero represented value at every completion have a common nonzero
rational represented value. -/
theorem exists_ternaryQuaternaryCommonRepresents_rat_of_real_and_padic
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (B : Matrix (Fin 4) (Fin 4) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : ∃ c : ℝ, c ≠ 0 ∧
      (∃ u : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = c) ∧
      ∃ v : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = c)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
      (∃ u : Fin 3 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
      ∃ v : Fin 4 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) v = c) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∃ u : Fin 3 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = q) ∧
      ∃ v : Fin 4 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = q := by
  classical
  let S := ternaryQuaternaryBadPrimes A B
  obtain ⟨cReal, hcReal, hcommonReal⟩ := hreal
  obtain ⟨UReal, hURealOpen, hcRealU, hURealSq⟩ :=
    exists_isOpen_mem_subset_real_nonzeroSqOrbit hcReal
  have hpadic' (p : {p : ℕ // p.Prime}) : ∃ c : ℚ_[p.1], c ≠ 0 ∧
      (∃ u : Fin 3 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = c) ∧
      ∃ v : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = c :=
    hpadic p.1
  choose cPadic hcPadic hcommonPadic using hpadic'
  have hopenPadic (p : {p : ℕ // p.Prime}) : ∃ U : Set ℚ_[p.1],
      IsOpen U ∧ cPadic p ∈ U ∧
        U ⊆ {y | ∃ s : ℚ_[p.1], s ≠ 0 ∧ y = s ^ 2 * cPadic p} :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit (hcPadic p)
  choose UPadic hUPadicOpen hcPadicU hUPadicSq using hopenPadic
  obtain ⟨q, hqReal, hqPadic⟩ :=
    exists_rat_mem_real_and_finitely_many_padic_opens S
      (UReal \ {0}) (fun p => UPadic p \ {0})
      (hURealOpen.sdiff isClosed_singleton)
      ⟨cReal, hcRealU, by simpa using hcReal⟩
      (fun p _ => (hUPadicOpen p).sdiff isClosed_singleton)
      (fun p _ => ⟨cPadic p, hcPadicU p, by simpa using hcPadic p⟩)
  have hq : q ≠ 0 := by
    intro hqzero
    apply hqReal.2
    simp [hqzero]
  have hcommonRealQ :
      (∃ u : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = (q : ℝ)) ∧
      ∃ v : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = (q : ℝ) := by
    obtain ⟨s, _hs, hqs⟩ := hURealSq hqReal.1
    rw [hqs]
    exact ternaryQuaternaryCommonRepresents_sq_mul hcommonReal s
  have hcommonPadicQ (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      (∃ u : Fin 3 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    obtain ⟨s, _hs, hqs⟩ := hUPadicSq p (hqPadic p hp).1
    rw [hqs]
    exact ternaryQuaternaryCommonRepresents_sq_mul (hcommonPadic p) s
  have hcommonAll (p : {p : ℕ // p.Prime}) :
      (∃ u : Fin 3 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    by_cases hp : p ∈ S
    · exact hcommonPadicQ p hp
    · apply ternaryQuaternaryCommonRepresents_padic_of_not_mem_badPrimeSet
        A B hA_symm hA_det hB_symm hB_det
      · exact fun hpbad =>
          hp ((mem_ternaryQuaternaryBadPrimes_iff A B p).2 hpbad)
  refine ⟨q, hq, ?_, ?_⟩
  · exact exists_ternary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det q hq hcommonRealQ.1
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).1)
  · exact exists_quaternary_gramQuadraticValue_eq_rat_of_real_and_padic
      B hB_symm hB_det q hq hcommonRealQ.2
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).2)

/-- A nonsingular symmetric rational rank-seven Gram matrix that is isotropic
over the reals and every p-adic field is isotropic over the rationals. -/
theorem rankSevenGramIsotropic_rat_of_real_and_padic
    (M : Matrix (Fin 7) (Fin 7) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    PositiveDefiniteIntegralLattice.GramIsotropic M := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP,
      hcommonReal, hcommonPadic⟩ :=
    exists_ternaryQuaternaryDifferenceGramBlock_common_values_of_rankSeven_real_and_padic
      M hM_symm hM_det hreal hpadic
  obtain ⟨q, hq, hcommon⟩ :=
    exists_ternaryQuaternaryCommonRepresents_rat_of_real_and_padic
      A B hA_symm hA_det hB_symm hB_det hcommonReal hcommonPadic
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.ternaryQuaternaryDifferenceGramBlock A B) :=
    (PositiveDefiniteIntegralLattice.gramIsotropic_ternaryQuaternaryDifferenceGramBlock_iff_exists_common_value
      A B hA_symm hA_det hB_symm hB_det (by norm_num)).2
      ⟨q, hq, hcommon⟩
  exact PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
    (show
      (PositiveDefiniteIntegralLattice.ternaryQuaternaryDifferenceGramBlock A B).IsCongruent M
      from
        (show M.IsCongruent
          (PositiveDefiniteIntegralLattice.ternaryQuaternaryDifferenceGramBlock A B) from
            ⟨P, hP⟩).symm)
    hblock

/-- Rank-seven Hasse--Minkowski for nonsingular symmetric rational Gram
matrices. -/
theorem rankSevenGramIsotropic_iff_real_and_padic
    (M : Matrix (Fin 7) (Fin 7) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic M ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℝ)) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          PositiveDefiniteIntegralLattice.GramIsotropic
            (M.map (algebraMap ℚ ℚ_[p])) := by
  constructor
  · intro hM
    exact
      ⟨gramIsotropic_scalarExtension_of_rat (K := ℝ) hM,
        fun p _ => gramIsotropic_scalarExtension_of_rat (K := ℚ_[p]) hM⟩
  · rintro ⟨hreal, hpadic⟩
    exact rankSevenGramIsotropic_rat_of_real_and_padic
      M hM_symm hM_det hreal hpadic

/-- A nonzero scalar locally represented by a nonsingular symmetric rational
sextenary form is represented over the rationals. -/
theorem exists_sextenary_gramQuadraticValue_eq_rat_of_real_and_padic
    (A : Matrix (Fin 6) (Fin 6) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0)
    (hreal : ∃ v : Fin 6 → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 6 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p])) :
    ∃ v : Fin 6 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c := by
  let B : Matrix (Fin 7) (Fin 7) ℚ :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock (-c) A
  have hB_symm : B.IsSymm :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock_isSymm (-c) A hA_symm
  have hB_det : B.det ≠ 0 := by
    simp only [B, PositiveDefiniteIntegralLattice.finSuccGramBlock_det]
    exact mul_ne_zero (neg_ne_zero.mpr hc) hA_det
  have hB_real : PositiveDefiniteIntegralLattice.GramIsotropic
      (B.map (algebraMap ℚ ℝ)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℝ) (A.map (algebraMap ℚ ℝ)) hreal
    simpa [B] using h
  have hB_padic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic (B.map (algebraMap ℚ ℚ_[p])) := by
    intro p hp
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℚ_[p]) (A.map (algebraMap ℚ ℚ_[p])) (hpadic p)
    simpa [B] using h
  have hB : PositiveDefiniteIntegralLattice.GramIsotropic B :=
    rankSevenGramIsotropic_rat_of_real_and_padic
      B hB_symm hB_det hB_real hB_padic
  rcases PositiveDefiniteIntegralLattice.gramIsotropic_or_exists_value_of_finSuccGramBlock
      c A hB with hA | hrep
  · exact PositiveDefiniteIntegralLattice.exists_sextenary_gramQuadraticValue_eq_of_gramIsotropic
      A hA_symm hA_det (by norm_num) hA c
  · exact hrep

/-- Nonzero scalar representation by a nonsingular symmetric rational
sextenary form is equivalent to representation over the real and every
p-adic field. -/
theorem exists_sextenary_gramQuadraticValue_eq_iff_real_and_padic
    (A : Matrix (Fin 6) (Fin 6) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0) :
    (∃ v : Fin 6 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c) ↔
      (∃ v : Fin 6 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 6 → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p]) := by
  constructor
  · intro hrep
    exact ⟨exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℝ) hrep,
      fun p _ => exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℚ_[p]) hrep⟩
  · rintro ⟨hreal, hpadic⟩
    exact exists_sextenary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det c hc hreal hpadic

private def quaternaryPairBadPrimes
    (A B : Matrix (Fin 4) (Fin 4) ℚ) : Finset {p : ℕ // p.Prime} :=
  ((matrixPairBadPrimeSet A B).attach).map
    ⟨fun p => ⟨p.1, by
        exact (Nat.mem_primeFactors.mp
          (show p.1 ∈ (matrixPairBadPrimeSupportNat A B).primeFactors from
            p.2)).1⟩,
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun z : {p : ℕ // p.Prime} => z.1) hpq⟩

private lemma mem_quaternaryPairBadPrimes_iff
    (A B : Matrix (Fin 4) (Fin 4) ℚ)
    (p : {p : ℕ // p.Prime}) :
    p ∈ quaternaryPairBadPrimes A B ↔
      p.1 ∈ matrixPairBadPrimeSet A B := by
  rw [quaternaryPairBadPrimes, Finset.mem_map]
  constructor
  · rintro ⟨q, _hq, rfl⟩
    exact q.property
  · intro hp
    refine ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, ?_⟩
    rfl

private lemma quaternaryPairCommonRepresents_sq_mul
    {K : Type*} [Field K]
    {A B : Matrix (Fin 4) (Fin 4) K} {c : K}
    (hcommon :
      (∃ u : Fin 4 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = c) ∧
      ∃ v : Fin 4 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = c)
    (s : K) :
    (∃ u : Fin 4 → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue A u = s ^ 2 * c) ∧
    ∃ v : Fin 4 → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue B v = s ^ 2 * c := by
  rcases hcommon with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  refine ⟨⟨s • u, ?_⟩, ⟨s • v, ?_⟩⟩
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hu]
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hv]

private theorem quaternaryPairCommonRepresents_rat_of_good_place
    (A B : Matrix (Fin 4) (Fin 4) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (q : ℚ) {p : ℕ} [Fact p.Prime]
    (hpnot : p ∉ matrixPairBadPrimeSet A B) :
    (∃ u : Fin 4 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
      (A.map (algebraMap ℚ ℚ_[p])) u = (q : ℚ_[p])) ∧
    ∃ v : Fin 4 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
      (B.map (algebraMap ℚ ℚ_[p])) v = (q : ℚ_[p]) := by
  obtain ⟨hpodd, hAden, hBden, hAnum, hAdenDet, hBnum, hBdenDet⟩ :=
    matrixPairGoodPrimeData A B hA_det hB_det
      (Fact.out : p.Prime) hpnot
  let Ap := rationalMatrixPadicInt A hAden
  let Bp := rationalMatrixPadicInt B hBden
  have hApMap : Ap.map PadicInt.Coe.ringHom =
      A.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map A hAden
  have hBpMap : Bp.map PadicInt.Coe.ringHom =
      B.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map B hBden
  constructor
  · simpa [hApMap] using
      PositiveDefiniteIntegralLattice.exists_quaternary_gramQuadraticValue_eq_padic_of_integral
        hpodd Ap
          (rationalMatrixPadicInt_isSymm A hA_symm hAden)
          (rationalMatrixPadicInt_det_isUnit
            A hA_det hAden hAnum hAdenDet) (q : ℚ_[p])
  · simpa [hBpMap] using
      PositiveDefiniteIntegralLattice.exists_quaternary_gramQuadraticValue_eq_padic_of_integral
        hpodd Bp
          (rationalMatrixPadicInt_isSymm B hB_symm hBden)
          (rationalMatrixPadicInt_det_isUnit
            B hB_det hBden hBnum hBdenDet) (q : ℚ_[p])

/-- Fixed nonsingular symmetric rational quaternary forms with a common
nonzero represented value at every completion have a common nonzero rational
represented value. -/
theorem exists_quaternaryPairCommonRepresents_rat_of_real_and_padic
    (A B : Matrix (Fin 4) (Fin 4) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : ∃ c : ℝ, c ≠ 0 ∧
      (∃ u : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = c) ∧
      ∃ v : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = c)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
      (∃ u : Fin 4 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
      ∃ v : Fin 4 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) v = c) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∃ u : Fin 4 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = q) ∧
      ∃ v : Fin 4 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = q := by
  classical
  let S := quaternaryPairBadPrimes A B
  obtain ⟨cReal, hcReal, hcommonReal⟩ := hreal
  obtain ⟨UReal, hURealOpen, hcRealU, hURealSq⟩ :=
    exists_isOpen_mem_subset_real_nonzeroSqOrbit hcReal
  have hpadic' (p : {p : ℕ // p.Prime}) : ∃ c : ℚ_[p.1], c ≠ 0 ∧
      (∃ u : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = c) ∧
      ∃ v : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = c :=
    hpadic p.1
  choose cPadic hcPadic hcommonPadic using hpadic'
  have hopenPadic (p : {p : ℕ // p.Prime}) : ∃ U : Set ℚ_[p.1],
      IsOpen U ∧ cPadic p ∈ U ∧
        U ⊆ {y | ∃ s : ℚ_[p.1], s ≠ 0 ∧ y = s ^ 2 * cPadic p} :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit (hcPadic p)
  choose UPadic hUPadicOpen hcPadicU hUPadicSq using hopenPadic
  obtain ⟨q, hqReal, hqPadic⟩ :=
    exists_rat_mem_real_and_finitely_many_padic_opens S
      (UReal \ {0}) (fun p => UPadic p \ {0})
      (hURealOpen.sdiff isClosed_singleton)
      ⟨cReal, hcRealU, by simpa using hcReal⟩
      (fun p _ => (hUPadicOpen p).sdiff isClosed_singleton)
      (fun p _ => ⟨cPadic p, hcPadicU p, by simpa using hcPadic p⟩)
  have hq : q ≠ 0 := by
    intro hqzero
    apply hqReal.2
    simp [hqzero]
  have hcommonRealQ :
      (∃ u : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = (q : ℝ)) ∧
      ∃ v : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = (q : ℝ) := by
    obtain ⟨s, _hs, hqs⟩ := hURealSq hqReal.1
    rw [hqs]
    exact quaternaryPairCommonRepresents_sq_mul hcommonReal s
  have hcommonPadicQ (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      (∃ u : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    obtain ⟨s, _hs, hqs⟩ := hUPadicSq p (hqPadic p hp).1
    rw [hqs]
    exact quaternaryPairCommonRepresents_sq_mul (hcommonPadic p) s
  have hcommonAll (p : {p : ℕ // p.Prime}) :
      (∃ u : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    by_cases hp : p ∈ S
    · exact hcommonPadicQ p hp
    · apply quaternaryPairCommonRepresents_rat_of_good_place
        A B hA_symm hA_det hB_symm hB_det q
      exact fun hpbad => hp ((mem_quaternaryPairBadPrimes_iff A B p).2 hpbad)
  refine ⟨q, hq, ?_, ?_⟩
  · exact exists_quaternary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det q hq hcommonRealQ.1
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).1)
  · exact exists_quaternary_gramQuadraticValue_eq_rat_of_real_and_padic
      B hB_symm hB_det q hq hcommonRealQ.2
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).2)

/-- A nonsingular symmetric rational rank-eight Gram matrix that is isotropic
over the reals and every p-adic field is isotropic over the rationals. -/
theorem rankEightGramIsotropic_rat_of_real_and_padic
    (M : Matrix (Fin 8) (Fin 8) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    PositiveDefiniteIntegralLattice.GramIsotropic M := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP,
      hcommonReal, hcommonPadic⟩ :=
    exists_quaternaryPairDifferenceGramBlock_common_values_of_rankEight_real_and_padic
      M hM_symm hM_det hreal hpadic
  obtain ⟨q, hq, hcommon⟩ :=
    exists_quaternaryPairCommonRepresents_rat_of_real_and_padic
      A B hA_symm hA_det hB_symm hB_det hcommonReal hcommonPadic
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.quaternaryPairDifferenceGramBlock A B) :=
    (PositiveDefiniteIntegralLattice.gramIsotropic_quaternaryPairDifferenceGramBlock_iff_exists_common_value
      A B hA_symm hA_det hB_symm hB_det (by norm_num)).2
      ⟨q, hq, hcommon⟩
  exact PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
    (show
      (PositiveDefiniteIntegralLattice.quaternaryPairDifferenceGramBlock A B).IsCongruent M
      from
        (show M.IsCongruent
          (PositiveDefiniteIntegralLattice.quaternaryPairDifferenceGramBlock A B) from
            ⟨P, hP⟩).symm)
    hblock

/-- Rank-eight Hasse--Minkowski for nonsingular symmetric rational Gram
matrices. -/
theorem rankEightGramIsotropic_iff_real_and_padic
    (M : Matrix (Fin 8) (Fin 8) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic M ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℝ)) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          PositiveDefiniteIntegralLattice.GramIsotropic
            (M.map (algebraMap ℚ ℚ_[p])) := by
  constructor
  · intro hM
    exact
      ⟨gramIsotropic_scalarExtension_of_rat (K := ℝ) hM,
        fun p _ => gramIsotropic_scalarExtension_of_rat (K := ℚ_[p]) hM⟩
  · rintro ⟨hreal, hpadic⟩
    exact rankEightGramIsotropic_rat_of_real_and_padic
      M hM_symm hM_det hreal hpadic

/-- A nonzero scalar locally represented by a nonsingular symmetric rational
septenary form is represented over the rationals. -/
theorem exists_septenary_gramQuadraticValue_eq_rat_of_real_and_padic
    (A : Matrix (Fin 7) (Fin 7) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0)
    (hreal : ∃ v : Fin 7 → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 7 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p])) :
    ∃ v : Fin 7 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c := by
  let B : Matrix (Fin 8) (Fin 8) ℚ :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock (-c) A
  have hB_symm : B.IsSymm :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock_isSymm (-c) A hA_symm
  have hB_det : B.det ≠ 0 := by
    simp only [B, PositiveDefiniteIntegralLattice.finSuccGramBlock_det]
    exact mul_ne_zero (neg_ne_zero.mpr hc) hA_det
  have hB_real : PositiveDefiniteIntegralLattice.GramIsotropic
      (B.map (algebraMap ℚ ℝ)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℝ) (A.map (algebraMap ℚ ℝ)) hreal
    simpa [B] using h
  have hB_padic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic (B.map (algebraMap ℚ ℚ_[p])) := by
    intro p hp
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℚ_[p]) (A.map (algebraMap ℚ ℚ_[p])) (hpadic p)
    simpa [B] using h
  have hB : PositiveDefiniteIntegralLattice.GramIsotropic B :=
    rankEightGramIsotropic_rat_of_real_and_padic
      B hB_symm hB_det hB_real hB_padic
  rcases PositiveDefiniteIntegralLattice.gramIsotropic_or_exists_value_of_finSuccGramBlock
      c A hB with hA | hrep
  · exact PositiveDefiniteIntegralLattice.exists_septenary_gramQuadraticValue_eq_of_gramIsotropic
      A hA_symm hA_det (by norm_num) hA c
  · exact hrep

/-- Nonzero scalar representation by a nonsingular symmetric rational
septenary form is equivalent to representation over the real and every
p-adic field. -/
theorem exists_septenary_gramQuadraticValue_eq_iff_real_and_padic
    (A : Matrix (Fin 7) (Fin 7) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0) :
    (∃ v : Fin 7 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c) ↔
      (∃ v : Fin 7 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 7 → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p]) := by
  constructor
  · intro hrep
    exact ⟨exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℝ) hrep,
      fun p _ => exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℚ_[p]) hrep⟩
  · rintro ⟨hreal, hpadic⟩
    exact exists_septenary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det c hc hreal hpadic

private def quaternaryQuinaryBadPrimes
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (B : Matrix (Fin 5) (Fin 5) ℚ) : Finset {p : ℕ // p.Prime} :=
  ((quaternaryQuinaryBadPrimeSet A B).attach).map
    ⟨fun p => ⟨p.1, by
        exact (Nat.mem_primeFactors.mp
          (show p.1 ∈
            (quaternaryQuinaryBadPrimeSupportNat A B).primeFactors from
              p.2)).1⟩,
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun z : {p : ℕ // p.Prime} => z.1) hpq⟩

private lemma mem_quaternaryQuinaryBadPrimes_iff
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (B : Matrix (Fin 5) (Fin 5) ℚ)
    (p : {p : ℕ // p.Prime}) :
    p ∈ quaternaryQuinaryBadPrimes A B ↔
      p.1 ∈ quaternaryQuinaryBadPrimeSet A B := by
  rw [quaternaryQuinaryBadPrimes, Finset.mem_map]
  constructor
  · rintro ⟨q, _hq, rfl⟩
    exact q.property
  · intro hp
    refine ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, ?_⟩
    rfl

private lemma quaternaryQuinaryCommonRepresents_sq_mul
    {K : Type*} [Field K]
    {A : Matrix (Fin 4) (Fin 4) K}
    {B : Matrix (Fin 5) (Fin 5) K} {c : K}
    (hcommon :
      (∃ u : Fin 4 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = c) ∧
      ∃ v : Fin 5 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = c)
    (s : K) :
    (∃ u : Fin 4 → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue A u = s ^ 2 * c) ∧
    ∃ v : Fin 5 → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue B v = s ^ 2 * c := by
  rcases hcommon with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  refine ⟨⟨s • u, ?_⟩, ⟨s • v, ?_⟩⟩
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hu]
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hv]

/-- Fixed nonsingular symmetric rational quaternary and quinary forms with a
common nonzero represented value at every completion have a common nonzero
rational represented value. -/
theorem exists_quaternaryQuinaryCommonRepresents_rat_of_real_and_padic
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (B : Matrix (Fin 5) (Fin 5) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : ∃ c : ℝ, c ≠ 0 ∧
      (∃ u : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = c) ∧
      ∃ v : Fin 5 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = c)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
      (∃ u : Fin 4 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
      ∃ v : Fin 5 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) v = c) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∃ u : Fin 4 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = q) ∧
      ∃ v : Fin 5 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = q := by
  classical
  let S := quaternaryQuinaryBadPrimes A B
  obtain ⟨cReal, hcReal, hcommonReal⟩ := hreal
  obtain ⟨UReal, hURealOpen, hcRealU, hURealSq⟩ :=
    exists_isOpen_mem_subset_real_nonzeroSqOrbit hcReal
  have hpadic' (p : {p : ℕ // p.Prime}) : ∃ c : ℚ_[p.1], c ≠ 0 ∧
      (∃ u : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = c) ∧
      ∃ v : Fin 5 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = c :=
    hpadic p.1
  choose cPadic hcPadic hcommonPadic using hpadic'
  have hopenPadic (p : {p : ℕ // p.Prime}) : ∃ U : Set ℚ_[p.1],
      IsOpen U ∧ cPadic p ∈ U ∧
        U ⊆ {y | ∃ s : ℚ_[p.1], s ≠ 0 ∧ y = s ^ 2 * cPadic p} :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit (hcPadic p)
  choose UPadic hUPadicOpen hcPadicU hUPadicSq using hopenPadic
  obtain ⟨q, hqReal, hqPadic⟩ :=
    exists_rat_mem_real_and_finitely_many_padic_opens S
      (UReal \ {0}) (fun p => UPadic p \ {0})
      (hURealOpen.sdiff isClosed_singleton)
      ⟨cReal, hcRealU, by simpa using hcReal⟩
      (fun p _ => (hUPadicOpen p).sdiff isClosed_singleton)
      (fun p _ => ⟨cPadic p, hcPadicU p, by simpa using hcPadic p⟩)
  have hq : q ≠ 0 := by
    intro hqzero
    apply hqReal.2
    simp [hqzero]
  have hcommonRealQ :
      (∃ u : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = (q : ℝ)) ∧
      ∃ v : Fin 5 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = (q : ℝ) := by
    obtain ⟨s, _hs, hqs⟩ := hURealSq hqReal.1
    rw [hqs]
    exact quaternaryQuinaryCommonRepresents_sq_mul hcommonReal s
  have hcommonPadicQ (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      (∃ u : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin 5 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    obtain ⟨s, _hs, hqs⟩ := hUPadicSq p (hqPadic p hp).1
    rw [hqs]
    exact quaternaryQuinaryCommonRepresents_sq_mul (hcommonPadic p) s
  have hcommonAll (p : {p : ℕ // p.Prime}) :
      (∃ u : Fin 4 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin 5 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    by_cases hp : p ∈ S
    · exact hcommonPadicQ p hp
    · apply quaternaryQuinaryCommonRepresents_padic_of_not_mem_badPrimeSet
        A B hA_symm hA_det hB_symm hB_det
      exact fun hpbad =>
        hp ((mem_quaternaryQuinaryBadPrimes_iff A B p).2 hpbad)
  refine ⟨q, hq, ?_, ?_⟩
  · exact exists_quaternary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det q hq hcommonRealQ.1
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).1)
  · exact exists_quinary_gramQuadraticValue_eq_rat_of_real_and_padic
      B hB_symm hB_det q hq hcommonRealQ.2
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).2)

/-- A nonsingular symmetric rational rank-nine Gram matrix that is isotropic
over the reals and every p-adic field is isotropic over the rationals. -/
theorem rankNineGramIsotropic_rat_of_real_and_padic
    (M : Matrix (Fin 9) (Fin 9) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    PositiveDefiniteIntegralLattice.GramIsotropic M := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP,
      hcommonReal, hcommonPadic⟩ :=
    exists_quaternaryQuinaryDifferenceGramBlock_common_values_of_rankNine_real_and_padic
      M hM_symm hM_det hreal hpadic
  obtain ⟨q, hq, hcommon⟩ :=
    exists_quaternaryQuinaryCommonRepresents_rat_of_real_and_padic
      A B hA_symm hA_det hB_symm hB_det hcommonReal hcommonPadic
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.quaternaryQuinaryDifferenceGramBlock A B) :=
    (PositiveDefiniteIntegralLattice.gramIsotropic_quaternaryQuinaryDifferenceGramBlock_iff_exists_common_value
      A B hA_symm hA_det hB_symm hB_det (by norm_num)).2
      ⟨q, hq, hcommon⟩
  exact PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
    (show
      (PositiveDefiniteIntegralLattice.quaternaryQuinaryDifferenceGramBlock A B).IsCongruent M
      from
        (show M.IsCongruent
          (PositiveDefiniteIntegralLattice.quaternaryQuinaryDifferenceGramBlock A B) from
            ⟨P, hP⟩).symm)
    hblock

/-- Rank-nine Hasse--Minkowski for nonsingular symmetric rational Gram
matrices. -/
theorem rankNineGramIsotropic_iff_real_and_padic
    (M : Matrix (Fin 9) (Fin 9) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic M ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℝ)) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          PositiveDefiniteIntegralLattice.GramIsotropic
            (M.map (algebraMap ℚ ℚ_[p])) := by
  constructor
  · intro hM
    exact
      ⟨gramIsotropic_scalarExtension_of_rat (K := ℝ) hM,
        fun p _ => gramIsotropic_scalarExtension_of_rat (K := ℚ_[p]) hM⟩
  · rintro ⟨hreal, hpadic⟩
    exact rankNineGramIsotropic_rat_of_real_and_padic
      M hM_symm hM_det hreal hpadic

/-- A nonzero scalar locally represented by a nonsingular symmetric rational
octonary form is represented over the rationals. -/
theorem exists_octonary_gramQuadraticValue_eq_rat_of_real_and_padic
    (A : Matrix (Fin 8) (Fin 8) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0)
    (hreal : ∃ v : Fin 8 → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 8 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p])) :
    ∃ v : Fin 8 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c := by
  let B : Matrix (Fin 9) (Fin 9) ℚ :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock (-c) A
  have hB_symm : B.IsSymm :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock_isSymm (-c) A hA_symm
  have hB_det : B.det ≠ 0 := by
    simp only [B, PositiveDefiniteIntegralLattice.finSuccGramBlock_det]
    exact mul_ne_zero (neg_ne_zero.mpr hc) hA_det
  have hB_real : PositiveDefiniteIntegralLattice.GramIsotropic
      (B.map (algebraMap ℚ ℝ)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℝ) (A.map (algebraMap ℚ ℝ)) hreal
    simpa [B] using h
  have hB_padic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic (B.map (algebraMap ℚ ℚ_[p])) := by
    intro p hp
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℚ_[p]) (A.map (algebraMap ℚ ℚ_[p])) (hpadic p)
    simpa [B] using h
  have hB : PositiveDefiniteIntegralLattice.GramIsotropic B :=
    rankNineGramIsotropic_rat_of_real_and_padic
      B hB_symm hB_det hB_real hB_padic
  rcases PositiveDefiniteIntegralLattice.gramIsotropic_or_exists_value_of_finSuccGramBlock
      c A hB with hA | hrep
  · exact PositiveDefiniteIntegralLattice.exists_octonary_gramQuadraticValue_eq_of_gramIsotropic
      A hA_symm hA_det (by norm_num) hA c
  · exact hrep

/-- Nonzero scalar representation by a nonsingular symmetric rational
octonary form is equivalent to representation over the real and every p-adic
field. -/
theorem exists_octonary_gramQuadraticValue_eq_iff_real_and_padic
    (A : Matrix (Fin 8) (Fin 8) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0) :
    (∃ v : Fin 8 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c) ↔
      (∃ v : Fin 8 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 8 → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p]) := by
  constructor
  · intro hrep
    exact ⟨exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℝ) hrep,
      fun p _ => exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℚ_[p]) hrep⟩
  · rintro ⟨hreal, hpadic⟩
    exact exists_octonary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det c hc hreal hpadic

private def quinaryPairBadPrimes
    (A B : Matrix (Fin 5) (Fin 5) ℚ) : Finset {p : ℕ // p.Prime} :=
  ((matrixPairBadPrimeSet A B).attach).map
    ⟨fun p => ⟨p.1, by
        exact (Nat.mem_primeFactors.mp
          (show p.1 ∈ (matrixPairBadPrimeSupportNat A B).primeFactors from
            p.2)).1⟩,
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun z : {p : ℕ // p.Prime} => z.1) hpq⟩

private lemma mem_quinaryPairBadPrimes_iff
    (A B : Matrix (Fin 5) (Fin 5) ℚ)
    (p : {p : ℕ // p.Prime}) :
    p ∈ quinaryPairBadPrimes A B ↔
      p.1 ∈ matrixPairBadPrimeSet A B := by
  rw [quinaryPairBadPrimes, Finset.mem_map]
  constructor
  · rintro ⟨q, _hq, rfl⟩
    exact q.property
  · intro hp
    refine ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, ?_⟩
    rfl

private lemma quinaryPairCommonRepresents_sq_mul
    {K : Type*} [Field K]
    {A B : Matrix (Fin 5) (Fin 5) K} {c : K}
    (hcommon :
      (∃ u : Fin 5 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = c) ∧
      ∃ v : Fin 5 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = c)
    (s : K) :
    (∃ u : Fin 5 → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue A u = s ^ 2 * c) ∧
    ∃ v : Fin 5 → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue B v = s ^ 2 * c := by
  rcases hcommon with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  refine ⟨⟨s • u, ?_⟩, ⟨s • v, ?_⟩⟩
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hu]
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hv]

private theorem quinaryPairCommonRepresents_rat_of_good_place
    (A B : Matrix (Fin 5) (Fin 5) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (q : ℚ) {p : ℕ} [Fact p.Prime]
    (hpnot : p ∉ matrixPairBadPrimeSet A B) :
    (∃ u : Fin 5 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
      (A.map (algebraMap ℚ ℚ_[p])) u = (q : ℚ_[p])) ∧
    ∃ v : Fin 5 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
      (B.map (algebraMap ℚ ℚ_[p])) v = (q : ℚ_[p]) := by
  obtain ⟨hpodd, hAden, hBden, hAnum, hAdenDet, hBnum, hBdenDet⟩ :=
    matrixPairGoodPrimeData A B hA_det hB_det
      (Fact.out : p.Prime) hpnot
  let Ap := rationalMatrixPadicInt A hAden
  let Bp := rationalMatrixPadicInt B hBden
  have hApMap : Ap.map PadicInt.Coe.ringHom =
      A.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map A hAden
  have hBpMap : Bp.map PadicInt.Coe.ringHom =
      B.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map B hBden
  constructor
  · simpa [hApMap] using
      PositiveDefiniteIntegralLattice.exists_quinary_gramQuadraticValue_eq_padic_of_integral
        hpodd Ap
          (rationalMatrixPadicInt_isSymm A hA_symm hAden)
          (rationalMatrixPadicInt_det_isUnit
            A hA_det hAden hAnum hAdenDet) (q : ℚ_[p])
  · simpa [hBpMap] using
      PositiveDefiniteIntegralLattice.exists_quinary_gramQuadraticValue_eq_padic_of_integral
        hpodd Bp
          (rationalMatrixPadicInt_isSymm B hB_symm hBden)
          (rationalMatrixPadicInt_det_isUnit
            B hB_det hBden hBnum hBdenDet) (q : ℚ_[p])

/-- Fixed nonsingular symmetric rational quinary forms with a common nonzero
represented value at every completion have a common nonzero rational
represented value. -/
theorem exists_quinaryPairCommonRepresents_rat_of_real_and_padic
    (A B : Matrix (Fin 5) (Fin 5) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : ∃ c : ℝ, c ≠ 0 ∧
      (∃ u : Fin 5 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = c) ∧
      ∃ v : Fin 5 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = c)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
      (∃ u : Fin 5 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
      ∃ v : Fin 5 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) v = c) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∃ u : Fin 5 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = q) ∧
      ∃ v : Fin 5 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = q := by
  classical
  let S := quinaryPairBadPrimes A B
  obtain ⟨cReal, hcReal, hcommonReal⟩ := hreal
  obtain ⟨UReal, hURealOpen, hcRealU, hURealSq⟩ :=
    exists_isOpen_mem_subset_real_nonzeroSqOrbit hcReal
  have hpadic' (p : {p : ℕ // p.Prime}) : ∃ c : ℚ_[p.1], c ≠ 0 ∧
      (∃ u : Fin 5 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = c) ∧
      ∃ v : Fin 5 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = c :=
    hpadic p.1
  choose cPadic hcPadic hcommonPadic using hpadic'
  have hopenPadic (p : {p : ℕ // p.Prime}) : ∃ U : Set ℚ_[p.1],
      IsOpen U ∧ cPadic p ∈ U ∧
        U ⊆ {y | ∃ s : ℚ_[p.1], s ≠ 0 ∧ y = s ^ 2 * cPadic p} :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit (hcPadic p)
  choose UPadic hUPadicOpen hcPadicU hUPadicSq using hopenPadic
  obtain ⟨q, hqReal, hqPadic⟩ :=
    exists_rat_mem_real_and_finitely_many_padic_opens S
      (UReal \ {0}) (fun p => UPadic p \ {0})
      (hURealOpen.sdiff isClosed_singleton)
      ⟨cReal, hcRealU, by simpa using hcReal⟩
      (fun p _ => (hUPadicOpen p).sdiff isClosed_singleton)
      (fun p _ => ⟨cPadic p, hcPadicU p, by simpa using hcPadic p⟩)
  have hq : q ≠ 0 := by
    intro hqzero
    apply hqReal.2
    simp [hqzero]
  have hcommonRealQ :
      (∃ u : Fin 5 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = (q : ℝ)) ∧
      ∃ v : Fin 5 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = (q : ℝ) := by
    obtain ⟨s, _hs, hqs⟩ := hURealSq hqReal.1
    rw [hqs]
    exact quinaryPairCommonRepresents_sq_mul hcommonReal s
  have hcommonPadicQ (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      (∃ u : Fin 5 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin 5 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    obtain ⟨s, _hs, hqs⟩ := hUPadicSq p (hqPadic p hp).1
    rw [hqs]
    exact quinaryPairCommonRepresents_sq_mul (hcommonPadic p) s
  have hcommonAll (p : {p : ℕ // p.Prime}) :
      (∃ u : Fin 5 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin 5 → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    by_cases hp : p ∈ S
    · exact hcommonPadicQ p hp
    · apply quinaryPairCommonRepresents_rat_of_good_place
        A B hA_symm hA_det hB_symm hB_det q
      exact fun hpbad => hp ((mem_quinaryPairBadPrimes_iff A B p).2 hpbad)
  refine ⟨q, hq, ?_, ?_⟩
  · exact exists_quinary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det q hq hcommonRealQ.1
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).1)
  · exact exists_quinary_gramQuadraticValue_eq_rat_of_real_and_padic
      B hB_symm hB_det q hq hcommonRealQ.2
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).2)

/-- A nonsingular symmetric rational rank-ten Gram matrix that is isotropic
over the reals and every p-adic field is isotropic over the rationals. -/
theorem rankTenGramIsotropic_rat_of_real_and_padic
    (M : Matrix (Fin 10) (Fin 10) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    PositiveDefiniteIntegralLattice.GramIsotropic M := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP,
      hcommonReal, hcommonPadic⟩ :=
    exists_quinaryPairDifferenceGramBlock_common_values_of_rankTen_real_and_padic
      M hM_symm hM_det hreal hpadic
  obtain ⟨q, hq, hcommon⟩ :=
    exists_quinaryPairCommonRepresents_rat_of_real_and_padic
      A B hA_symm hA_det hB_symm hB_det hcommonReal hcommonPadic
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.quinaryPairDifferenceGramBlock A B) :=
    (PositiveDefiniteIntegralLattice.gramIsotropic_quinaryPairDifferenceGramBlock_iff_exists_common_value
      A B hA_symm hA_det hB_symm hB_det (by norm_num)).2
      ⟨q, hq, hcommon⟩
  exact PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
    (show
      (PositiveDefiniteIntegralLattice.quinaryPairDifferenceGramBlock A B).IsCongruent M
      from
        (show M.IsCongruent
          (PositiveDefiniteIntegralLattice.quinaryPairDifferenceGramBlock A B) from
            ⟨P, hP⟩).symm)
    hblock

/-- Rank-ten Hasse--Minkowski for nonsingular symmetric rational Gram
matrices. -/
theorem rankTenGramIsotropic_iff_real_and_padic
    (M : Matrix (Fin 10) (Fin 10) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic M ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℝ)) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          PositiveDefiniteIntegralLattice.GramIsotropic
            (M.map (algebraMap ℚ ℚ_[p])) := by
  constructor
  · intro hM
    exact
      ⟨gramIsotropic_scalarExtension_of_rat (K := ℝ) hM,
        fun p _ => gramIsotropic_scalarExtension_of_rat (K := ℚ_[p]) hM⟩
  · rintro ⟨hreal, hpadic⟩
    exact rankTenGramIsotropic_rat_of_real_and_padic
      M hM_symm hM_det hreal hpadic

/-- A nonzero scalar locally represented by a nonsingular symmetric rational
nonary form is represented over the rationals. -/
theorem exists_nonary_gramQuadraticValue_eq_rat_of_real_and_padic
    (A : Matrix (Fin 9) (Fin 9) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0)
    (hreal : ∃ v : Fin 9 → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 9 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p])) :
    ∃ v : Fin 9 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c := by
  let B : Matrix (Fin 10) (Fin 10) ℚ :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock (-c) A
  have hB_symm : B.IsSymm :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock_isSymm (-c) A hA_symm
  have hB_det : B.det ≠ 0 := by
    simp only [B, PositiveDefiniteIntegralLattice.finSuccGramBlock_det]
    exact mul_ne_zero (neg_ne_zero.mpr hc) hA_det
  have hB_real : PositiveDefiniteIntegralLattice.GramIsotropic
      (B.map (algebraMap ℚ ℝ)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℝ) (A.map (algebraMap ℚ ℝ)) hreal
    simpa [B] using h
  have hB_padic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic (B.map (algebraMap ℚ ℚ_[p])) := by
    intro p hp
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℚ_[p]) (A.map (algebraMap ℚ ℚ_[p])) (hpadic p)
    simpa [B] using h
  have hB : PositiveDefiniteIntegralLattice.GramIsotropic B :=
    rankTenGramIsotropic_rat_of_real_and_padic
      B hB_symm hB_det hB_real hB_padic
  rcases PositiveDefiniteIntegralLattice.gramIsotropic_or_exists_value_of_finSuccGramBlock
      c A hB with hA | hrep
  · exact PositiveDefiniteIntegralLattice.exists_nonary_gramQuadraticValue_eq_of_gramIsotropic
      A hA_symm hA_det (by norm_num) hA c
  · exact hrep

/-- Nonzero scalar representation by a nonsingular symmetric rational
nonary form is equivalent to representation over the real and every p-adic
field. -/
theorem exists_nonary_gramQuadraticValue_eq_iff_real_and_padic
    (A : Matrix (Fin 9) (Fin 9) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0) :
    (∃ v : Fin 9 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c) ↔
      (∃ v : Fin 9 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 9 → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p]) := by
  constructor
  · intro hrep
    exact ⟨exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℝ) hrep,
      fun p _ => exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℚ_[p]) hrep⟩
  · rintro ⟨hreal, hpadic⟩
    exact exists_nonary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det c hc hreal hpadic

private def matrixPairBadPrimes {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) : Finset {p : ℕ // p.Prime} :=
  ((matrixPairBadPrimeSet A B).attach).map
    ⟨fun p => ⟨p.1, by
        exact (Nat.mem_primeFactors.mp
          (show p.1 ∈ (matrixPairBadPrimeSupportNat A B).primeFactors from
            p.2)).1⟩,
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun z : {p : ℕ // p.Prime} => z.1) hpq⟩

private lemma mem_matrixPairBadPrimes_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (p : {p : ℕ // p.Prime}) :
    p ∈ matrixPairBadPrimes A B ↔
      p.1 ∈ matrixPairBadPrimeSet A B := by
  rw [matrixPairBadPrimes, Finset.mem_map]
  constructor
  · rintro ⟨q, _hq, rfl⟩
    exact q.property
  · intro hp
    refine ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, ?_⟩
    rfl

private lemma matrixPairCommonRepresents_sq_mul
    {K : Type*} [Field K] {m n : ℕ}
    {A : Matrix (Fin m) (Fin m) K}
    {B : Matrix (Fin n) (Fin n) K} {c : K}
    (hcommon :
      (∃ u : Fin m → K, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = c) ∧
      ∃ v : Fin n → K, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = c)
    (s : K) :
    (∃ u : Fin m → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue A u = s ^ 2 * c) ∧
    ∃ v : Fin n → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue B v = s ^ 2 * c := by
  rcases hcommon with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  refine ⟨⟨s • u, ?_⟩, ⟨s • v, ?_⟩⟩
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hu]
  · rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_vector, hv]

/-- Fixed nonsingular symmetric rational forms of dimensions at least three
with a common nonzero represented value at every completion have a common
nonzero rational represented value, assuming nonzero representation
local-global for each form. -/
theorem exists_matrixPairCommonRepresents_rat_of_real_and_padic
    {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : ∃ c : ℝ, c ≠ 0 ∧
      (∃ u : Fin m → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = c) ∧
      ∃ v : Fin n → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = c)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
      (∃ u : Fin m → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
      ∃ v : Fin n → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) v = c)
    (hA_local_global : ∀ (q : ℚ), q ≠ 0 →
      (∃ u : Fin m → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = (q : ℝ)) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ u : Fin m → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) u = (q : ℚ_[p])) →
      ∃ u : Fin m → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = q)
    (hB_local_global : ∀ (q : ℚ), q ≠ 0 →
      (∃ v : Fin n → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = (q : ℝ)) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin n → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℚ_[p])) v = (q : ℚ_[p])) →
      ∃ v : Fin n → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = q) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∃ u : Fin m → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = q) ∧
      ∃ v : Fin n → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = q := by
  classical
  let S := matrixPairBadPrimes A B
  obtain ⟨cReal, hcReal, hcommonReal⟩ := hreal
  obtain ⟨UReal, hURealOpen, hcRealU, hURealSq⟩ :=
    exists_isOpen_mem_subset_real_nonzeroSqOrbit hcReal
  have hpadic' (p : {p : ℕ // p.Prime}) : ∃ c : ℚ_[p.1], c ≠ 0 ∧
      (∃ u : Fin m → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = c) ∧
      ∃ v : Fin n → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = c :=
    hpadic p.1
  choose cPadic hcPadic hcommonPadic using hpadic'
  have hopenPadic (p : {p : ℕ // p.Prime}) : ∃ U : Set ℚ_[p.1],
      IsOpen U ∧ cPadic p ∈ U ∧
        U ⊆ {y | ∃ s : ℚ_[p.1], s ≠ 0 ∧ y = s ^ 2 * cPadic p} :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit (hcPadic p)
  choose UPadic hUPadicOpen hcPadicU hUPadicSq using hopenPadic
  obtain ⟨q, hqReal, hqPadic⟩ :=
    exists_rat_mem_real_and_finitely_many_padic_opens S
      (UReal \ {0}) (fun p => UPadic p \ {0})
      (hURealOpen.sdiff isClosed_singleton)
      ⟨cReal, hcRealU, by simpa using hcReal⟩
      (fun p _ => (hUPadicOpen p).sdiff isClosed_singleton)
      (fun p _ => ⟨cPadic p, hcPadicU p, by simpa using hcPadic p⟩)
  have hq : q ≠ 0 := by
    intro hqzero
    apply hqReal.2
    simp [hqzero]
  have hcommonRealQ :
      (∃ u : Fin m → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) u = (q : ℝ)) ∧
      ∃ v : Fin n → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) v = (q : ℝ) := by
    obtain ⟨s, _hs, hqs⟩ := hURealSq hqReal.1
    rw [hqs]
    exact matrixPairCommonRepresents_sq_mul hcommonReal s
  have hcommonPadicQ (p : {p : ℕ // p.Prime}) (hp : p ∈ S) :
      (∃ u : Fin m → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin n → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    obtain ⟨s, _hs, hqs⟩ := hUPadicSq p (hqPadic p hp).1
    rw [hqs]
    exact matrixPairCommonRepresents_sq_mul (hcommonPadic p) s
  have hcommonAll (p : {p : ℕ // p.Prime}) :
      (∃ u : Fin m → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p.1])) u = (q : ℚ_[p.1])) ∧
      ∃ v : Fin n → ℚ_[p.1], PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1]) := by
    by_cases hp : p ∈ S
    · exact hcommonPadicQ p hp
    · apply matrixPairCommonRepresents_padic_of_not_mem_badPrimeSet
        hm hn A B hA_symm hA_det hB_symm hB_det
      exact fun hpbad => hp ((mem_matrixPairBadPrimes_iff A B p).2 hpbad)
  refine ⟨q, hq, ?_, ?_⟩
  · exact hA_local_global q hq hcommonRealQ.1
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).1)
  · exact hB_local_global q hq hcommonRealQ.2
      (fun p _ => (hcommonAll ⟨p, Fact.out⟩).2)

/-- Conditional generic Hasse--Minkowski assembly: representation
local-global in dimensions `m` and `n` implies isotropy local-global in
dimension `m+n`. -/
theorem gramIsotropic_rat_of_real_and_padic_of_add_representation_local_global
    {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hm_local_global : ∀ (A : Matrix (Fin m) (Fin m) ℚ),
      A.IsSymm → A.det ≠ 0 → ∀ (q : ℚ), q ≠ 0 →
        (∃ u : Fin m → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℝ)) u = (q : ℝ)) →
        (∀ (p : ℕ) [Fact p.Prime], ∃ u : Fin m → ℚ_[p],
          PositiveDefiniteIntegralLattice.gramQuadraticValue
            (A.map (algebraMap ℚ ℚ_[p])) u = (q : ℚ_[p])) →
        ∃ u : Fin m → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A u = q)
    (hn_local_global : ∀ (B : Matrix (Fin n) (Fin n) ℚ),
      B.IsSymm → B.det ≠ 0 → ∀ (q : ℚ), q ≠ 0 →
        (∃ v : Fin n → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℝ)) v = (q : ℝ)) →
        (∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin n → ℚ_[p],
          PositiveDefiniteIntegralLattice.gramQuadraticValue
            (B.map (algebraMap ℚ ℚ_[p])) v = (q : ℚ_[p])) →
        ∃ v : Fin n → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue B v = q)
    (M : Matrix (Fin (m + n)) (Fin (m + n)) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    PositiveDefiniteIntegralLattice.GramIsotropic M := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP,
      hcommonReal, hcommonPadic⟩ :=
    exists_differenceGramBlock_common_values_of_real_and_padic
      M hM_symm hM_det hreal hpadic
  obtain ⟨q, hq, hcommon⟩ :=
    exists_matrixPairCommonRepresents_rat_of_real_and_padic
      hm hn A B hA_symm hA_det hB_symm hB_det hcommonReal hcommonPadic
      (hm_local_global A hA_symm hA_det)
      (hn_local_global B hB_symm hB_det)
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.differenceGramBlock A B) :=
    (PositiveDefiniteIntegralLattice.gramIsotropic_differenceGramBlock_iff_exists_common_value
      A B hA_symm hA_det hB_symm hB_det (by norm_num)).2
      ⟨q, hq, hcommon⟩
  exact PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
    (show (PositiveDefiniteIntegralLattice.differenceGramBlock A B).IsCongruent M from
      (show M.IsCongruent (PositiveDefiniteIntegralLattice.differenceGramBlock A B) from
        ⟨P, hP⟩).symm)
    hblock

/-- Conditional one-line induction bridge: isotropy local-global in dimension
`n+1` implies nonzero representation local-global in dimension `n`. -/
theorem exists_gramQuadraticValue_eq_rat_of_real_and_padic_of_succ_gramIsotropic
    {n : ℕ}
    (hsucc_local_global :
      ∀ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ),
        M.IsSymm → M.det ≠ 0 →
        PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℝ)) →
        (∀ (p : ℕ) [Fact p.Prime], PositiveDefiniteIntegralLattice.GramIsotropic
          (M.map (algebraMap ℚ ℚ_[p]))) →
        PositiveDefiniteIntegralLattice.GramIsotropic M)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0)
    (hreal : ∃ v : Fin n → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
      (A.map (algebraMap ℚ ℝ)) v = (c : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin n → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p])) :
    ∃ v : Fin n → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock (-c) A
  have hB_symm : B.IsSymm :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock_isSymm (-c) A hA_symm
  have hB_det : B.det ≠ 0 := by
    simp only [B, PositiveDefiniteIntegralLattice.finSuccGramBlock_det]
    exact mul_ne_zero (neg_ne_zero.mpr hc) hA_det
  have hB_real : PositiveDefiniteIntegralLattice.GramIsotropic
      (B.map (algebraMap ℚ ℝ)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℝ) (A.map (algebraMap ℚ ℝ)) hreal
    simpa [B] using h
  have hB_padic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic (B.map (algebraMap ℚ ℚ_[p])) := by
    intro p hp
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℚ_[p]) (A.map (algebraMap ℚ ℚ_[p])) (hpadic p)
    simpa [B] using h
  have hB : PositiveDefiniteIntegralLattice.GramIsotropic B :=
    hsucc_local_global B hB_symm hB_det hB_real hB_padic
  rcases PositiveDefiniteIntegralLattice.gramIsotropic_or_exists_value_of_finSuccGramBlock
      c A hB with hA | hrep
  · exact PositiveDefiniteIntegralLattice.exists_gramQuadraticValue_eq_of_gramIsotropic
      A hA_symm hA_det (by norm_num) hA c
  · exact hrep

/-- Hasse--Minkowski for nonsingular symmetric rational Gram matrices in every
dimension at least three. -/
theorem gramIsotropic_rat_of_real_and_padic
    {n : ℕ} (hn : 3 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    PositiveDefiniteIntegralLattice.GramIsotropic M := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn10 : n ≤ 10
      · interval_cases n
        · exact ternaryGramIsotropic_rat_of_real_and_padic
            M hM_symm hM_det hreal hpadic
        · exact rankFourGramIsotropic_rat_of_real_and_padic
            M hM_symm hM_det hreal hpadic
        · exact rankFiveGramIsotropic_rat_of_real_and_padic
            M hM_symm hM_det hreal hpadic
        · exact rankSixGramIsotropic_rat_of_real_and_padic
            M hM_symm hM_det hreal hpadic
        · exact rankSevenGramIsotropic_rat_of_real_and_padic
            M hM_symm hM_det hreal hpadic
        · exact rankEightGramIsotropic_rat_of_real_and_padic
            M hM_symm hM_det hreal hpadic
        · exact rankNineGramIsotropic_rat_of_real_and_padic
            M hM_symm hM_det hreal hpadic
        · exact rankTenGramIsotropic_rat_of_real_and_padic
            M hM_symm hM_det hreal hpadic
      · have hn11 : 11 ≤ n := by omega
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
        apply gramIsotropic_rat_of_real_and_padic_of_add_representation_local_global
            (m := 3) (n := k) (by norm_num) (by omega)
        · intro A hA_symm hA_det q hq hAreal hApadic
          exact
            exists_gramQuadraticValue_eq_rat_of_real_and_padic_of_succ_gramIsotropic
              (fun N hN_symm hN_det hN_real hN_padic =>
                rankFourGramIsotropic_rat_of_real_and_padic
                  N hN_symm hN_det hN_real hN_padic)
              A hA_symm hA_det q hq hAreal hApadic
        · intro B hB_symm hB_det q hq hBreal hBpadic
          exact
            exists_gramQuadraticValue_eq_rat_of_real_and_padic_of_succ_gramIsotropic
              (fun N hN_symm hN_det hN_real hN_padic =>
                ih (k + 1) (by omega) (by omega)
                  N hN_symm hN_det hN_real hN_padic)
              B hB_symm hB_det q hq hBreal hBpadic
        · exact hM_symm
        · exact hM_det
        · exact hreal
        · exact hpadic

/-- Arbitrary-rank rational Hasse--Minkowski, expressed as equivalence with
real and all p-adic Gram isotropy. -/
theorem gramIsotropic_iff_real_and_padic
    {n : ℕ} (hn : 3 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic M ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℝ)) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          PositiveDefiniteIntegralLattice.GramIsotropic
            (M.map (algebraMap ℚ ℚ_[p])) := by
  constructor
  · intro hM
    exact
      ⟨gramIsotropic_scalarExtension_of_rat (K := ℝ) hM,
        fun p _ => gramIsotropic_scalarExtension_of_rat (K := ℚ_[p]) hM⟩
  · rintro ⟨hreal, hpadic⟩
    exact gramIsotropic_rat_of_real_and_padic
      hn M hM_symm hM_det hreal hpadic

/-- A nonzero scalar locally represented by a nonsingular symmetric rational
form of dimension at least two is represented over the rationals. -/
theorem exists_gramQuadraticValue_eq_rat_of_real_and_padic
    {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0)
    (hreal : ∃ v : Fin n → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
      (A.map (algebraMap ℚ ℝ)) v = (c : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin n → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p])) :
    ∃ v : Fin n → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c := by
  exact
    exists_gramQuadraticValue_eq_rat_of_real_and_padic_of_succ_gramIsotropic
      (fun M hM_symm hM_det hM_real hM_padic =>
        gramIsotropic_rat_of_real_and_padic
          (n := n + 1) (by omega) M hM_symm hM_det hM_real hM_padic)
      A hA_symm hA_det c hc hreal hpadic

/-- Nonzero scalar representation by a nonsingular symmetric rational form of
dimension at least two is equivalent to representation over the real and
every p-adic field. -/
theorem exists_gramQuadraticValue_eq_iff_real_and_padic
    {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0) :
    (∃ v : Fin n → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c) ↔
      (∃ v : Fin n → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin n → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p]) := by
  constructor
  · intro hrep
    exact ⟨exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℝ) hrep,
      fun p _ => exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℚ_[p]) hrep⟩
  · rintro ⟨hreal, hpadic⟩
    exact exists_gramQuadraticValue_eq_rat_of_real_and_padic
      hn A hA_symm hA_det c hc hreal hpadic

end Rat
