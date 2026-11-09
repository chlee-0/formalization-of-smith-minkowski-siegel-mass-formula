import SMSFormula.PadicQuadraticResidueCountStable
import SMSFormula.RationalAdeleResidueCountMultiplicative
import SMSFormula.PadicQuadraticLocalDensityTailProduct
import SMSFormula.AdelicValueDensityLocalProduct

/-!
# The finite local value density at an integer is a finite block limit times an Euler product

The existing finite local value density of the standard integral indicator at an integer `M`
is the limit of the normalized residue counts `(k!)^{-n} #{z mod k! : Q_L(z) = M}` (rank
`n + 1`, `tendsto_finiteLocal_residueCount`).  Three existing or newly closed facts turn this
limit into an Euler product without assuming one:

* the residue count is multiplicative over the prime-power factorization of the level
  (`card_residueSet_eq_prod_factorization`), so the normalized count at `k!` is the product
  over `p ≤ k` of the normalized counts at `p^{v_p(k!)}`;
* at every odd prime `p ∤ M` the normalized count at `p^e` is the same for every `e ≥ 1`
  (`normalized_card_residueSet_primePow_eq`);
* at every odd prime `p ∤ M det F` the level-one count is the existing finite-field count, so
  the normalized count is `1 + O(p^{-2})` in rank at least five, and the product over those
  primes converges to a positive real.

For a supplied finite set `T` of primes containing `2`, the primes dividing `M` and the primes
dividing `det F`, the conclusion is

```text
d_fin(1_{Zhat^{n+1}})(M) = B_T(M) * prod_{p not in T} c_p(M),
B_T(M) = lim_k prod_{p in T} (p^{v_p(k!)})^{-n} #{z mod p^{v_p(k!)} : Q_L(z) = M},
```

with `c_p(M) = p^{-n} #{z mod p : Q_L(z) = M}` the good-prime factor, and the block limit
exists.  The block `T` is supplied, not chosen; no individual bad-prime limit is asserted, and
no identification of `B_T(M)` with any group volume is made here.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance srsFactPrimePowOne (p : ℕ) [Fact p.Prime] : Fact (p ^ 1).Prime :=
  ⟨by rw [pow_one]; exact Fact.out⟩

/-- The normalized residue count `m^{-n} #{z mod m : Q_L(z) = M}` in rank `n + 1`. -/
def normalizedResidueCount (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) (m : ℕ) : ℝ :=
  ((m : ℝ) ^ n)⁻¹ *
    (Nat.card {z : Fin (n + 1) → ZMod m // L.zmodQuadForm m z = ((M : ℤ) : ZMod m)} : ℝ)

/-- Euler structure of one truncation: the normalized count at `m ≠ 0` is the product of the
normalized counts at the prime powers of `m`. -/
theorem normalizedResidueCount_eq_prod_primeFactors (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ)
    {m : ℕ} (hm : m ≠ 0) :
    L.normalizedResidueCount M m =
      ∏ p ∈ m.primeFactors, L.normalizedResidueCount M (p ^ m.factorization p) := by
  have hself := Nat.factorization_prod_pow_eq_self hm
  rw [Finsupp.prod, Nat.support_factorization] at hself
  have hm' : (m : ℝ) = ∏ p ∈ m.primeFactors, ((p ^ m.factorization p : ℕ) : ℝ) := by
    rw [← Nat.cast_prod, hself]
  rw [normalizedResidueCount, L.card_residueSet_eq_prod_factorization M hm, Finsupp.prod,
    Nat.support_factorization, hm', ← Finset.prod_pow, ← Finset.prod_inv_distrib, Nat.cast_prod,
    ← Finset.prod_mul_distrib]
  rfl

/-- The prime factors of `k!` are the primes at most `k`. -/
theorem primeFactors_factorial (k : ℕ) :
    (Nat.factorial k).primeFactors = (Finset.range (k + 1)).filter Nat.Prime := by
  ext p
  rw [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hd, -⟩
    exact ⟨Nat.lt_succ_of_le ((hp.dvd_factorial).1 hd), hp⟩
  · rintro ⟨hr, hp⟩
    exact ⟨hp, (hp.dvd_factorial).2 (Nat.lt_succ_iff.1 hr), Nat.factorial_ne_zero k⟩

/-- Level stability in the normalized form, at every odd prime `p ∤ M`. -/
theorem normalizedResidueCount_primePow_eq (L : PositiveDefiniteIntegralLattice (n + 1)) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {M : ℤ} (hM : ¬ (p : ℤ) ∣ M) {k : ℕ} (hk : 1 ≤ k) :
    L.normalizedResidueCount M (p ^ k) = L.normalizedResidueCount M (p ^ 1) := by
  unfold normalizedResidueCount
  rw [L.normalized_card_residueSet_primePow_eq hp hM hk]
  congr 1
  rw [pow_one]

private theorem normalized_sub_one_odd {q χ : ℝ} (hq : q ≠ 0) :
    (q ^ 2)⁻¹ * (q ^ 2 + q * χ) - 1 = χ / q := by
  field_simp
  ring

private theorem normalized_sub_one_even {q r χ : ℝ} (hq : q ≠ 0) (hr : r ≠ 0) :
    (q * r)⁻¹ * (q * r - q * χ) - 1 = -(χ / r) := by
  field_simp
  ring

/-- The explicit good-prime normalized count is within `p^{-2}` of one in rank at least four: the
level-one deviation is `χ/p^m` in rank `2m+1` (`m ≥ 2`) and `χ/p^(m+1)` in rank `2m+2` (`m ≥ 1`). -/
theorem abs_normalizedResidueCount_prime_sub_one_le_of_three_le (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {M : ℤ} (hM : ¬ (p : ℤ) ∣ M)
    (hdet : ¬ (p : ℤ) ∣ L.pairingMatrix.det) :
    |L.normalizedResidueCount M (p ^ 1) - 1| ≤ 1 / (p : ℝ) ^ 2 := by
  have hunit : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → ‖(((z : ℤ) : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    intro z hz
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact le_antisymm (PadicInt.norm_le_one _)
      (not_lt.1 fun h ↦ hz ((PadicInt.norm_int_lt_one_iff_dvd z).1 h))
  have hF : (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).IsSymm := L.form_symm.map _
  have hdetF : ‖(((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).det : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    have h : (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).det = ((L.pairingMatrix.det : ℤ) : ℤ_[p]) := by
      rw [← eq_intCast (Int.castRingHom ℤ_[p]), RingHom.map_det, RingHom.mapMatrix_apply]
    rw [h]
    exact hunit _ hdet
  have ha := hunit M hM
  have hP : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hP0 : (0 : ℝ) < p := by linarith
  unfold normalizedResidueCount
  rw [L.card_residueSet_eq_card_filter_padic p M 1,
    show (((p ^ 1 : ℕ) : ℝ)) = (p : ℝ) by push_cast; ring]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h := PadicInt.card_levelOne_odd hp m _ hF hdetF ((M : ℤ) : ℤ_[p])
    have hχ := abs_quadraticChar_le_one ((-1) ^ m *
      PadicInt.toZModPow 1 (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).det *
      PadicInt.toZModPow 1 ((M : ℤ) : ℤ_[p]))
    have hR := congrArg (Int.cast : ℤ → ℝ) h
    push_cast at hR
    rw [hR]
    generalize ((quadraticChar (ZMod (p ^ 1)) ((-1) ^ m *
      PadicInt.toZModPow 1 (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).det *
      PadicInt.toZModPow 1 ((M : ℤ) : ℤ_[p])) : ℤ) : ℝ) = χ at hχ ⊢
    have hm : 2 ≤ m := by omega
    have hpm : (0 : ℝ) < (p : ℝ) ^ m := pow_pos hP0 m
    have heq : ((p : ℝ) ^ (2 * m))⁻¹ * ((p : ℝ) ^ (2 * m) + (p : ℝ) ^ m * χ) - 1 =
        χ / (p : ℝ) ^ m := by
      rw [pow_mul']
      exact normalized_sub_one_odd hpm.ne'
    rw [heq, abs_div, abs_of_pos hpm]
    calc |χ| / (p : ℝ) ^ m ≤ 1 / (p : ℝ) ^ m := div_le_div_of_nonneg_right hχ hpm.le
      _ ≤ 1 / (p : ℝ) ^ 2 := one_div_le_one_div_of_le (pow_pos hP0 2)
          (pow_le_pow_right₀ hP.le hm)
  · have h := PadicInt.card_levelOne_even hp m _ hF hdetF ((M : ℤ) : ℤ_[p]) ha
    have hχ := abs_quadraticChar_le_one ((-1) ^ (m + 1) *
      PadicInt.toZModPow 1 (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).det)
    have hR := congrArg (Int.cast : ℤ → ℝ) h
    push_cast at hR
    rw [hR]
    generalize ((quadraticChar (ZMod (p ^ 1)) ((-1) ^ (m + 1) *
      PadicInt.toZModPow 1 (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).det) : ℤ) : ℝ) = χ at hχ ⊢
    have hm : 2 ≤ m + 1 := by omega
    have hpm : (0 : ℝ) < (p : ℝ) ^ (m + 1) := pow_pos hP0 _
    have heq : ((p : ℝ) ^ (2 * m + 1))⁻¹ * ((p : ℝ) ^ (2 * m + 1) - (p : ℝ) ^ m * χ) - 1 =
        -(χ / (p : ℝ) ^ (m + 1)) := by
      rw [show (p : ℝ) ^ (2 * m + 1) = (p : ℝ) ^ m * (p : ℝ) ^ (m + 1) by
        rw [← pow_add]; congr 1; omega]
      exact normalized_sub_one_even (pow_pos hP0 m).ne' hpm.ne'
    rw [heq, abs_neg, abs_div, abs_of_pos hpm]
    calc |χ| / (p : ℝ) ^ (m + 1) ≤ 1 / (p : ℝ) ^ (m + 1) := div_le_div_of_nonneg_right hχ hpm.le
      _ ≤ 1 / (p : ℝ) ^ 2 := one_div_le_one_div_of_le (pow_pos hP0 2)
          (pow_le_pow_right₀ hP.le hm)

/-- The explicit good-prime normalized count is within `p^{-2}` of one in rank at least five. -/
theorem abs_normalizedResidueCount_prime_sub_one_le (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 4 ≤ n)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {M : ℤ} (hM : ¬ (p : ℤ) ∣ M)
    (hdet : ¬ (p : ℤ) ∣ L.pairingMatrix.det) :
    |L.normalizedResidueCount M (p ^ 1) - 1| ≤ 1 / (p : ℝ) ^ 2 :=
  L.abs_normalizedResidueCount_prime_sub_one_le_of_three_le (by omega) hp hM hdet

/-- The good-prime factor outside a supplied finite block `T`: one on `T`, the level-one
normalized count elsewhere. -/
def goodResidueFactor (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) (T : Finset ℕ) (p : ℕ) : ℝ :=
  if p ∈ T then 1 else L.normalizedResidueCount M (p ^ 1)

/-- A block containing `2`, the prime divisors of `M` and of `det F`. -/
def IsResidueBadBlock (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) (T : Finset ℕ) : Prop :=
  2 ∈ T ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ M → p ∈ T) ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ L.pairingMatrix.det → p ∈ T)

/-- The good Euler product converges to a positive real in rank at least four. -/
theorem multipliable_goodResidueFactor_and_tprod_pos_of_three_le (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} {T : Finset ℕ} (hT : L.IsResidueBadBlock M T) :
    Multipliable (fun p : Nat.Primes ↦ L.goodResidueFactor M T p) ∧
      0 < ∏' p : Nat.Primes, L.goodResidueFactor M T p := by
  have hbound : ∀ p : Nat.Primes,
      |L.goodResidueFactor M T p - 1| ≤ 1 / ((p : ℕ) : ℝ) ^ 2 := by
    intro p
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    unfold goodResidueFactor
    split_ifs with hpT
    · rw [sub_self, abs_zero]; positivity
    · have hp2 : (p : ℕ) ≠ 2 := fun h ↦ hpT (h ▸ hT.1)
      have hM : ¬ ((p : ℕ) : ℤ) ∣ M := fun h ↦ hpT (hT.2.1 p p.2 h)
      have hdet : ¬ ((p : ℕ) : ℤ) ∣ L.pairingMatrix.det := fun h ↦ hpT (hT.2.2 p p.2 h)
      exact L.abs_normalizedResidueCount_prime_sub_one_le_of_three_le hn hp2 hM hdet
  have h := Nat.Primes.multipliable_one_add_and_tprod_pos
    (fun p : Nat.Primes ↦ L.goodResidueFactor M T p - 1) le_rfl hbound
  simpa only [add_sub_cancel] using h

/-- The good Euler product converges to a positive real in rank at least five. -/
theorem multipliable_goodResidueFactor_and_tprod_pos (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 4 ≤ n)
    {M : ℤ} {T : Finset ℕ} (hT : L.IsResidueBadBlock M T) :
    Multipliable (fun p : Nat.Primes ↦ L.goodResidueFactor M T p) ∧
      0 < ∏' p : Nat.Primes, L.goodResidueFactor M T p :=
  L.multipliable_goodResidueFactor_and_tprod_pos_of_three_le (by omega) hT

/-- For `k` beyond the block, the normalized count at `k!` is the block product times the
partial good Euler product over `p ≤ k`. -/
theorem normalizedResidueCount_factorial_eq_block_mul (L : PositiveDefiniteIntegralLattice (n + 1)) {M : ℤ}
    {T : Finset ℕ} (hT : L.IsResidueBadBlock M T) {k : ℕ} (hk : ∀ t ∈ T, t ≤ k) :
    L.normalizedResidueCount M (Nat.factorial k) =
      (∏ p ∈ T.filter Nat.Prime,
          L.normalizedResidueCount M (p ^ (Nat.factorial k).factorization p)) *
        ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, L.goodResidueFactor M T p := by
  classical
  rw [L.normalizedResidueCount_eq_prod_primeFactors M (Nat.factorial_ne_zero k),
    primeFactors_factorial]
  set P := (Finset.range (k + 1)).filter Nat.Prime
  rw [← Finset.prod_filter_mul_prod_filter_not P (· ∈ T)]
  have hblock : P.filter (· ∈ T) = T.filter Nat.Prime := by
    ext p
    simp only [P, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨-, hp⟩, hpT⟩
      exact ⟨hpT, hp⟩
    · rintro ⟨hpT, hp⟩
      exact ⟨⟨Nat.lt_succ_of_le (hk p hpT), hp⟩, hpT⟩
  rw [hblock]
  congr 1
  unfold goodResidueFactor
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  simp only [P, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨⟨hpk, hprime⟩, hpT⟩ := hp
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp2 : p ≠ 2 := fun h ↦ hpT (h ▸ hT.1)
  have hM : ¬ (p : ℤ) ∣ M := fun h ↦ hpT (hT.2.1 p hprime h)
  have hv : 1 ≤ (Nat.factorial k).factorization p :=
    hprime.factorization_pos_of_dvd (Nat.factorial_ne_zero k)
      ((hprime.dvd_factorial).2 (Nat.lt_succ_iff.1 hpk))
  exact L.normalizedResidueCount_primePow_eq hp2 hM hv

/-- The finite local integral of the residue limit is a block limit times the Euler product.
For a supplied block `T` containing `2` and the prime divisors of `M` and `det F`, the block
products converge and the existing finite local integral at `M` is their limit times the
positive good Euler product, in rank at least five. -/
theorem finiteLocal_eq_blockLimit_mul_tprod (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 4 ≤ n)
    {M : ℤ} {T : Finset ℕ} (hT : L.IsResidueBadBlock M T) :
    ∃ B : ℝ,
      Tendsto (fun k : ℕ ↦ ∏ p ∈ T.filter Nat.Prime,
          L.normalizedResidueCount M (p ^ (Nat.factorial k).factorization p)) atTop (𝓝 B) ∧
      (∫ y : RationalFiniteAdele,
          ((rationalFiniteAdeleFourierChar
              (algebraMap ℚ RationalFiniteAdele (-((M : ℤ) : ℚ)) * y) : Circle) : ℂ) *
            L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
          ∂rationalFiniteAdeleAddHaarMeasure) =
        ((B * ∏' p : Nat.Primes, L.goodResidueFactor M T p : ℝ) : ℂ) := by
  classical
  set S := ∫ y : RationalFiniteAdele,
      ((rationalFiniteAdeleFourierChar
          (algebraMap ℚ RationalFiniteAdele (-((M : ℤ) : ℚ)) * y) : Circle) : ℂ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
      ∂rationalFiniteAdeleAddHaarMeasure with hSdef
  obtain ⟨hmult, hpos⟩ := L.multipliable_goodResidueFactor_and_tprod_pos hn hT
  set P := ∏' p : Nat.Primes, L.goodResidueFactor M T p with hPdef
  -- the real residue limit
  have hS : Tendsto (fun k : ℕ ↦ ((L.normalizedResidueCount M (Nat.factorial k) : ℝ) : ℂ))
      atTop (𝓝 S) := by
    refine (L.tendsto_finiteLocal_residueCount one_pos (by omega) M).congr fun k ↦ ?_
    have hk0 : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    unfold normalizedResidueCount
    push_cast
    rw [pow_succ]
    field_simp
    exact mul_div_mul_left _ _ (by exact_mod_cast hk0)
  have hre : Tendsto (fun k : ℕ ↦ L.normalizedResidueCount M (Nat.factorial k)) atTop
      (𝓝 S.re) := by
    simpa using (Complex.continuous_re.tendsto S).comp hS
  have him : S.im = 0 := by
    have h := (Complex.continuous_im.tendsto S).comp hS
    simp only [Function.comp_def, Complex.ofReal_im] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- the partial good products
  have hfin : Tendsto (fun k : ℕ ↦ (Finset.range (k + 1)).subtype Nat.Prime) atTop atTop := by
    apply Filter.tendsto_atTop_finset_of_monotone
    · intro a b hab
      exact Finset.subtype_mono (Finset.range_mono (by omega))
    · intro p
      exact ⟨p, Finset.mem_subtype.2 (Finset.mem_range.2 (Nat.lt_succ_self _))⟩
  have hpartial : Tendsto (fun k : ℕ ↦
      ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, L.goodResidueFactor M T p) atTop (𝓝 P) := by
    have h := hmult.hasProd.comp hfin
    refine h.congr fun k ↦ ?_
    exact Finset.prod_subtype_eq_prod_filter (fun p : ℕ ↦ L.goodResidueFactor M T p)
  -- the block products
  have hev : ∀ᶠ k in atTop,
      L.normalizedResidueCount M (Nat.factorial k) /
          ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, L.goodResidueFactor M T p =
        ∏ p ∈ T.filter Nat.Prime,
          L.normalizedResidueCount M (p ^ (Nat.factorial k).factorization p) := by
    filter_upwards [Filter.eventually_ge_atTop (T.sup id),
      hpartial.eventually_ne hpos.ne'] with k hk hne
    have hkT : ∀ t ∈ T, t ≤ k := fun t ht ↦ le_trans (Finset.le_sup (f := id) ht) hk
    rw [L.normalizedResidueCount_factorial_eq_block_mul hT hkT, mul_div_assoc, div_self hne,
      mul_one]
  refine ⟨S.re / P, (hre.div hpartial hpos.ne').congr' hev, ?_⟩
  rw [div_mul_cancel₀ _ hpos.ne']
  exact Complex.ext rfl (by simpa using him)

/-- The same identity for the literal finite local value density of the integral indicator at
the rational value `M`. -/
theorem finiteLocalValueDensity_integralIndicator_eq_blockLimit_mul_tprod
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 4 ≤ n) {M : ℤ} {T : Finset ℕ}
    (hT : L.IsResidueBadBlock M T) :
    ∃ B : ℝ,
      Tendsto (fun k : ℕ ↦ ∏ p ∈ T.filter Nat.Prime,
          L.normalizedResidueCount M (p ^ (Nat.factorial k).factorization p)) atTop (𝓝 B) ∧
      L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity
          rationalFiniteAdeleVectorIntegralIndicator (algebraMap ℚ RationalFiniteAdele (M : ℚ)) =
        ((B * ∏' p : Nat.Primes, L.goodResidueFactor M T p : ℝ) : ℂ) := by
  obtain ⟨B, hB, hS⟩ := L.finiteLocal_eq_blockLimit_mul_tprod hn hT
  refine ⟨B, hB, ?_⟩
  rw [← hS, finiteLocalValueDensity]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [finiteLocalBruhatCoefficient_integralIndicator]
  rw [show -(y * algebraMap ℚ RationalFiniteAdele (M : ℚ)) =
      algebraMap ℚ RationalFiniteAdele (-((M : ℤ) : ℚ)) * y by
    rw [RingHom.map_neg, neg_mul, mul_comm]]

/-- The adelic value density of the polar Gaussian--LATTICE test at a rational-integer finite
component: the real local density at the literal real scalar, times the block limit, times the
positive good Euler product. -/
theorem complexValueFourierDensity_polarGaussianLattice_eq_real_mul_blockLimit_mul_tprod
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 4 ≤ n) {M : ℤ} {T : Finset ℕ}
    (hT : L.IsResidueBadBlock M T) (b : ℂ) (w : RationalAdele)
    (hw : w.2 = algebraMap ℚ RationalFiniteAdele (M : ℚ)) :
    ∃ B : ℝ,
      Tendsto (fun k : ℕ ↦ ∏ p ∈ T.filter Nat.Prime,
          L.normalizedResidueCount M (p ^ (Nat.factorial k).factorization p)) atTop (𝓝 B) ∧
      L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
          (rationalAdeleVectorPolarGaussianLatticeTest L b) w =
        L.rationalQuadraticSpaceMatrix.realLocalValueDensity (polarRealGaussian L b)
            (rationalAdeleRealScalar w) *
          ((B * ∏' p : Nat.Primes, L.goodResidueFactor M T p : ℝ) : ℂ) := by
  obtain ⟨B, hB, hfin⟩ := L.finiteLocalValueDensity_integralIndicator_eq_blockLimit_mul_tprod hn hT
  refine ⟨B, hB, ?_⟩
  rw [complexValueFourierDensity_polarGaussianLattice, hw, hfin]

end PositiveDefiniteIntegralLattice

end
