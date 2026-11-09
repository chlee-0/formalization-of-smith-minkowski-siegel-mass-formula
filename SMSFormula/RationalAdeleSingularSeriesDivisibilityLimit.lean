import SMSFormula.RationalAdeleSingularSeriesLocalDensity

/-!
# The rank-four singular series along every divisibility-cofinal level sequence

The residue-count limit uses the levels `k!`.  In rank at least four the limit exists along
every sequence of levels `m_k` that is eventually divisible by each positive integer, and it is
always the Euler product `∏'_p δ_p(M)`:

* `tendsto_normalizedResidueCount_of_eventually_dvd`: the normalized residue counts at `m_k`;
* `tendsto_mul_congruenceIntegral_of_eventually_dvd`: the `m_k`-tube masses
  `m_k · ∫ 1_Ẑ(x) 1_Ẑ((Q(x) - M)/m_k) dx` of the integral indicator;
* `tendsto_mul_congruenceIntegral_dilatedFactorial`: the special case of the dilated levels `c · k!`.

So the Fourier-free finite value density in rank four does not depend on the level sequence (for
example the dilated levels `c² · k!` used by the dual test).  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A level sequence eventually divisible by each positive integer has `p`-adic valuations tending
to infinity at every prime. -/
theorem tendsto_factorization_of_eventually_dvd {m : ℕ → ℕ} (hm0 : ∀ k, m k ≠ 0)
    (hdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun k ↦ (m k).factorization p) atTop atTop := by
  refine Filter.tendsto_atTop.2 fun j ↦ ?_
  filter_upwards [hdvd (p ^ j) (pow_ne_zero _ hp.ne_zero)] with k hk
  exact (hp.pow_dvd_iff_le_factorization (hm0 k)).1 hk

/-- The prime-factor sets of such a level sequence tend to the whole set of primes. -/
theorem tendsto_primeFactors_subtype_of_eventually_dvd {m : ℕ → ℕ} (hm0 : ∀ k, m k ≠ 0)
    (hdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) :
    Tendsto (fun k ↦ (m k).primeFactors.subtype Nat.Prime) atTop atTop := by
  classical
  refine Filter.tendsto_atTop.2 fun t ↦ ?_
  have hN : (∏ p ∈ t, (p : ℕ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ ↦ p.2.ne_zero
  filter_upwards [hdvd _ hN] with k hk
  intro p hp
  rw [Finset.mem_subtype, Nat.mem_primeFactors]
  exact ⟨p.2, (Finset.dvd_prod_of_mem (fun q : Nat.Primes ↦ (q : ℕ)) hp).trans hk, hm0 k⟩

/-- The rank-four singular series along any divisibility-cofinal levels: for `M ≠ 0` and levels
`m_k ≠ 0` eventually divisible by each positive integer, the normalized residue counts at `m_k`
converge to `∏'_p δ_p(M)`. -/
theorem tendsto_normalizedResidueCount_of_eventually_dvd (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) {m : ℕ → ℕ} (hm0 : ∀ k, m k ≠ 0)
    (hdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) :
    Tendsto (fun k ↦ L.normalizedResidueCount M (m k)) atTop
      (𝓝 (∏' p : Nat.Primes, L.localResidueDensity M p)) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, L.IsResidueBadBlock M T :=
    ⟨_, L.isResidueBadBlock_residueBadBlock hM⟩
  obtain ⟨-, hprod⟩ := L.multipliable_localResidueDensity_of_three_le hn hM hT
  obtain ⟨hgood, -⟩ := L.multipliable_goodResidueFactor_and_tprod_pos_of_three_le hn hT
  -- the good part converges along the prime-factor sets
  have hpartial : Tendsto (fun k ↦ ∏ p ∈ (m k).primeFactors, L.goodResidueFactor M T p) atTop
      (𝓝 (∏' p : Nat.Primes, L.goodResidueFactor M T p)) := by
    refine (hgood.hasProd.comp (tendsto_primeFactors_subtype_of_eventually_dvd hm0 hdvd)).congr
      fun k ↦ ?_
    refine (Finset.prod_subtype_eq_prod_filter (fun p : ℕ ↦ L.goodResidueFactor M T p)).trans ?_
    rw [Finset.filter_true_of_mem fun p hp ↦ Nat.prime_of_mem_primeFactors hp]
  rw [hprod]
  refine (tendsto_const_nhds.mul hpartial).congr' ?_
  -- eventually the block primes divide `m_k` and sit at their stable level
  have hTdvd : ∀ᶠ k in atTop, ∀ p ∈ T.filter Nat.Prime, p ∣ m k := by
    rw [Filter.eventually_all_finset]
    intro p hp
    exact hdvd p (Finset.mem_filter.1 hp).2.ne_zero
  have hTstab : ∀ᶠ k in atTop, ∀ p ∈ T.filter Nat.Prime,
      L.normalizedResidueCount M (p ^ (m k).factorization p) = L.localResidueDensity M p := by
    rw [Filter.eventually_all_finset]
    intro p hp
    haveI : Fact p.Prime := ⟨(Finset.mem_filter.1 hp).2⟩
    exact (tendsto_factorization_of_eventually_dvd hm0 hdvd (Finset.mem_filter.1 hp).2).eventually
      (L.eventually_normalizedResidueCount_eq_localResidueDensity p hM)
  filter_upwards [hTdvd, hTstab] with k hkdvd hkstab
  set P := (m k).primeFactors with hPdef
  rw [L.normalizedResidueCount_eq_prod_primeFactors M (hm0 k)]
  conv_rhs => rw [← Finset.prod_filter_mul_prod_filter_not P (· ∈ T)]
  conv_lhs => rw [← Finset.prod_filter_mul_prod_filter_not P (· ∈ T)]
  have hblock : P.filter (· ∈ T) = T.filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, hPdef, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, -, -⟩, hpT⟩
      exact ⟨hpT, hp⟩
    · rintro ⟨hpT, hp⟩
      exact ⟨⟨hp, hkdvd p (Finset.mem_filter.2 ⟨hpT, hp⟩), hm0 k⟩, hpT⟩
  have hgood1 : ∏ p ∈ P.filter (· ∈ T), L.goodResidueFactor M T p = 1 :=
    Finset.prod_eq_one fun p hp ↦ by
      simp only [goodResidueFactor, if_pos (Finset.mem_filter.1 hp).2]
  have hrest : ∏ p ∈ P.filter (· ∉ T), L.normalizedResidueCount M (p ^ (m k).factorization p) =
      ∏ p ∈ P.filter (· ∉ T), L.goodResidueFactor M T p := by
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    obtain ⟨hpP, hpT⟩ := Finset.mem_filter.1 hp
    have hprime := Nat.prime_of_mem_primeFactors hpP
    haveI : Fact p.Prime := ⟨hprime⟩
    have hp2 : p ≠ 2 := fun h ↦ hpT (h ▸ hT.1)
    have hpM : ¬ (p : ℤ) ∣ M := fun h ↦ hpT (hT.2.1 p hprime h)
    have hv : 1 ≤ (m k).factorization p :=
      hprime.factorization_pos_of_dvd (hm0 k) (Nat.dvd_of_mem_primeFactors hpP)
    simp only [goodResidueFactor, if_neg hpT]
    exact L.normalizedResidueCount_primePow_eq hp2 hpM hv
  rw [hgood1, one_mul, hrest, hblock]
  congr 1
  exact Finset.prod_congr rfl fun p hp ↦ (hkstab p hp).symm

set_option maxHeartbeats 2000000 in
/-- The rank-four tube density along any divisibility-cofinal levels: the `m_k`-tube masses of the
integral indicator at `M ≠ 0` converge to `∏'_p δ_p(M)`. -/
theorem tendsto_mul_congruenceIntegral_of_eventually_dvd (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) {m : ℕ → ℕ} (hm0 : ∀ k, m k ≠ 0)
    (hdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) :
    Tendsto (fun k : ℕ ↦ ((m k : ℕ) : ℂ) *
        ∫ x : Fin (n + 1) → RationalFiniteAdele,
          rationalFiniteAdeleVectorIntegralIndicator x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((m k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1))
      atTop (𝓝 ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp
    (L.tendsto_normalizedResidueCount_of_eventually_dvd hn hM hm0 hdvd)
  refine h.congr fun k ↦ ?_
  have hk0 : ((m k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm0 k
  rw [Function.comp_apply, L.measure_congruenceSet_eq_residueCount (hm0 k) M]
  unfold normalizedResidueCount
  push_cast
  rw [pow_succ]
  field_simp

/-- The factorial levels are divisibility-cofinal. -/
theorem eventually_dvd_factorial (N : ℕ) (hN : N ≠ 0) : ∀ᶠ k in atTop, N ∣ Nat.factorial k :=
  Filter.eventually_atTop.2 ⟨N, fun _ hk ↦ Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hk⟩

/-- The dilated factorial levels `c · k!` are divisibility-cofinal. -/
theorem eventually_dvd_mul_factorial (c N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ k in atTop, N ∣ c * Nat.factorial k :=
  (eventually_dvd_factorial N hN).mono fun _ h ↦ h.mul_left c

/-- The rank-four tube density at the dilated levels `c · k!` (`c ≠ 0`) is the same singular
series `∏'_p δ_p(M)`. -/
theorem tendsto_mul_congruenceIntegral_dilatedFactorial (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) {c : ℕ} (hc : c ≠ 0) :
    Tendsto (fun k : ℕ ↦ ((c * Nat.factorial k : ℕ) : ℂ) *
        ∫ x : Fin (n + 1) → RationalFiniteAdele,
          rationalFiniteAdeleVectorIntegralIndicator x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((c * Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1))
      atTop (𝓝 ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ)) :=
  L.tendsto_mul_congruenceIntegral_of_eventually_dvd hn hM
    (fun k ↦ mul_ne_zero hc (Nat.factorial_ne_zero k)) (eventually_dvd_mul_factorial c)

end PositiveDefiniteIntegralLattice
