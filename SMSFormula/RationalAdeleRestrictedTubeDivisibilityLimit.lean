import SMSFormula.RationalAdeleResidueRestrictedTubeRankFour
import SMSFormula.RationalAdeleSingularSeriesDivisibilityLimit
import SMSFormula.RationalAdeleRestrictedTubeLimitExistence

/-!
# Restricted tube limits along any divisibility-cofinal widths

The rank-four tube limits are taken along the widths `k!`.  A core finite factor carried by
`(1/c)Ẑⁿ` becomes, after dilation by `c`, a residue function on `Ẑⁿ` whose tubes have widths
`c²·k!`, which are not factorials.  This file gives the limits along every width sequence
`m_k ≠ 0` that is eventually divisible by each positive integer:
* `eventually_restrictedResidueCount_mul_prod_eq_of_tendsto` (CRT, proof along `m_k`);
* `tendsto_mul_localRestrictionCongruenceIntegral_of_eventually_dvd`: the replacement lemma
  `m_k · ∫ 1_{U_R} 1_{Q ≡ M (m_k)} → (∏ gR/∏ gF) · ∏'_p δ_p(M)`.
Only the rank-free count identities and the divisibility-cofinal full tube limit
(`tendsto_mul_congruenceIntegral_of_eventually_dvd`) are used.
Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- CRT along any widths whose valuations at the primes of `P` tend to infinity. -/
theorem eventually_restrictedResidueCount_mul_prod_eq_of_tendsto (L : PositiveDefiniteIntegralLattice n) (M : ℤ)
    (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞)
    (hloc : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop,
      (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0)
    {m : ℕ → ℕ} (hm0 : ∀ k, m k ≠ 0)
    (hv : ∀ p ∈ P, Tendsto (fun k ↦ (m k).factorization p) atTop atTop) :
    ∀ᶠ k : ℕ in atTop,
      (L.restrictedResidueCount M P e R (m k) : ℝ≥0∞) * ∏ p ∈ P, gF p =
        (L.fullResidueCount M (m k) : ℝ≥0∞) * ∏ p ∈ P, gR p := by
  have hall : ∀ᶠ k : ℕ in atTop, ∀ p ∈ P,
      ((L.restrictedResidueCount M P e R (p ^ (m k).factorization p) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ (m k).factorization p) : ℝ≥0∞) * gR p) ∧
        L.fullResidueCount M (p ^ (m k).factorization p) ≠ 0 :=
    (Filter.eventually_all_finset P).2 fun p hp ↦
      ((hv p hp).eventually (hloc p hp)).and ((hv p hp).eventually (hFne p hp))
  filter_upwards [hall] with k hk
  have hprod := L.restrictedResidueCount_mul_prod_eq M P e R hP (hm0 k)
  have hprodE : (L.restrictedResidueCount M P e R (m k) : ℝ≥0∞) *
      ∏ p ∈ P, (L.fullResidueCount M (p ^ (m k).factorization p) : ℝ≥0∞) =
      (L.fullResidueCount M (m k) : ℝ≥0∞) *
        ∏ p ∈ P, (L.restrictedResidueCount M P e R (p ^ (m k).factorization p) : ℝ≥0∞) := by
    exact_mod_cast hprod
  have hFP0 : (∏ p ∈ P, (L.fullResidueCount M (p ^ (m k).factorization p) : ℝ≥0∞)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp ↦ by exact_mod_cast (hk p hp).2
  have hFPt : (∏ p ∈ P, (L.fullResidueCount M (p ^ (m k).factorization p) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.prod_ne_top fun p _ ↦ ENNReal.natCast_ne_top _
  refine (ENNReal.mul_left_inj hFP0 hFPt).mp ?_
  set A : ℝ≥0∞ := ∏ p ∈ P, (L.fullResidueCount M (p ^ (m k).factorization p) : ℝ≥0∞) with hA
  set Bf : ℝ≥0∞ := ∏ p ∈ P, (L.restrictedResidueCount M P e R
    (p ^ (m k).factorization p) : ℝ≥0∞) with hBf
  have hstep : Bf * ∏ p ∈ P, gF p = A * ∏ p ∈ P, gR p := by
    rw [hBf, hA, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp ↦ (hk p hp).1
  calc ((L.restrictedResidueCount M P e R (m k) : ℝ≥0∞) * ∏ p ∈ P, gF p) * A
      = ((L.restrictedResidueCount M P e R (m k) : ℝ≥0∞) * A) * ∏ p ∈ P, gF p := by ring
    _ = ((L.fullResidueCount M (m k) : ℝ≥0∞) * Bf) * ∏ p ∈ P, gF p := by rw [hprodE]
    _ = (L.fullResidueCount M (m k) : ℝ≥0∞) * (Bf * ∏ p ∈ P, gF p) := by ring
    _ = (L.fullResidueCount M (m k) : ℝ≥0∞) * (A * ∏ p ∈ P, gR p) := by rw [hstep]
    _ = ((L.fullResidueCount M (m k) : ℝ≥0∞) * ∏ p ∈ P, gR p) * A := by ring

set_option maxHeartbeats 2000000 in
/-- The replacement lemma as a tube limit along any divisibility-cofinal widths, rank at least
four: `m_k · ∫ 1_{U_R} 1_{Q ≡ M (m_k)} → (∏_P gR_p / ∏_P gF_p) · ∏'_p δ_p(M)`. -/
theorem tendsto_mul_localRestrictionCongruenceIntegral_of_eventually_dvd
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞)
    (hgF0 : ∀ p ∈ P, gF p ≠ 0) (hgFt : ∀ p ∈ P, gF p ≠ ⊤)
    (hloc : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop,
      (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0)
    {m : ℕ → ℕ} (hm0 : ∀ k, m k ≠ 0) (hdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    Tendsto (fun k : ℕ ↦ ((m k : ℕ) : ℂ) *
        ∫ x : Fin (n + 1) → RationalFiniteAdele,
          residueRestrictedIndicator (n + 1) (localRestrictionLevel P e)
              (localRestrictionSet P e R) x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((m k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1))
      atTop (𝓝 ((((∏ p ∈ P, gR p) / ∏ p ∈ P, gF p).toReal : ℂ) *
        ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ))) := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  have hPF0 : (∏ p ∈ P, gF p) ≠ 0 := Finset.prod_ne_zero_iff.2 hgF0
  have hPFt : (∏ p ∈ P, gF p) ≠ ⊤ := ENNReal.prod_ne_top hgFt
  have hfull := L.tendsto_mul_congruenceIntegral_of_eventually_dvd hn hM hm0 hdvd
  refine (tendsto_const_nhds.mul hfull).congr' ?_
  have hv : ∀ p ∈ P, Tendsto (fun k ↦ (m k).factorization p) atTop atTop := fun p hp ↦
    tendsto_factorization_of_eventually_dvd hm0 hdvd (hP p hp).1
  filter_upwards [L.eventually_restrictedResidueCount_mul_prod_eq_of_tendsto M P e R hP gF gR hloc
    hFne hm0 hv, hdvd (localRestrictionLevel P e) (NeZero.ne _)] with k hk hdvdk
  have huniv := L.measure_restrictedCongruenceSet_eq_residueCount (hm0 k) hdvdk Set.univ M
  rw [residueRestrictedIndicator_univ (localRestrictionLevel P e)] at huniv
  rw [huniv, L.measure_restrictedCongruenceSet_eq_residueCount (hm0 k) hdvdk _ M]
  have hcardR : Nat.card {z : Fin (n + 1) → ZMod (m k) //
      L.zmodQuadForm (m k) z = ((M : ℤ) : ZMod (m k)) ∧
      (fun i ↦ ZMod.castHom hdvdk (ZMod (localRestrictionLevel P e)) (z i)) ∈
        localRestrictionSet P e R} = L.restrictedResidueCount M P e R (m k) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z ↦
      and_congr_right' (castHom_mem_localRestrictionSet_iff P e R hdvdk z))
  have hcardF : Nat.card {z : Fin (n + 1) → ZMod (m k) //
      L.zmodQuadForm (m k) z = ((M : ℤ) : ZMod (m k)) ∧
      (fun i ↦ ZMod.castHom hdvdk (ZMod (localRestrictionLevel P e)) (z i)) ∈
        (Set.univ : Set (Fin (n + 1) → ZMod (localRestrictionLevel P e)))} =
      L.fullResidueCount M (m k) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, Set.mem_univ _⟩⟩)
  rw [hcardR, hcardF]
  have hdiv : (L.restrictedResidueCount M P e R (m k) : ℝ≥0∞) =
      (L.fullResidueCount M (m k) : ℝ≥0∞) * ((∏ p ∈ P, gR p) / ∏ p ∈ P, gF p) := by
    rw [← mul_div_assoc, ENNReal.eq_div_iff hPF0 hPFt, mul_comm, hk]
  have hreal := congrArg ENNReal.toReal hdiv
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hreal
  have hc : ((L.restrictedResidueCount M P e R (m k) : ℕ) : ℂ) =
      (((L.restrictedResidueCount M P e R (m k) : ℕ) : ℝ) : ℂ) := by norm_cast
  rw [hc, hreal]
  push_cast
  ring

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- No integral solution at some prime ⇒ the restricted tube masses are eventually zero along any
divisibility-cofinal widths. -/
theorem eventually_restrictedTube_eq_zero_of_not_represented_of_dvd (L : PositiveDefiniteIntegralLattice n)
    {N₀ : ℕ} [NeZero N₀] (R : Set (Fin n → ZMod N₀)) (M : ℤ) (p : ℕ) [hp : Fact p.Prime]
    (hno : ¬ ∃ x : Fin n → ℤ_[p],
      x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x = ((M : ℤ) : ℤ_[p]))
    {m : ℕ → ℕ} (hm0 : ∀ k, m k ≠ 0) (hdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) :
    ∀ᶠ k : ℕ in atTop, ((m k : ℕ) : ℂ) *
        ∫ x : Fin n → RationalFiniteAdele,
          residueRestrictedIndicator n N₀ R x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((m k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n = 0 := by
  classical
  obtain ⟨k₀, hk₀⟩ := L.eventually_card_residueSet_primePow_eq_zero_of_not_represented p M hno
  have hv := (tendsto_factorization_of_eventually_dvd hm0 hdvd hp.out).eventually_ge_atTop
    (max k₀ 1)
  filter_upwards [hv, hdvd N₀ (NeZero.ne N₀)] with k hk hdvdk
  have hk0 : m k ≠ 0 := hm0 k
  have hpk : p ∣ m k := by
    have h1 : 1 ≤ (m k).factorization p := le_trans (le_max_right _ _) hk
    exact (Nat.Prime.dvd_iff_one_le_factorization hp.out hk0).2 h1
  have hfull := L.card_residueSet_eq_zero_of_primePow M hk0 hp.out hpk
    (hk₀ _ (le_trans (le_max_left _ _) hk))
  rw [L.measure_restrictedCongruenceSet_eq_residueCount hk0 hdvdk R M]
  have hres : Nat.card {z : Fin n → ZMod (m k) //
      L.zmodQuadForm (m k) z = ((M : ℤ) : ZMod (m k)) ∧
      (fun i ↦ ZMod.castHom hdvdk (ZMod N₀) (z i)) ∈ R} = 0 := by
    haveI : NeZero (m k) := ⟨hk0⟩
    rw [Nat.card_eq_zero] at hfull ⊢
    rcases hfull with hfull | hfull
    · left
      exact ⟨fun z ↦ hfull.false ⟨z.1, z.2.1⟩⟩
    · right
      exact absurd hfull (not_infinite_iff_finite.2 inferInstance)
  rw [hres]
  simp

set_option maxHeartbeats 2000000 in
/-- The restricted tube limit is width-independent: for every CRT residue restriction and every
`M ≠ 0` (rank at least four) there is one value `D` such that the tube masses converge to `D` along
every divisibility-cofinal width sequence. -/
theorem exists_forall_tendsto_mul_restrictedTube_of_eventually_dvd (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    ∃ D : ℂ, ∀ (m : ℕ → ℕ), (∀ k, m k ≠ 0) → (∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) →
      Tendsto (fun k : ℕ ↦ ((m k : ℕ) : ℂ) *
        ∫ x : Fin (n + 1) → RationalFiniteAdele,
          residueRestrictedIndicator (n + 1) (localRestrictionLevel P e)
              (localRestrictionSet P e R) x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((m k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1)) atTop (𝓝 D) := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  classical
  by_cases hrep : ∀ p (hp : p ∈ P), haveI : Fact p.Prime := ⟨(hP p hp).1⟩;
      ∃ x : Fin (n + 1) → ℤ_[p],
        x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x = ((M : ℤ) : ℤ_[p])
  · obtain ⟨gF, gR, h0, ht, hloc, hFne⟩ := L.exists_localGlueRatio_family M hM P e R hP
      fun p hp ↦ by
        haveI : Fact p.Prime := ⟨(hP p hp).1⟩
        exact L.exists_rep_of_padicInt p M (hrep p hp)
    exact ⟨_, fun m hm0 hdvd ↦ L.tendsto_mul_localRestrictionCongruenceIntegral_of_eventually_dvd
      hn hM P e R hP gF gR h0 ht hloc hFne hm0 hdvd⟩
  · push_neg at hrep
    obtain ⟨p, hp, hno⟩ := hrep
    haveI : Fact p.Prime := ⟨(hP p hp).1⟩
    refine ⟨0, fun m hm0 hdvd ↦ tendsto_const_nhds.congr' ?_⟩
    filter_upwards [L.eventually_restrictedTube_eq_zero_of_not_represented_of_dvd
      (localRestrictionSet P e R) M p (fun ⟨x, hx⟩ ↦ hno x hx) hm0 hdvd] with k hk
    exact hk.symm

end PositiveDefiniteIntegralLattice
