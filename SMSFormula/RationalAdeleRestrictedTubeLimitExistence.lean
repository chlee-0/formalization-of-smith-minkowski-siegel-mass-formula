import SMSFormula.RationalAdeleResidueRestrictedTubeRankFour
import SMSFormula.RationalAdeleSingularSeriesRepresentation

/-!
# Tube limits of residue-restricted integral tests exist at every nonzero integer (rank ≥ 4)

The rank-four replacement lemma (`exists_tendsto_factorial_mul_localRestrictionCongruenceIntegral`)
computes the `k!`-tube limit of a residue-restricted integral indicator `1_{U_R}` at `M ≠ 0` under
the hypothesis that `M` is integrally represented at every prime of the restriction set `P`.  This
file removes that hypothesis for the existence of the limit:

* if `M` has no integral `p`-adic solution, the residue counts modulo `p^k` are eventually zero
  (`eventually_card_residueSet_primePow_eq_zero_of_not_represented`, by compactness of `ℤ_pⁿ`), hence
  so are the counts at `k!` (CRT) and the restricted tube masses; the limit is `0`;
* otherwise the theorem applies.

So `exists_tendsto_factorial_mul_restrictedTube` holds for every CRT residue restriction and every
`M ≠ 0` in rank at least four.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix Matrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- No integral solution ⇒ the counts modulo `p^k` are eventually zero (compactness of `ℤ_pⁿ`). -/
theorem eventually_card_residueSet_primePow_eq_zero_of_not_represented (L : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact p.Prime] (M : ℤ)
    (hno : ¬ ∃ x : Fin n → ℤ_[p],
      x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x = ((M : ℤ) : ℤ_[p])) :
    ∃ k₀, ∀ k, k₀ ≤ k → Nat.card {z : Fin n → ZMod (p ^ k) //
      L.zmodQuadForm (p ^ k) z = ((M : ℤ) : ZMod (p ^ k))} = 0 := by
  classical
  by_contra h
  push_neg at h
  apply hno
  set F := L.pairingMatrix.map (Int.castRingHom ℤ_[p]) with hFdef
  let t : ℕ → Set (Fin n → ℤ_[p]) := fun i ↦
    {x | ‖x ⬝ᵥ F *ᵥ x - ((M : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(i : ℤ))}
  have hQ : Continuous fun x : Fin n → ℤ_[p] ↦ x ⬝ᵥ F *ᵥ x - ((M : ℤ) : ℤ_[p]) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hP : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have htd : ∀ i, t (i + 1) ⊆ t i := by
    intro i x hx
    refine le_trans hx (zpow_le_zpow_right₀ hP ?_)
    push_cast
    omega
  have htn : ∀ i, (t i).Nonempty := by
    intro i
    obtain ⟨k, hk, hcard⟩ := h i
    obtain ⟨x, hx⟩ := L.exists_padicInt_norm_sub_le_of_card_ne_zero p M k hcard
    exact ⟨x, le_trans hx (zpow_le_zpow_right₀ hP (show (-(k : ℤ)) ≤ -(i : ℤ) by omega))⟩
  have htcl : ∀ i, IsClosed (t i) := fun i ↦
    isClosed_le (continuous_norm.comp hQ) continuous_const
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn
    (isCompact_univ.of_isClosed_subset (htcl 0) (Set.subset_univ _)) htcl
  rw [Set.mem_iInter] at hx
  refine ⟨x, sub_eq_zero.1 (PadicInt.ext_of_toZModPow.1 fun m ↦ ?_)⟩
  have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).1 (hx m)
  rw [map_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
  exact hmem

/-- The count at `m` vanishes when the count at one of its prime-power parts vanishes (CRT). -/
theorem card_residueSet_eq_zero_of_primePow (L : PositiveDefiniteIntegralLattice n) (M : ℤ) {m : ℕ} (hm : m ≠ 0)
    {p : ℕ} (hp : p.Prime) (hpm : p ∣ m)
    (h0 : Nat.card {z : Fin n → ZMod (p ^ m.factorization p) //
      L.zmodQuadForm (p ^ m.factorization p) z = ((M : ℤ) : ZMod (p ^ m.factorization p))} = 0) :
    Nat.card {z : Fin n → ZMod m // L.zmodQuadForm m z = ((M : ℤ) : ZMod m)} = 0 := by
  rw [L.card_residueSet_eq_prod_factorization M hm, Finsupp.prod]
  refine Finset.prod_eq_zero (i := p) ?_ h0
  rw [Nat.support_factorization]
  exact Nat.mem_primeFactors.2 ⟨hp, hpm, hm⟩

theorem tendsto_factorization_factorial_atTop (p : ℕ) (hp : p.Prime) :
    Tendsto (fun k : ℕ ↦ (Nat.factorial k).factorization p) atTop atTop := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact tendsto_factorization_factorial p

/-- No integral solution at some prime ⇒ the restricted `k!`-tube masses are eventually zero. -/
theorem eventually_restrictedTube_eq_zero_of_not_represented (L : PositiveDefiniteIntegralLattice n) {N₀ : ℕ}
    [NeZero N₀] (R : Set (Fin n → ZMod N₀)) (M : ℤ) (p : ℕ) [hp : Fact p.Prime]
    (hno : ¬ ∃ x : Fin n → ℤ_[p],
      x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x = ((M : ℤ) : ℤ_[p])) :
    ∀ᶠ k : ℕ in atTop, ((Nat.factorial k : ℕ) : ℂ) *
        ∫ x : Fin n → RationalFiniteAdele,
          residueRestrictedIndicator n N₀ R x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n = 0 := by
  classical
  obtain ⟨k₀, hk₀⟩ := L.eventually_card_residueSet_primePow_eq_zero_of_not_represented p M hno
  have hv := (tendsto_factorization_factorial_atTop p hp.out).eventually_ge_atTop (max k₀ 1)
  filter_upwards [hv, eventually_ge_atTop N₀] with k hk hkN
  have hk0 : Nat.factorial k ≠ 0 := Nat.factorial_ne_zero k
  have hdvd : N₀ ∣ Nat.factorial k := Nat.dvd_factorial (Nat.pos_of_ne_zero (NeZero.ne N₀)) hkN
  have hpk : p ∣ Nat.factorial k := by
    have h1 : 1 ≤ (Nat.factorial k).factorization p := le_trans (le_max_right _ _) hk
    exact (Nat.Prime.dvd_iff_one_le_factorization hp.out hk0).2 h1
  have hfull := L.card_residueSet_eq_zero_of_primePow M hk0 hp.out hpk
    (hk₀ _ (le_trans (le_max_left _ _) hk))
  rw [L.measure_restrictedCongruenceSet_eq_residueCount hk0 hdvd R M]
  have hres : Nat.card {z : Fin n → ZMod (Nat.factorial k) //
      L.zmodQuadForm (Nat.factorial k) z = ((M : ℤ) : ZMod (Nat.factorial k)) ∧
      (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ R} = 0 := by
    haveI : NeZero (Nat.factorial k) := ⟨hk0⟩
    rw [Nat.card_eq_zero] at hfull ⊢
    rcases hfull with hfull | hfull
    · left
      exact ⟨fun z ↦ hfull.false ⟨z.1, z.2.1⟩⟩
    · right
      exact absurd hfull (not_infinite_iff_finite.2 inferInstance)
  rw [hres]
  simp

/-- The ℤ_p-form of integral representation from the ℚ_p-form hypothesis. -/
theorem exists_rep_of_padicInt (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime] (M : ℤ)
    (h : ∃ x : Fin n → ℤ_[p],
      x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x = ((M : ℤ) : ℤ_[p])) :
    ∃ u : Fin n → ℚ_[p], ‖u‖ ≤ 1 ∧
      ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' u = (((M : ℤ) : ℤ_[p]) : ℚ_[p]) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨fun i ↦ (x i : ℚ_[p]), ?_, ?_⟩
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ by
      rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one _
  · rw [Matrix.toQuadraticMap', Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', ← hx]
    have hcomp : (fun i ↦ ((x i : ℤ_[p]) : ℚ_[p])) =
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) ∘ x := rfl
    change _ = (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) _
    rw [hcomp, RingHom.map_dotProduct]
    congr 1
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm

set_option maxHeartbeats 2000000 in
/-- The restricted tube limit exists at every `M ≠ 0` in rank at least four, for every CRT residue
restriction: it is `(∏ gR/∏ gF) · ∏'_p δ_p(M)` when `M` is integrally represented at every prime of
`P`, and `0` otherwise. -/
theorem exists_tendsto_factorial_mul_restrictedTube (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n)
    {M : ℤ} (hM : M ≠ 0) (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    ∃ D : ℂ, Tendsto (fun k : ℕ ↦ ((Nat.factorial k : ℕ) : ℂ) *
        ∫ x : Fin (n + 1) → RationalFiniteAdele,
          residueRestrictedIndicator (n + 1) (localRestrictionLevel P e)
              (localRestrictionSet P e R) x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1)) atTop (𝓝 D) := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  classical
  by_cases hrep : ∀ p (hp : p ∈ P), haveI : Fact p.Prime := ⟨(hP p hp).1⟩;
      ∃ x : Fin (n + 1) → ℤ_[p],
        x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x = ((M : ℤ) : ℤ_[p])
  · obtain ⟨gF, gR, -, -, -, -, h⟩ := L.exists_tendsto_factorial_mul_localRestrictionCongruenceIntegral
      hn hM P e R hP fun p hp ↦ by
        haveI : Fact p.Prime := ⟨(hP p hp).1⟩
        exact L.exists_rep_of_padicInt p M (hrep p hp)
    exact ⟨_, h⟩
  · push_neg at hrep
    obtain ⟨p, hp, hno⟩ := hrep
    haveI : Fact p.Prime := ⟨(hP p hp).1⟩
    refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [L.eventually_restrictedTube_eq_zero_of_not_represented
      (localRestrictionSet P e R) M p (fun ⟨x, hx⟩ ↦ hno x hx)] with k hk
    exact hk.symm

end PositiveDefiniteIntegralLattice
