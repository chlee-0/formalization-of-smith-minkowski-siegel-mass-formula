import SMSFormula.RationalAdeleRestrictedTubeDivisibilityLimit

/-!
# Tube limits for every residue set at a CRT level

At a CRT level `N₀ = ∏_{p ∈ P} p^{e_p}` (distinct primes, `e_p ≥ 1`):
* a single residue class `{ρ}` is the CRT product of its local singletons
  (`localRestrictionSet_localSingletonSets`), by the Chinese remainder theorem;
* the tube mass of an arbitrary residue set `R` is the sum of the tube masses of its classes, at every
  level divisible by `N₀` (`restrictedTube_eq_sum_singleton`), since the counted residues split by
  their class;
* hence every residue set has one tube limit along every divisibility-cofinal width sequence
  (`exists_forall_tendsto_mul_residueTube_of_eventually_dvd`, rank at least four, `M ≠ 0`).
No residue representative, level or normalization is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- CRT: a residue modulo `∏_P p^{e_p}` is determined by its reductions modulo the `p^{e_p}`. -/
theorem eq_of_forall_castHom_eq (P : Finset ℕ) (e : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a b : ZMod (localRestrictionLevel P e))
    (h : ∀ p (hp : p ∈ P), ZMod.castHom (primePow_dvd_localRestrictionLevel hp) (ZMod (p ^ e p)) a =
      ZMod.castHom (primePow_dvd_localRestrictionLevel hp) (ZMod (p ^ e p)) b) : a = b := by
  haveI : NeZero (localRestrictionLevel P e) := ⟨localRestrictionLevel_ne_zero hP⟩
  rw [← sub_eq_zero]
  have hdvd : ∀ p ∈ P, ((p ^ e p : ℕ) : ℤ) ∣ ((a - b).val : ℤ) := by
    intro p hp
    have hp' := h p hp
    rw [← sub_eq_zero, ← map_sub, ZMod.castHom_apply, ZMod.cast_eq_val,
      ZMod.natCast_eq_zero_iff] at hp'
    exact Int.natCast_dvd_natCast.2 hp'
  have hcop : (P : Set ℕ).Pairwise (Function.onFun IsCoprime fun p ↦ ((p ^ e p : ℕ) : ℤ)) := by
    intro p hp q hq hpq
    exact Nat.isCoprime_iff_coprime.2
      (Nat.coprime_pow_primes _ _ (hP p hp) (hP q hq) hpq)
  have hprod := Finset.prod_dvd_of_coprime hcop hdvd
  rw [← Nat.cast_prod] at hprod
  have hN : localRestrictionLevel P e ∣ (a - b).val := Int.natCast_dvd_natCast.1 hprod
  have hlt := (a - b).val_lt
  have h0 : (a - b).val = 0 := Nat.eq_zero_of_dvd_of_lt hN hlt
  exact (ZMod.val_eq_zero _).1 h0

/-- The local singletons of a residue vector at a CRT level (the whole set away from `P`). -/
def localSingletonSets (P : Finset ℕ) (e : ℕ → ℕ) (ρ : Fin n → ZMod (localRestrictionLevel P e)) :
    ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)) :=
  fun p ↦ {w | ∀ hp : p ∈ P,
    w = fun i ↦ ZMod.castHom (primePow_dvd_localRestrictionLevel hp) (ZMod (p ^ e p)) (ρ i)}

/-- A single residue class is the CRT product of its local singletons. -/
theorem localRestrictionSet_localSingletonSets (P : Finset ℕ) (e : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ρ : Fin n → ZMod (localRestrictionLevel P e)) :
    localRestrictionSet P e (localSingletonSets P e ρ) = {ρ} := by
  ext w
  simp only [localRestrictionSet, localSingletonSets, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hw
    funext i
    refine eq_of_forall_castHom_eq P e hP _ _ fun p hp ↦ ?_
    exact congrFun (hw p hp hp) i
  · rintro rfl p hp _
    rfl

set_option maxHeartbeats 1600000 in
/-- The tube mass of a residue set is the sum over its classes, at every level divisible by `N₀`. -/
theorem restrictedTube_eq_sum_singleton (L : PositiveDefiniteIntegralLattice n) {N₀ m : ℕ} [NeZero N₀]
    (hm : m ≠ 0) (hdvd : N₀ ∣ m) (R : Finset (Fin n → ZMod N₀)) (M : ℤ) :
    (∫ x : Fin n → RationalFiniteAdele,
        residueRestrictedIndicator n N₀ (R : Set (Fin n → ZMod N₀)) x *
          rationalFiniteAdeleIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
              (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      ∑ ρ ∈ R,
        ∫ x : Fin n → RationalFiniteAdele,
          residueRestrictedIndicator n N₀ {ρ} x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
  classical
  haveI : NeZero m := ⟨hm⟩
  rw [L.measure_restrictedCongruenceSet_eq_residueCount hm hdvd _ M]
  simp_rw [L.measure_restrictedCongruenceSet_eq_residueCount hm hdvd _ M]
  rw [← Finset.mul_sum]
  congr 1
  let red : (Fin n → ZMod m) → (Fin n → ZMod N₀) := fun z i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)
  let Q : (Fin n → ZMod m) → Prop := fun z ↦ L.zmodQuadForm m z = ((M : ℤ) : ZMod m)
  change (Nat.card {z // Q z ∧ red z ∈ (R : Set (Fin n → ZMod N₀))} : ℂ) =
    ∑ ρ ∈ R, (Nat.card {z // Q z ∧ red z ∈ ({ρ} : Set (Fin n → ZMod N₀))} : ℂ)
  have hsplit : {z // Q z ∧ red z ∈ (R : Set (Fin n → ZMod N₀))} ≃
      Σ ρ : R, {z // Q z ∧ red z ∈ ({ρ.1} : Set (Fin n → ZMod N₀))} :=
    { toFun := fun z ↦ ⟨⟨red z.1, z.2.2⟩, ⟨z.1, z.2.1, rfl⟩⟩
      invFun := fun w ↦ ⟨w.2.1, w.2.2.1, by
        have h : red w.2.1 = w.1.1 := w.2.2.2
        change red w.2.1 ∈ (R : Set (Fin n → ZMod N₀))
        rw [h]
        exact w.1.2⟩
      left_inv := fun z ↦ rfl
      right_inv := by
        rintro ⟨⟨ρ, hρ⟩, ⟨z, hz, hzρ⟩⟩
        have h : red z = ρ := hzρ
        subst h
        rfl }
  rw [Nat.card_congr hsplit, Nat.card_sigma, Nat.cast_sum]
  exact (Finset.sum_coe_sort R fun ρ ↦
    (Nat.card {z // Q z ∧ red z ∈ ({ρ} : Set (Fin n → ZMod N₀))} : ℂ))

set_option maxHeartbeats 2000000 in
/-- Every residue set at a CRT level has one tube limit along all divisibility-cofinal widths
(rank at least four, `M ≠ 0`). -/
theorem exists_forall_tendsto_mul_residueTube_of_eventually_dvd (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) (P : Finset ℕ) (e : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    (R : Set (Fin (n + 1) → ZMod (localRestrictionLevel P e))) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    ∃ D : ℂ, ∀ (m : ℕ → ℕ), (∀ k, m k ≠ 0) → (∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) →
      Tendsto (fun k : ℕ ↦ ((m k : ℕ) : ℂ) *
        ∫ x : Fin (n + 1) → RationalFiniteAdele,
          residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) R x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((m k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1)) atTop (𝓝 D) := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  classical
  have hsing : ∀ ρ : Fin (n + 1) → ZMod (localRestrictionLevel P e), ∃ D : ℂ,
      ∀ (m : ℕ → ℕ), (∀ k, m k ≠ 0) → (∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) →
      Tendsto (fun k : ℕ ↦ ((m k : ℕ) : ℂ) *
        ∫ x : Fin (n + 1) → RationalFiniteAdele,
          residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) {ρ} x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((m k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1)) atTop (𝓝 D) := by
    intro ρ
    have h := L.exists_forall_tendsto_mul_restrictedTube_of_eventually_dvd hn hM P e
      (localSingletonSets P e ρ) hP
    rwa [localRestrictionSet_localSingletonSets P e (fun p hp ↦ (hP p hp).1) ρ] at h
  choose D hD using hsing
  refine ⟨∑ ρ ∈ R.toFinset, D ρ, fun m hm0 hdvd ↦ ?_⟩
  have hsum := tendsto_finset_sum R.toFinset fun ρ _ ↦ hD ρ m hm0 hdvd
  refine hsum.congr' ?_
  filter_upwards [hdvd (localRestrictionLevel P e) (NeZero.ne _)] with k hk
  have hR : R = ((R.toFinset : Finset _) : Set (Fin (n + 1) → ZMod (localRestrictionLevel P e))) :=
    (Set.coe_toFinset R).symm
  conv_rhs => rw [hR]
  rw [L.restrictedTube_eq_sum_singleton (hm0 k) hk R.toFinset M, Finset.mul_sum]

end PositiveDefiniteIntegralLattice
