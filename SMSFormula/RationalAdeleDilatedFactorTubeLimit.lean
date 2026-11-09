import SMSFormula.RationalAdeleDilatedLatticeTubeLimit

/-!
# Tube limits of dilated `Ẑⁿ`-carried finite factors

For a finite factor `h` carried by `Ẑⁿ` and periodic modulo `NẐⁿ`, and `k ≠ 0`:

* `tendsto_finiteTubeMass_comp_scale_of_tendsto`: if the `j!`-tube masses of `h` at an integer `m ≠ 0` converge
  to `D`, those of `h(·/k)` at `k² m` converge to `k²/kⁿ⁺¹ · D` (width independence plus the dilation law along
  the cofinal widths `k² j!`);
* `tendsto_finiteTubeMass_comp_scale_of_not_int`: if `k² b = M` is an integer but `b` is not, the `j!`-tube masses
  of `h(·/k)` at `M` converge to `0` (a fiber point of a class where `h(·/k)` is nonzero would give an integral
  vector of norm `b`).
These generalize the lattice-indicator statements of `RationalAdeleDilatedLatticeTubeLimit` verbatim.
Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option maxHeartbeats 2000000 in
/-- The dilated factor tube at an integer: `T_{j!}(h(·/k))(k² m) → k²/kⁿ⁺¹ · lim T_{j!}(h)(m)`. -/
theorem tendsto_finiteTubeMass_comp_scale_of_tendsto (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n)
    {h : (Fin (n + 1) → RationalFiniteAdele) → ℂ} {N : ℕ} (hN : N ≠ 0) (hcar : IsStandardCarried 1 h)
    (hper : IsStandardPeriodic N h) {k : ℕ} (hk : k ≠ 0) {m : ℤ} (hm : m ≠ 0) {D : ℂ}
    (hD0 : Tendsto (fun j ↦ L.finiteTubeMass h (Nat.factorial j) m) atTop (𝓝 D)) :
    Tendsto (fun j ↦ L.finiteTubeMass (fun y ↦ h (rationalFiniteAdeleCoordinateScale ((k : ℚ))⁻¹ y))
        (Nat.factorial j) ((k : ℤ) ^ 2 * m)) atTop (𝓝 ((k : ℂ) ^ 2 / (k : ℂ) ^ (n + 1) * D)) := by
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hM' : (k : ℤ) ^ 2 * m ≠ 0 := mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hk)) hm
  obtain ⟨D₁, hD⟩ := L.exists_forall_tendsto_finiteTubeMass_of_carried_one hn hM' (mul_ne_zero hk hN)
    (isStandardCarried_one_comp_scale hk (hcar.mono (one_dvd k)))
    (isStandardPeriodic_mul_comp_scale hk hper)
  have hm0 : ∀ j, k ^ 2 * Nat.factorial j ≠ 0 := fun j ↦
    mul_ne_zero (pow_ne_zero 2 hk) (Nat.factorial_ne_zero j)
  have hmdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ j in atTop, N ∣ k ^ 2 * Nat.factorial j := fun N hN ↦ by
    filter_upwards [eventually_ge_atTop N] with j hj
    exact (Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hj).mul_left _
  have hdil : Tendsto (fun j ↦ L.finiteTubeMass
      (fun y ↦ h (rationalFiniteAdeleCoordinateScale ((k : ℚ))⁻¹ y))
      (k ^ 2 * Nat.factorial j) ((k : ℤ) ^ 2 * m)) atTop
      (𝓝 ((k : ℂ) ^ 2 / (k : ℂ) ^ (n + 1) * D)) := by
    refine (hD0.const_mul ((k : ℂ) ^ 2 / (k : ℂ) ^ (n + 1))).congr fun j ↦ ?_
    have h2 := L.finiteTubeMass_mul_sq_eq_dilate h hk (Nat.factorial j) m
    rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hkC)]
    linear_combination h2
  have hD' := hD (fun j ↦ k ^ 2 * Nat.factorial j) hm0 hmdvd
  rw [tendsto_nhds_unique hD' hdil] at hD
  exact hD (fun j ↦ Nat.factorial j) (fun j ↦ Nat.factorial_ne_zero j) fun N hN ↦ by
    filter_upwards [eventually_ge_atTop N] with j hj
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hj

set_option maxHeartbeats 2000000 in
/-- The dilated factor tube at a non-integral shell vanishes: if `k² b = M` is an integer but `b` is not,
the `j!`-tube masses of `h(·/k)` at `M` converge to `0`. -/
theorem tendsto_finiteTubeMass_comp_scale_of_not_int (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n)
    {h : (Fin (n + 1) → RationalFiniteAdele) → ℂ} {N : ℕ} (hN : N ≠ 0) (hcar : IsStandardCarried 1 h)
    (hper : IsStandardPeriodic N h) {k : ℕ} (hk : k ≠ 0) {M : ℤ} (hM : M ≠ 0) {b : ℚ}
    (hb : ((k : ℚ)) ^ 2 * b = M) (hbint : b ∉ (algebraMap ℤ ℚ).range) :
    Tendsto (fun j ↦ L.finiteTubeMass (fun y ↦ h (rationalFiniteAdeleCoordinateScale ((k : ℚ))⁻¹ y))
      (Nat.factorial j) M) atTop (𝓝 0) := by
  classical
  set g := fun y ↦ h (rationalFiniteAdeleCoordinateScale ((k : ℚ))⁻¹ y) with hgdef
  have hcar1 : IsStandardCarried 1 g := isStandardCarried_one_comp_scale hk (hcar.mono (one_dvd k))
  have hkN : k * N ≠ 0 := mul_ne_zero hk hN
  set P := (k * N).primeFactors with hPdef
  set e := (k * N).factorization with hedef
  have hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p := fun p hp ↦
    ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hkN
        (Nat.dvd_of_mem_primeFactors hp))⟩
  have hlevel : localRestrictionLevel P e = k * N := Nat.factorization_prod_pow_eq_self hkN
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  have hper' : IsStandardPeriodic (localRestrictionLevel P e) g := by
    rw [hlevel]; exact isStandardPeriodic_mul_comp_scale hk hper
  have hsing := fun ρ : Fin (n + 1) → ZMod (localRestrictionLevel P e) ↦
    L.exists_forall_tendsto_mul_residueTube_of_eventually_dvd hn hM P e hP {ρ}
  choose D hD using hsing
  have hm0 : ∀ j, Nat.factorial j ≠ 0 := fun j ↦ Nat.factorial_ne_zero j
  have hmdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ j in atTop, N ∣ Nat.factorial j := fun N hN ↦ by
    filter_upwards [eventually_ge_atTop N] with j hj
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hj
  -- every class term vanishes
  have hterm : ∀ ρ, g (residueFiniteAdeleLift _ ρ) * D ρ = 0 := by
    intro ρ
    by_cases hg0 : g (residueFiniteAdeleLift _ ρ) = 0
    · rw [hg0, zero_mul]
    rcases L.exists_fiberPoint_or_eventually_residueTube_eq_zero M P e hP ρ hm0 hmdvd with
      ⟨y, hyρ, hyQ⟩ | hzero
    · exfalso
      have hval : g (residueFiniteAdeleLift _ ρ) =
          g (fun i ↦ ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) := by
        rw [eq_sum_residueRestrictedIndicator hcar1 hper' (fun i ↦ ((y i : IntegralFiniteAdele) :
          RationalFiniteAdele))]
        have hind : ∀ σ : Fin (n + 1) → ZMod (localRestrictionLevel P e),
            residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) {σ}
              (fun i ↦ ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) =
            if σ = ρ then 1 else 0 := by
          intro σ
          have hint : (fun i ↦ ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) ∈
              integralFiniteAdeleVectors (n + 1) := fun i ↦ (y i).2
          rw [residueRestrictedIndicator, dif_pos hint]
          have hy' : integralVectorResidue (n + 1) (localRestrictionLevel P e)
              (fun i ↦ ⟨((y i : IntegralFiniteAdele) : RationalFiniteAdele), hint i⟩) = ρ := hyρ
          simp only [Set.mem_singleton_iff, hy']
          by_cases hσ : σ = ρ
          · rw [if_pos hσ.symm, if_pos hσ]
          · rw [if_neg (Ne.symm hσ), if_neg hσ]
        simp_rw [hind, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      rw [hval] at hg0
      set w := rationalFiniteAdeleCoordinateScale ((k : ℚ))⁻¹
        (fun i ↦ ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) with hwdef
      have hw : w ∈ integralFiniteAdeleVectors (n + 1) := by
        by_contra hw
        refine hg0 (hcar w fun hmem ↦ hw ?_)
        have hmem' : (1 : ℕ) • w ∈ integralFiniteAdeleVectors (n + 1) := hmem
        rwa [one_smul] at hmem'
      have hQw := L.finiteAdelicQuadraticFormValue_mem_integral hw
      rw [hwdef, PositiveDefiniteIntegralLattice.finiteAdelicQuadraticFormValue_coordinateScale, hyQ, ← map_mul] at hQw
      apply hbint
      rw [← rational_mem_integralFiniteAdeleSubring_iff]
      have hcq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      have hbq : b = ((k : ℚ))⁻¹ ^ 2 * ((M : ℤ) : ℚ) := by
        rw [← hb]; field_simp
      rw [hbq]
      exact hQw
    · rw [tendsto_nhds_unique (hD ρ _ hm0 hmdvd)
        (tendsto_const_nhds.congr' (hzero.mono fun j hj ↦ hj.symm)), mul_zero]
  have hlim := tendsto_finset_sum Finset.univ fun ρ _ ↦ (hD ρ _ hm0 hmdvd).const_mul
    (g (residueFiniteAdeleLift _ ρ))
  rw [Finset.sum_eq_zero fun ρ _ ↦ hterm ρ] at hlim
  refine hlim.congr fun j ↦ ?_
  unfold finiteTubeMass
  have hdecomp : ∀ x, g x = ∑ ρ, g (residueFiniteAdeleLift _ ρ) *
      residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) {ρ} x :=
    eq_sum_residueRestrictedIndicator hcar1 hper'
  have hint : (fun x ↦ g x * rationalFiniteAdeleIntegralIndicator
      (algebraMap ℚ RationalFiniteAdele (((Nat.factorial j : ℕ) : ℚ))⁻¹ *
        (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
          algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))) =
      fun x ↦ ∑ ρ, g (residueFiniteAdeleLift _ ρ) *
        residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) {ρ} x *
          rationalFiniteAdeleIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele (((Nat.factorial j : ℕ) : ℚ))⁻¹ *
              (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ))) := by
    funext x
    rw [hdecomp x, Finset.sum_mul]
  rw [hint, integral_finset_sum _ fun ρ _ ↦ ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    ring
  · simp_rw [mul_assoc]
    exact (L.integrable_residueRestrictedIndicator_mul_tube _ _ _ _).const_mul _

end PositiveDefiniteIntegralLattice
