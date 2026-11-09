import SMSFormula.RationalAdeleStandardFactorTubePositivity

/-!
# The tube limit of the dilated lattice indicator

* `exists_forall_tendsto_finiteTubeMass_of_carried_one`: a finite factor carried by `Ẑⁿ` and periodic
  modulo `NẐⁿ` has one tube limit along every divisibility-cofinal width sequence (residue
  decomposition at the CRT level `N`, `RationalAdeleResidueTubeDecomposition`);
* `tendsto_finiteTubeMass_dilatedIntegral_of_int`: for `k ≠ 0` and an integer `m ≠ 0`, the `j!`-tube
  masses of `x ↦ 1_Ẑ(x/k)` at `k² m` converge to `k²/kⁿ · ∏'_p δ_p(m)` (dilation law along the cofinal
  widths `k² j!` plus width independence);
* `tendsto_finiteTubeMass_dilatedIntegral_of_not_int`: if `k² b` is an integer but `b` is not, they
  converge to `0` (a fiber point of the class would give an integral vector of norm `b`).
Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option maxHeartbeats 2000000 in
/-- Width independence for `Ẑⁿ`-carried periodic finite factors. -/
theorem exists_forall_tendsto_finiteTubeMass_of_carried_one (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) {N : ℕ} (hN : N ≠ 0)
    {g : (Fin (n + 1) → RationalFiniteAdele) → ℂ} (hcar : IsStandardCarried 1 g)
    (hper : IsStandardPeriodic N g) :
    ∃ D : ℂ, ∀ m : ℕ → ℕ, (∀ k, m k ≠ 0) → (∀ N' : ℕ, N' ≠ 0 → ∀ᶠ k in atTop, N' ∣ m k) →
      Tendsto (fun k ↦ L.finiteTubeMass g (m k) M) atTop (𝓝 D) := by
  classical
  set P := N.primeFactors with hPdef
  set e := N.factorization with hedef
  have hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p := fun p hp ↦
    ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hN
        (Nat.dvd_of_mem_primeFactors hp))⟩
  have hlevel : localRestrictionLevel P e = N := Nat.factorization_prod_pow_eq_self hN
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  have hper' : IsStandardPeriodic (localRestrictionLevel P e) g := by rw [hlevel]; exact hper
  have hsing := fun ρ : Fin (n + 1) → ZMod (localRestrictionLevel P e) ↦
    L.exists_forall_tendsto_mul_residueTube_of_eventually_dvd hn hM P e hP {ρ}
  choose D hD using hsing
  refine ⟨∑ ρ, g (residueFiniteAdeleLift _ ρ) * D ρ, fun m hm0 hmdvd ↦ ?_⟩
  refine (tendsto_finset_sum Finset.univ fun ρ _ ↦ (hD ρ m hm0 hmdvd).const_mul
    (g (residueFiniteAdeleLift _ ρ))).congr fun k ↦ ?_
  unfold finiteTubeMass
  have hdecomp : ∀ x, g x = ∑ ρ, g (residueFiniteAdeleLift _ ρ) *
      residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) {ρ} x :=
    eq_sum_residueRestrictedIndicator hcar hper'
  have hint : (fun x ↦ g x * rationalFiniteAdeleIntegralIndicator
      (algebraMap ℚ RationalFiniteAdele (((m k : ℕ) : ℚ))⁻¹ *
        (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
          algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))) =
      fun x ↦ ∑ ρ, g (residueFiniteAdeleLift _ ρ) *
        residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) {ρ} x *
          rationalFiniteAdeleIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele (((m k : ℕ) : ℚ))⁻¹ *
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

/-- The finite quadratic value of an integral vector is integral. -/
theorem finiteAdelicQuadraticFormValue_mem_integral (L : PositiveDefiniteIntegralLattice n)
    {x : Fin n → RationalFiniteAdele} (hx : x ∈ integralFiniteAdeleVectors n) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x ∈ integralFiniteAdeleSubring := by
  unfold finiteAdelicQuadraticFormValue dotProduct Matrix.mulVec
  refine Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (hx i) (Subring.sum_mem _ fun j _ ↦ ?_)
  refine Subring.mul_mem _ ?_ (hx j)
  have h : L.rationalQuadraticSpaceMatrix.finiteAdelicFormMatrix i j =
      algebraMap ℚ RationalFiniteAdele ((L.pairingMatrix i j : ℤ) : ℚ) := by
    simp [RationalQuadraticSpaceMatrix.finiteAdelicFormMatrix, rationalQuadraticSpaceMatrix_pairingMatrix,
      PositiveDefiniteIntegralLattice.rationalFormMatrix]
  change L.rationalQuadraticSpaceMatrix.finiteAdelicFormMatrix i j ∈ _
  rw [h]
  exact (rational_mem_integralFiniteAdeleSubring_iff _).2 ⟨L.pairingMatrix i j, rfl⟩

/-- The dilated lattice indicator `x ↦ 1_Ẑ(x/k)`. -/
def dilatedIntegralIndicator (n k : ℕ) (x : Fin n → RationalFiniteAdele) : ℂ :=
  rationalFiniteAdeleVectorIntegralIndicator (rationalFiniteAdeleCoordinateScale ((k : ℚ))⁻¹ x)

theorem isStandardCarried_integralIndicator_one :
    IsStandardCarried 1 (rationalFiniteAdeleVectorIntegralIndicator (n := n)) := by
  have h := isStandardCarried_residueRestrictedIndicator (n := n) 1 Set.univ
  rwa [residueRestrictedIndicator_univ] at h

theorem isStandardPeriodic_integralIndicator_one :
    IsStandardPeriodic 1 (rationalFiniteAdeleVectorIntegralIndicator (n := n)) := by
  have h := isStandardPeriodic_residueRestrictedIndicator (n := n) 1 Set.univ
  rwa [residueRestrictedIndicator_univ] at h

theorem isStandardCarried_dilatedIntegralIndicator {k : ℕ} (hk : k ≠ 0) :
    IsStandardCarried 1 (dilatedIntegralIndicator n k) :=
  isStandardCarried_one_comp_scale hk (isStandardCarried_integralIndicator_one.mono (one_dvd k))

theorem isStandardPeriodic_dilatedIntegralIndicator {k : ℕ} (hk : k ≠ 0) :
    IsStandardPeriodic k (dilatedIntegralIndicator n k) := by
  have h := isStandardPeriodic_mul_comp_scale (c := k) hk
    (isStandardPeriodic_integralIndicator_one (n := n))
  rwa [mul_one] at h

set_option maxHeartbeats 2000000 in
/-- The dilated lattice tube at an integer: `T_{j!}(1_Ẑ(·/k))(k² m) → k²/kⁿ⁺¹ · ∏'_p δ_p(m)`. -/
theorem tendsto_finiteTubeMass_dilatedIntegral_of_int (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≠ 0) {m : ℤ} (hm : m ≠ 0) :
    Tendsto (fun j ↦ L.finiteTubeMass (dilatedIntegralIndicator (n + 1) k) (Nat.factorial j)
        ((k : ℤ) ^ 2 * m)) atTop
      (𝓝 ((k : ℂ) ^ 2 / (k : ℂ) ^ (n + 1) * ((∏' p : Nat.Primes, L.localResidueDensity m p : ℝ) : ℂ))) := by
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hM' : (k : ℤ) ^ 2 * m ≠ 0 := mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hk)) hm
  obtain ⟨D, hD⟩ := L.exists_forall_tendsto_finiteTubeMass_of_carried_one hn hM' hk
    (isStandardCarried_dilatedIntegralIndicator hk) (isStandardPeriodic_dilatedIntegralIndicator hk)
  -- along the cofinal widths `k² j!` the dilation law identifies the limit
  have hm0 : ∀ j, k ^ 2 * Nat.factorial j ≠ 0 := fun j ↦
    mul_ne_zero (pow_ne_zero 2 hk) (Nat.factorial_ne_zero j)
  have hmdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ j in atTop, N ∣ k ^ 2 * Nat.factorial j := fun N hN ↦ by
    filter_upwards [eventually_ge_atTop N] with j hj
    exact (Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hj).mul_left _
  have hfull := L.tendsto_factorial_mul_congruenceIntegral_tprod_localResidueDensity hn hm
  have hdil : Tendsto (fun j ↦ L.finiteTubeMass (dilatedIntegralIndicator (n + 1) k)
      (k ^ 2 * Nat.factorial j) ((k : ℤ) ^ 2 * m)) atTop
      (𝓝 ((k : ℂ) ^ 2 / (k : ℂ) ^ (n + 1) * ((∏' p : Nat.Primes, L.localResidueDensity m p : ℝ) : ℂ))) := by
    refine (hfull.const_mul ((k : ℂ) ^ 2 / (k : ℂ) ^ (n + 1))).congr fun j ↦ ?_
    have h := L.finiteTubeMass_mul_sq_eq_dilate rationalFiniteAdeleVectorIntegralIndicator hk
      (Nat.factorial j) m
    have hT : L.finiteTubeMass (dilatedIntegralIndicator (n + 1) k) (k ^ 2 * Nat.factorial j)
        ((k : ℤ) ^ 2 * m) = (k : ℂ) ^ 2 / (k : ℂ) ^ (n + 1) *
          L.finiteTubeMass rationalFiniteAdeleVectorIntegralIndicator (Nat.factorial j) m := by
      rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hkC), mul_comm ((k : ℂ) ^ 2), h, mul_comm]
      rfl
    rw [hT]
    rfl
  have hD' := hD (fun j ↦ k ^ 2 * Nat.factorial j) hm0 hmdvd
  rw [tendsto_nhds_unique hD' hdil] at hD
  exact hD (fun j ↦ Nat.factorial j) (fun j ↦ Nat.factorial_ne_zero j) fun N hN ↦ by
    filter_upwards [eventually_ge_atTop N] with j hj
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hj

set_option maxHeartbeats 2000000 in
/-- The dilated lattice tube at a non-integral shell vanishes: if `k² b = M` is an integer but `b`
is not, the `j!`-tube masses of `1_Ẑ(·/k)` at `M` converge to `0`. -/
theorem tendsto_finiteTubeMass_dilatedIntegral_of_not_int (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {k : ℕ} (hk : k ≠ 0) {M : ℤ} (hM : M ≠ 0) {b : ℚ}
    (hb : ((k : ℚ)) ^ 2 * b = M) (hbint : b ∉ (algebraMap ℤ ℚ).range) :
    Tendsto (fun j ↦ L.finiteTubeMass (dilatedIntegralIndicator (n + 1) k) (Nat.factorial j) M)
      atTop (𝓝 0) := by
  classical
  set g := dilatedIntegralIndicator (n + 1) k with hgdef
  have hcar1 : IsStandardCarried 1 g := isStandardCarried_dilatedIntegralIndicator (n := n + 1) hk
  set P := k.primeFactors with hPdef
  set e := k.factorization with hedef
  have hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p := fun p hp ↦
    ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hk
        (Nat.dvd_of_mem_primeFactors hp))⟩
  have hlevel : localRestrictionLevel P e = k := Nat.factorization_prod_pow_eq_self hk
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  have hper' : IsStandardPeriodic (localRestrictionLevel P e) g := by
    rw [hlevel]; exact isStandardPeriodic_dilatedIntegralIndicator hk
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
      -- `g` is constant on the class, so `y/k` is integral and has norm `b`
      have hval : g (residueFiniteAdeleLift _ ρ) = g (fun i ↦ ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) := by
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
          by_cases h : σ = ρ
          · rw [if_pos h.symm, if_pos h]
          · rw [if_neg (Ne.symm h), if_neg h]
        simp_rw [hind, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      rw [hval] at hg0
      set w := rationalFiniteAdeleCoordinateScale ((k : ℚ))⁻¹
        (fun i ↦ ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) with hwdef
      have hw : w ∈ integralFiniteAdeleVectors (n + 1) := by
        by_contra hw
        exact hg0 (by rw [hgdef, dilatedIntegralIndicator, ← hwdef,
          rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hw])
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
