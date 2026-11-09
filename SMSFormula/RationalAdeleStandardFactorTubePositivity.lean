import SMSFormula.RationalAdeleResidueClassFiberPoint
import SMSFormula.RationalAdeleStandardFactorTubeLimit

/-!
# Positivity of the tube limit on the finite fiber

Let `ψ` be a real standard finite factor (carried by `(1/c)Ẑⁿ`, periodic modulo `dẐⁿ`) that is
nonnegative on the finite fiber `{Q_f = M}`, `M ≠ 0`, lattice rank at least four.  Then the limit of
its `k!`-tube masses has nonnegative real part (`re_nonneg_of_tendsto_finiteTubeMass_of_fiber_nonneg`).

The proof follows `RationalAdeleStandardFactorTubeLimit`: after dilation the tube mass is
`c^n/c² · Σ_ρ ψ̃(ρ) · T_ρ`, where each class tube `T_ρ` is a nonnegative real (a residue count) with
limit `D_ρ ≥ 0`. By the local-to-global dichotomy, `D_ρ ≠ 0` forces the class `ρ` to contain an
integral point of `{Q_f = c²M}`, on which `ψ̃ = ψ(·/c) ≥ 0`; so every term is nonnegative. Nothing
is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The class tube mass is a nonnegative real number. -/
theorem exists_nonneg_real_residueTube (L : PositiveDefiniteIntegralLattice n) {N₀ m : ℕ} [NeZero N₀]
    (hm : m ≠ 0) (hdvd : N₀ ∣ m) (ρ : Fin n → ZMod N₀) (M : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ((m : ℕ) : ℂ) *
        ∫ x : Fin n → RationalFiniteAdele,
          residueRestrictedIndicator n N₀ {ρ} x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n = r := by
  rw [L.measure_restrictedCongruenceSet_eq_residueCount hm hdvd _ M]
  refine ⟨(m : ℝ) * (((m : ℝ) ^ n)⁻¹ * (Nat.card {z : Fin n → ZMod m //
      L.zmodQuadForm m z = ((M : ℤ) : ZMod m) ∧
        (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ ({ρ} : Set (Fin n → ZMod N₀))} : ℝ)),
    by positivity, ?_⟩
  push_cast
  ring

theorem isClosed_nonnegReal : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

set_option maxHeartbeats 4000000 in
/-- The tube limit of a standard factor nonnegative on the finite fiber has nonnegative real
part (rank at least four, `M ≠ 0`). -/
theorem re_nonneg_of_tendsto_finiteTubeMass_of_fiber_nonneg (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {ψ : (Fin (n + 1) → RationalFiniteAdele) → ℝ}
    (hcar : IsStandardCarried c (fun x ↦ (ψ x : ℂ))) (hper : IsStandardPeriodic d (fun x ↦ (ψ x : ℂ)))
    (hpos : ∀ x, L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x =
      algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ) → 0 ≤ ψ x)
    {D : ℂ} (hD : Tendsto (fun k ↦ L.finiteTubeMass (fun x ↦ (ψ x : ℂ)) (Nat.factorial k) M)
      atTop (𝓝 D)) :
    0 ≤ D.re := by
  classical
  set g : (Fin (n + 1) → RationalFiniteAdele) → ℂ := fun x ↦ (ψ x : ℂ) with hgdef
  set gt : (Fin (n + 1) → RationalFiniteAdele) → ℂ :=
    fun y ↦ g (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ y) with hgt
  have hcar1 : IsStandardCarried 1 gt := isStandardCarried_one_comp_scale hc hcar
  set P := (c * d).primeFactors with hPdef
  set e := (c * d).factorization with hedef
  have hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p := fun p hp ↦
    ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp)
        (mul_ne_zero hc hd) (Nat.dvd_of_mem_primeFactors hp))⟩
  have hlevel : localRestrictionLevel P e = c * d :=
    Nat.factorization_prod_pow_eq_self (mul_ne_zero hc hd)
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  have hper' : IsStandardPeriodic (localRestrictionLevel P e) gt := by
    rw [hlevel]; exact isStandardPeriodic_mul_comp_scale hc hper
  have hM' : (c : ℤ) ^ 2 * M ≠ 0 := mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hc)) hM
  have hsing := fun ρ : Fin (n + 1) → ZMod (localRestrictionLevel P e) ↦
    L.exists_forall_tendsto_mul_residueTube_of_eventually_dvd hn hM' P e hP {ρ}
  choose Dρ hDρ using hsing
  set m : ℕ → ℕ := fun k ↦ c ^ 2 * Nat.factorial k with hmdef
  have hm0 : ∀ k, m k ≠ 0 := fun k ↦ mul_ne_zero (pow_ne_zero 2 hc) (Nat.factorial_ne_zero k)
  have hmdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k := fun N hN ↦ by
    filter_upwards [eventually_ge_atTop N] with k hk
    exact (Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hk).mul_left _
  have hcC : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  -- the decomposed limit
  have hlim := (tendsto_finset_sum Finset.univ fun ρ _ ↦
    (hDρ ρ m hm0 hmdvd).const_mul (gt (residueFiniteAdeleLift _ ρ))).const_mul ((c : ℂ) ^ (n + 1) / (c : ℂ) ^ 2)
  have hlim' : Tendsto (fun k ↦ L.finiteTubeMass g (Nat.factorial k) M) atTop
      (𝓝 ((c : ℂ) ^ (n + 1) / (c : ℂ) ^ 2 * ∑ ρ, gt (residueFiniteAdeleLift _ ρ) * Dρ ρ)) := by
    refine hlim.congr fun k ↦ ?_
    have hdil := L.finiteTubeMass_mul_sq_eq_dilate g hc (Nat.factorial k) M
    have hT : L.finiteTubeMass g (Nat.factorial k) M =
        (c : ℂ) ^ (n + 1) / (c : ℂ) ^ 2 * L.finiteTubeMass gt (c ^ 2 * Nat.factorial k)
          ((c : ℤ) ^ 2 * M) := by
      rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hcC), hdil]
    rw [hT]
    congr 1
    unfold finiteTubeMass
    have hdecomp : ∀ x, gt x = ∑ ρ, gt (residueFiniteAdeleLift _ ρ) *
        residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) {ρ} x :=
      eq_sum_residueRestrictedIndicator hcar1 hper'
    have hint : (fun x ↦ gt x * rationalFiniteAdeleIntegralIndicator
        (algebraMap ℚ RationalFiniteAdele (((c ^ 2 * Nat.factorial k : ℕ) : ℚ))⁻¹ *
          (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
            algebraMap ℚ RationalFiniteAdele ((((c : ℤ) ^ 2 * M : ℤ)) : ℚ)))) =
        fun x ↦ ∑ ρ, gt (residueFiniteAdeleLift _ ρ) *
          residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) {ρ} x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((c ^ 2 * Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((((c : ℤ) ^ 2 * M : ℤ)) : ℚ))) := by
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
  have hDeq := tendsto_nhds_unique hD hlim'
  -- each class limit is a nonnegative real, and vanishes unless the class meets the fiber
  have hclass : ∀ ρ : Fin (n + 1) → ZMod (localRestrictionLevel P e),
      (Dρ ρ).im = 0 ∧ 0 ≤ (Dρ ρ).re ∧ (Dρ ρ ≠ 0 → 0 ≤ (gt (residueFiniteAdeleLift _ ρ)).re) := by
    intro ρ
    have hmem : Dρ ρ ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
      refine isClosed_nonnegReal.mem_of_tendsto (hDρ ρ m hm0 hmdvd) ?_
      filter_upwards [hmdvd (localRestrictionLevel P e) (NeZero.ne _)] with k hk
      obtain ⟨r, hr0, hr⟩ := L.exists_nonneg_real_residueTube (hm0 k) hk ρ ((c : ℤ) ^ 2 * M)
      rw [hr]
      exact ⟨Complex.ofReal_im r, by rw [Complex.ofReal_re]; exact hr0⟩
    refine ⟨hmem.1, hmem.2, fun hne ↦ ?_⟩
    rcases L.exists_fiberPoint_or_eventually_residueTube_eq_zero ((c : ℤ) ^ 2 * M) P e hP ρ
      hm0 hmdvd with ⟨y, hyρ, hyQ⟩ | hzero
    · -- `gt` is constant on the class, and nonnegative at the fiber point `y/c`
      have hval : gt (residueFiniteAdeleLift _ ρ) = gt (fun i ↦ ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) := by
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
      rw [hval]
      change 0 ≤ ((ψ (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹
        (fun i ↦ ((y i : IntegralFiniteAdele) : RationalFiniteAdele))) : ℝ) : ℂ).re
      rw [Complex.ofReal_re]
      refine hpos _ ?_
      rw [finiteAdelicQuadraticFormValue_coordinateScale, hyQ]
      have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc
      rw [← map_mul]
      congr 1
      push_cast
      field_simp
    · exact absurd (tendsto_nhds_unique (hDρ ρ m hm0 hmdvd)
        (tendsto_const_nhds.congr' (hzero.mono fun k hk ↦ hk.symm))) hne
  -- conclude
  rw [hDeq]
  have hC : (c : ℂ) ^ (n + 1) / (c : ℂ) ^ 2 = (((c : ℝ) ^ (n + 1) / (c : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hC, Complex.re_ofReal_mul]
  refine mul_nonneg (by positivity) ?_
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun ρ _ ↦ ?_
  obtain ⟨him, hre, himp⟩ := hclass ρ
  have hgreal : gt (residueFiniteAdeleLift _ ρ) = ((gt (residueFiniteAdeleLift _ ρ)).re : ℂ) := by
    change ((ψ _ : ℝ) : ℂ) = (((ψ _ : ℝ) : ℂ).re : ℂ)
    rw [Complex.ofReal_re]
  rw [hgreal, Complex.re_ofReal_mul]
  by_cases h0 : Dρ ρ = 0
  · rw [h0, Complex.zero_re, mul_zero]
  · exact mul_nonneg (himp h0) hre

end PositiveDefiniteIntegralLattice
