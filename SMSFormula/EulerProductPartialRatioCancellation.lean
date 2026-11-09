import SMSFormula.Product

/-!
# Cancelling an Euler product against a limit of partial volume ratios

Abstract bookkeeping for cancelling an Euler product against finite stabilizer volumes. Let `f, g`
be positive finite functions on the rational primes (local volumes of two lattices), `d ≥ 0` a
multipliable function (local densities), `E` a finite set `E` of primes with `f q = g q · d q` for
every `q ∉ E`, and suppose the partial ratios `∏_{q ≤ N} f / ∏_{q ≤ N} g` converge to `t`. Then

`t · ∏_{q ∈ E} d q · ∏_{q ∈ E} g q = ∏_{q ∈ E} f q · ∏'_q d q`,

i.e. the infinite Euler product cancels against the tail of the partial ratios, leaving only the
finite exceptional factors.  Nothing is chosen.
-/

noncomputable section

open Filter Topology
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

/-- The rational-prime cutoffs exhaust the rational primes. -/
theorem tendsto_rationalPrimesUpTo_atTop :
    Tendsto rationalPrimesUpTo atTop (atTop : Filter (Finset {p : ℕ // Nat.Prime p})) := by
  refine Filter.tendsto_atTop_atTop.2 fun s ↦ ⟨s.sup (fun q ↦ q.1), fun N hN q hq ↦ ?_⟩
  rw [mem_rationalPrimesUpTo_iff]
  exact (Finset.le_sup (f := fun q : {p : ℕ // Nat.Prime p} ↦ q.1) hq).trans hN

/-- A multipliable real function is the limit of its partial products over the prime cutoffs. -/
theorem tendsto_prod_rationalPrimesUpTo_tprod {d : {p : ℕ // Nat.Prime p} → ℝ}
    (hd : Multipliable d) :
    Tendsto (fun N ↦ ∏ q ∈ rationalPrimesUpTo N, d q) atTop (𝓝 (∏' q, d q)) :=
  hd.hasProd.comp tendsto_rationalPrimesUpTo_atTop

/-- Euler product cancellation against a limit of partial ratios. -/
theorem mul_prod_eq_prod_mul_tprod_of_partialRatio
    {f g : {p : ℕ // Nat.Prime p} → ℝ≥0∞} {d : {p : ℕ // Nat.Prime p} → ℝ}
    (E : Finset {p : ℕ // Nat.Prime p})
    (hf : ∀ q, f q ≠ ⊤) (hg0 : ∀ q, g q ≠ 0) (hgt : ∀ q, g q ≠ ⊤)
    (hd0 : ∀ q, 0 ≤ d q) (hd : Multipliable d)
    (hfg : ∀ q ∉ E, f q = g q * ENNReal.ofReal (d q))
    {t : ℝ≥0∞}
    (ht : Tendsto (fun N ↦ (∏ q ∈ rationalPrimesUpTo N, f q) / ∏ q ∈ rationalPrimesUpTo N, g q)
      atTop (𝓝 t)) :
    t * ENNReal.ofReal (∏ q ∈ E, d q) * ∏ q ∈ E, g q =
      (∏ q ∈ E, f q) * ENNReal.ofReal (∏' q, d q) := by
  classical
  have hsub : ∀ᶠ N in atTop, E ⊆ rationalPrimesUpTo N :=
    tendsto_rationalPrimesUpTo_atTop (Filter.eventually_ge_atTop E)
  have hkey : ∀ᶠ N in atTop,
      (∏ q ∈ rationalPrimesUpTo N, f q) / (∏ q ∈ rationalPrimesUpTo N, g q) *
          ENNReal.ofReal (∏ q ∈ E, d q) * ∏ q ∈ E, g q =
        (∏ q ∈ E, f q) * ENNReal.ofReal (∏ q ∈ rationalPrimesUpTo N, d q) := by
    filter_upwards [hsub] with N hN
    set S := rationalPrimesUpTo N
    have hsplit : ∀ h : {p : ℕ // Nat.Prime p} → ℝ≥0∞,
        ∏ q ∈ S, h q = (∏ q ∈ E, h q) * ∏ q ∈ S \ E, h q := fun h ↦ by
      rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hN]
    set X := ∏ q ∈ S \ E, g q
    set D := ∏ q ∈ S \ E, ENNReal.ofReal (d q)
    have hfS : ∏ q ∈ S, f q = (∏ q ∈ E, f q) * (X * D) := by
      rw [hsplit f, ← Finset.prod_mul_distrib]
      congr 1
      exact Finset.prod_congr rfl fun q hq ↦ hfg q (Finset.mem_sdiff.mp hq).2
    have hgS : ∏ q ∈ S, g q = (∏ q ∈ E, g q) * X := hsplit g
    have hdS : ENNReal.ofReal (∏ q ∈ S, d q) = ENNReal.ofReal (∏ q ∈ E, d q) * D := by
      rw [ENNReal.ofReal_prod_of_nonneg fun q _ ↦ hd0 q,
        ENNReal.ofReal_prod_of_nonneg fun q _ ↦ hd0 q]
      exact hsplit (fun q ↦ ENNReal.ofReal (d q))
    have hP0 : (∏ q ∈ E, g q) * X ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun q _ ↦ hg0 q)
        (Finset.prod_ne_zero_iff.mpr fun q _ ↦ hg0 q)
    have hPt : (∏ q ∈ E, g q) * X ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.prod_ne_top fun q _ ↦ hgt q)
        (ENNReal.prod_ne_top fun q _ ↦ hgt q)
    rw [hfS, hgS, hdS, div_eq_mul_inv]
    calc (∏ q ∈ E, f q) * (X * D) * ((∏ q ∈ E, g q) * X)⁻¹ *
          ENNReal.ofReal (∏ q ∈ E, d q) * ∏ q ∈ E, g q =
        (∏ q ∈ E, f q) * (ENNReal.ofReal (∏ q ∈ E, d q) * D) *
          (((∏ q ∈ E, g q) * X)⁻¹ * ((∏ q ∈ E, g q) * X)) := by ring
      _ = _ := by rw [ENNReal.inv_mul_cancel hP0 hPt, mul_one]
  have hL : Tendsto (fun N ↦ (∏ q ∈ rationalPrimesUpTo N, f q) /
        (∏ q ∈ rationalPrimesUpTo N, g q) * ENNReal.ofReal (∏ q ∈ E, d q) * ∏ q ∈ E, g q)
      atTop (𝓝 (t * ENNReal.ofReal (∏ q ∈ E, d q) * ∏ q ∈ E, g q)) :=
    (ENNReal.Tendsto.mul_const (ENNReal.Tendsto.mul_const ht (Or.inr ENNReal.ofReal_ne_top))
      (Or.inr (ENNReal.prod_ne_top fun q _ ↦ hgt q)))
  have hR : Tendsto (fun N ↦ (∏ q ∈ E, f q) * ENNReal.ofReal (∏ q ∈ rationalPrimesUpTo N, d q))
      atTop (𝓝 ((∏ q ∈ E, f q) * ENNReal.ofReal (∏' q, d q))) :=
    ENNReal.Tendsto.const_mul
      ((ENNReal.continuous_ofReal.tendsto _).comp (tendsto_prod_rationalPrimesUpTo_tprod hd))
      (Or.inr (ENNReal.prod_ne_top fun q _ ↦ hf q))
  exact tendsto_nhds_unique hL (hR.congr' (hkey.mono fun N h ↦ h.symm))

end PositiveDefiniteIntegralLattice
