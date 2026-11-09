import SMSFormula.RationalAdeleSingularSeriesLocalDensity
import SMSFormula.AdelicGaussianSpinTamagawaEisensteinComparison

/-!
# A nonvanishing singular series forces a rational representation

In rank at least five every positive rational is represented (local isotropy and Hasse--Minkowski,
`exists_nativeRationalQuadraticForm_eq_of_pos`).  In rank four this fails, and the replacement is:

* `exists_padicInt_eq_of_localResidueDensity_ne_zero`: `δ_p(M) ≠ 0` gives an integral `p`-adic
  solution of `Q(x) = M` (residue solutions at all large levels `p^k` and compactness of `ℤ_p^N`);
* `localResidueDensity_ne_zero_of_tprod_ne_zero`: a nonzero Euler product has no zero factor;
* `exists_nativeRationalQuadraticForm_eq_of_tprod_localResidueDensity_ne_zero`: in rank `≥ 4`, a
  positive integer `M` with nonzero singular series `∏'_p δ_p(M)` is represented over `ℚ` (old
  Hasse--Minkowski, which holds in every rank);
* `tprod_localResidueDensity_eq_zero_of_not_represented`: at a positive integer that is not
  represented, the singular series vanishes.

Nothing is chosen.
-/

noncomputable section

open Filter Topology Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A residue solution modulo `p^k` gives a `p`-adic integral vector solving `Q(x) ≡ M` to
precision `p^(-k)`. -/
theorem exists_padicInt_norm_sub_le_of_card_ne_zero (L : PositiveDefiniteIntegralLattice n) (p : ℕ)
    [Fact p.Prime] (M : ℤ) (k : ℕ)
    (h : Nat.card {z : Fin n → ZMod (p ^ k) //
      L.zmodQuadForm (p ^ k) z = ((M : ℤ) : ZMod (p ^ k))} ≠ 0) :
    ∃ x : Fin n → ℤ_[p],
      ‖x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x - ((M : ℤ) : ℤ_[p])‖ ≤
        (p : ℝ) ^ (-(k : ℤ)) := by
  classical
  rw [L.card_residueSet_eq_card_filter_padic p M k] at h
  obtain ⟨r, hr⟩ := Finset.card_ne_zero.1 h
  rw [Finset.mem_filter] at hr
  set F := L.pairingMatrix.map (Int.castRingHom ℤ_[p]) with hFdef
  let x : Fin n → ℤ_[p] := fun i ↦ ((r i).val : ℤ_[p])
  have hx : (PadicInt.toZModPow k : ℤ_[p] →+* ZMod (p ^ k)) ∘ x = r := by
    funext i
    simp [x]
  refine ⟨x, ?_⟩
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    sub_eq_zero, RingHom.map_dotProduct]
  have hmv : (PadicInt.toZModPow k : ℤ_[p] →+* ZMod (p ^ k)) ∘ (F *ᵥ x) =
      (F.map (PadicInt.toZModPow k)) *ᵥ r := by
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec, hx]
  rw [hmv, hx]
  exact hr.2

/-- A nonzero local residue density gives an integral `p`-adic solution of `Q(x) = M`. -/
theorem exists_padicInt_eq_of_localResidueDensity_ne_zero (L : PositiveDefiniteIntegralLattice (n + 1)) (p : ℕ)
    [Fact p.Prime] {M : ℤ} (hM : M ≠ 0) (hd : L.localResidueDensity M p ≠ 0) :
    ∃ x : Fin (n + 1) → ℤ_[p],
      x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x = ((M : ℤ) : ℤ_[p]) := by
  classical
  set F := L.pairingMatrix.map (Int.castRingHom ℤ_[p]) with hFdef
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1
    (L.eventually_normalizedResidueCount_eq_localResidueDensity p hM)
  have hcard : ∀ k, k₀ ≤ k → Nat.card {z : Fin (n + 1) → ZMod (p ^ k) //
      L.zmodQuadForm (p ^ k) z = ((M : ℤ) : ZMod (p ^ k))} ≠ 0 := by
    intro k hk h0
    apply hd
    rw [← hk₀ k hk, normalizedResidueCount, h0, Nat.cast_zero, mul_zero]
  let t : ℕ → Set (Fin (n + 1) → ℤ_[p]) := fun i ↦
    {x | ‖x ⬝ᵥ F *ᵥ x - ((M : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-((k₀ + i : ℕ) : ℤ))}
  have hQ : Continuous fun x : Fin (n + 1) → ℤ_[p] ↦ x ⬝ᵥ F *ᵥ x - ((M : ℤ) : ℤ_[p]) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hP : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have htd : ∀ i, t (i + 1) ⊆ t i := by
    intro i x hx
    refine le_trans hx (zpow_le_zpow_right₀ hP ?_)
    push_cast
    omega
  have htn : ∀ i, (t i).Nonempty := fun i ↦
    L.exists_padicInt_norm_sub_le_of_card_ne_zero p M (k₀ + i) (hcard _ (by omega))
  have htcl : ∀ i, IsClosed (t i) := fun i ↦
    isClosed_le (continuous_norm.comp hQ) continuous_const
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn
    (isCompact_univ.of_isClosed_subset (htcl 0) (Set.subset_univ _)) htcl
  rw [Set.mem_iInter] at hx
  refine ⟨x, sub_eq_zero.1 (PadicInt.ext_of_toZModPow.1 fun m ↦ ?_)⟩
  have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow _ (k₀ + m)).1 (hx m)
  rw [map_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  rw [Ideal.mem_span_singleton] at hmem
  exact (pow_dvd_pow _ (by omega)).trans hmem

/-- A multipliable real family with a zero factor has product zero. -/
theorem tprod_eq_zero_of_eq_zero {ι : Type*} {f : ι → ℝ} (hf : Multipliable f) {i : ι}
    (hi : f i = 0) : ∏' j, f j = 0 := by
  classical
  refine tendsto_nhds_unique hf.hasProd (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop ({i} : Finset ι)] with s hs
  exact (Finset.prod_eq_zero (hs (Finset.mem_singleton_self i)) hi).symm

/-- A nonzero singular series has no zero local factor. -/
theorem localResidueDensity_ne_zero_of_tprod_ne_zero (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n)
    {M : ℤ} (hM : M ≠ 0) (hd : ∏' p : Nat.Primes, L.localResidueDensity M p ≠ 0)
    (p : Nat.Primes) : L.localResidueDensity M p ≠ 0 := fun h ↦
  hd (tprod_eq_zero_of_eq_zero
    (L.multipliable_localResidueDensity_of_three_le hn hM (L.isResidueBadBlock_residueBadBlock hM)).1 h)

/-- Nonvanishing singular series forces a rational representation, rank at least four: a positive
integer `M` with `∏'_p δ_p(M) ≠ 0` is represented over `ℚ`. -/
theorem exists_nativeRationalQuadraticForm_eq_of_tprod_localResidueDensity_ne_zero
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {M : ℤ} (hM : 0 < M)
    (hd : ∏' p : Nat.Primes, L.localResidueDensity M p ≠ 0) :
    ∃ x : Fin (n + 1) → ℚ, L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = M := by
  set A := L.rationalQuadraticSpaceMatrix.pairingMatrix with hAdef
  have hA_symm : A.IsSymm := L.rationalQuadraticSpaceMatrix.form_symm
  have hA_det : A.det ≠ 0 := L.rationalQuadraticSpaceMatrix.form_det_ne_zero
  have hM0 : M ≠ 0 := hM.ne'
  have hb : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hM
  have hreal : ∃ v : Fin (n + 1) → ℝ,
      gramQuadraticValue (A.map (algebraMap ℚ ℝ)) v = ((M : ℚ) : ℝ) := by
    have hmap : A.map (algebraMap ℚ ℝ) = L.pairingMatrix.map (Int.cast : ℤ → ℝ) := by
      ext i j
      simp [hAdef, rationalQuadraticSpaceMatrix_pairingMatrix, PositiveDefiniteIntegralLattice.rationalFormMatrix]
    set v₀ : Fin (n + 1) → ℝ := Pi.single 0 1 with hv₀
    have hq₀ : 0 < gramQuadraticValue (A.map (algebraMap ℚ ℝ)) v₀ := by
      have hval : gramQuadraticValue (A.map (algebraMap ℚ ℝ)) v₀ =
          (A.map (algebraMap ℚ ℝ)) 0 0 := by
        simp [hv₀, gramQuadraticValue, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hval, hmap]
      exact L.form_posDef.diag_pos
    refine ⟨Real.sqrt (((M : ℚ) : ℝ) / gramQuadraticValue (A.map (algebraMap ℚ ℝ)) v₀) • v₀, ?_⟩
    rw [gramQuadraticValue_smul_vector,
      Real.sq_sqrt (div_nonneg (by exact_mod_cast hb.le) hq₀.le), div_mul_cancel₀ _ hq₀.ne']
  have hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin (n + 1) → ℚ_[p],
      gramQuadraticValue (A.map (algebraMap ℚ ℚ_[p])) v = ((M : ℚ) : ℚ_[p]) := by
    intro p hp
    obtain ⟨x, hx⟩ := L.exists_padicInt_eq_of_localResidueDensity_ne_zero p hM0
      (L.localResidueDensity_ne_zero_of_tprod_ne_zero hn hM0 hd ⟨p, hp.out⟩)
    refine ⟨fun i ↦ (x i : ℚ_[p]), ?_⟩
    have hmap : A.map (algebraMap ℚ ℚ_[p]) =
        (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom) := by
      ext i j
      simp [hAdef, rationalQuadraticSpaceMatrix_pairingMatrix, PositiveDefiniteIntegralLattice.rationalFormMatrix]
    have hcoe := congrArg (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) hx
    rw [RingHom.map_dotProduct] at hcoe
    have hmv : (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) ∘
        ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x) =
        ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom) *ᵥ
          ((PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) ∘ x) := by
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec]
    rw [hmv] at hcoe
    rw [gramQuadraticValue, hmap]
    convert hcoe using 1
  obtain ⟨x, hx⟩ := Rat.exists_gramQuadraticValue_eq_rat_of_real_and_padic (by omega) A hA_symm
    hA_det (M : ℚ) (by exact_mod_cast hM0) hreal hpadic
  exact ⟨x, (L.nativeRationalQuadraticForm_eq_gramQuadraticValue x).trans hx⟩

/-- At a positive integer that is not represented over `ℚ` the singular series vanishes, rank at
least four. -/
theorem tprod_localResidueDensity_eq_zero_of_not_represented (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : 0 < M)
    (hnot : ∀ x : Fin (n + 1) → ℚ, L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ M) :
    ∏' p : Nat.Primes, L.localResidueDensity M p = 0 := by
  by_contra hd
  obtain ⟨x, hx⟩ := L.exists_nativeRationalQuadraticForm_eq_of_tprod_localResidueDensity_ne_zero
    hn hM hd
  exact hnot x hx

end PositiveDefiniteIntegralLattice
