import SMSFormula.RationalAdeleSingularSeriesEulerProduct

/-!
# Every prime has a local residue density, and the singular series is their Euler product

At every prime `p` (including `2` and the primes dividing `M` or `det F`) and every nonzero
`p`-adic value `a`, the existing tube identity
`vol(ℤ_p^N ∩ Q⁻¹B) = glue_a(X_a(ℤ_p)) · ν(B)` holds for all measurable `B` inside an open
neighbourhood `B₀` of `a`.  Once `closedBall a p^{-k} ⊆ B₀`, the existing count--measure identity
turns it into `#R_k = p^{(k-k₀) n} · #R_{k₀}` in dimension `n + 1`: the residue counts are
eventually level-stable.  The atlas and auxiliary Haars cancel.

For the lattice `L` and an integer `M ≠ 0`, the normalized count `c_p(p^k)` is therefore
eventually constant; its limit is the local residue density `δ_p(M)`.  At odd `p ∤ M` it is the
level-one factor `c_p(M)`.  The block limit of the singular-series factorization is the finite
product `∏_{p ∈ T} δ_p(M)`, and the finite value density of the integral indicator is the full
Euler product

```text
d_fin(1_Zhat)(M) = ∏'_p δ_p(M)       (rank ≥ 5).
```

No block, atlas, Haar normalization or representative is chosen in the conclusion.
-/

noncomputable section

open MeasureTheory Set Metric Matrix Filter Topology RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

local instance rcdPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance rcdPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- Eventual level stability at every prime and every nonzero value, in dimension `n + 1`. -/
theorem exists_card_residue_pow_eq_pow_mul {n : ℕ}
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p]) (a : ℤ_[p]) (ha : (a : ℚ_[p]) ≠ 0)
    (hform : ∃ v, (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' v ≠ 0) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      (Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ k) ↦
          r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a)).card =
        p ^ ((k - k₀) * n) * (Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ k₀) ↦
          r ⬝ᵥ (F.map (toZModPow k₀)) *ᵥ r = toZModPow k₀ a)).card := by
  set Q := (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' with hQ
  obtain ⟨point, hpoint, hcover⟩ := Q.exists_padicSquareBranchAtlas_cover p hform
  let tH : ∀ i, Measure (Q.anisotropicOrthogonal (point i)) := fun _ ↦ Measure.addHaar
  haveI : ∀ i, (tH i).IsAddHaarMeasure := fun _ ↦ by simp only [tH]; infer_instance
  let νs : Measure ℚ_[p] := Measure.addHaar
  let νv : Measure (Fin (n + 1) → ℚ_[p]) := Measure.addHaar
  obtain ⟨B₀, hB₀o, haB₀, hB₀⟩ := Q.exists_isOpen_padicSquareBranchAtlasGlue_integralPoints_mul p
    point hpoint tH νs νv hcover (a : ℚ_[p]) ha
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hB₀o _ haB₀
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hε (by
    rw [div_lt_one (by linarith)]; exact hp1 : 1 / (p : ℝ) < 1)
  set G := Q.padicSquareBranchAtlasGlue p point hpoint tH νs νv (a : ℚ_[p]) {x | ‖x.val‖ ≤ 1}
  have hradius : ∀ k, k₀ ≤ k → (p : ℝ) ^ (-(k : ℤ)) < ε := by
    intro k hk
    have heq : (p : ℝ) ^ (-(k₀ : ℤ)) = (1 / (p : ℝ)) ^ k₀ := by
      rw [_root_.zpow_neg, zpow_natCast, one_div, inv_pow]
    refine lt_of_le_of_lt ?_ (heq ▸ hk₀)
    exact zpow_le_zpow_right₀ hp1.le (neg_le_neg (by exact_mod_cast hk))
  have key : ∀ k, k₀ ≤ k →
      ((Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ k) ↦
          r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a)).card : ℝ≥0∞) *
          νv (closedBall 0 1) = ((p : ℝ≥0∞) ^ k) ^ n * (G * νs (closedBall 0 1)) := by
    intro k hk
    have h1 := card_mul_measure_integralPoints_closedBall νv F a k
    have h2 := hB₀ (closedBall (a : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ))))
      ((Metric.closedBall_subset_ball (hradius k hk)).trans hball) measurableSet_closedBall
    have h3 := pow_mul_measure_closedBall νs (a : ℚ_[p]) k
    rw [← h1, ← hQ, h2, ← h3, pow_succ]
    ring
  have hc0 : νv (closedBall 0 1) ≠ 0 :=
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).measure_ne_zero νv
      ⟨0, mem_closedBall_self zero_le_one⟩
  have hctop : νv (closedBall 0 1) ≠ ⊤ := (isCompact_closedBall 0 1).measure_lt_top.ne
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hk' := key k hk
  have hk₀' := key k₀ le_rfl
  obtain ⟨j, rfl⟩ : ∃ j, k = k₀ + j := ⟨k - k₀, by omega⟩
  have hsplit : ((p : ℝ≥0∞) ^ (k₀ + j)) ^ n =
      (p : ℝ≥0∞) ^ ((k₀ + j - k₀) * n) * ((p : ℝ≥0∞) ^ k₀) ^ n := by
    rw [Nat.add_sub_cancel_left, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  have h : ((Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ (k₀ + j)) ↦
        r ⬝ᵥ (F.map (toZModPow (k₀ + j))) *ᵥ r = toZModPow (k₀ + j) a)).card : ℝ≥0∞) *
        νv (closedBall 0 1) =
      ((p ^ ((k₀ + j - k₀) * n) * (Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ k₀) ↦
        r ⬝ᵥ (F.map (toZModPow k₀)) *ᵥ r = toZModPow k₀ a)).card : ℕ) : ℝ≥0∞) *
        νv (closedBall 0 1) := by
    rw [hk', hsplit, Nat.cast_mul, Nat.cast_pow, mul_assoc, ← hk₀']
    ring
  exact_mod_cast (ENNReal.mul_left_inj hc0 hctop).1 h

end PadicInt

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Eventual level stability of the normalized residue count at every prime, for `M ≠ 0`. -/
theorem exists_normalizedResidueCount_primePow_eq (L : PositiveDefiniteIntegralLattice (n + 1)) (p : ℕ)
    [Fact p.Prime] {M : ℤ} (hM : M ≠ 0) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      L.normalizedResidueCount M (p ^ k) = L.normalizedResidueCount M (p ^ k₀) := by
  have ha : (((M : ℤ) : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    rw [PadicInt.coe_intCast]; exact_mod_cast hM
  obtain ⟨k₀, hk₀⟩ := PadicInt.exists_card_residue_pow_eq_pow_mul _ _ ha
    (L.exists_padic_pairingMatrix_ne_zero p)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  unfold normalizedResidueCount
  rw [L.card_residueSet_eq_card_filter_padic p M k, L.card_residueSet_eq_card_filter_padic p M k₀,
    hk₀ k hk]
  have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨j, rfl⟩ : ∃ j, k = k₀ + j := ⟨k - k₀, by omega⟩
  rw [Nat.add_sub_cancel_left]
  push_cast
  rw [show ((p : ℝ) ^ (k₀ + j)) ^ n = (p : ℝ) ^ (j * n) * ((p : ℝ) ^ k₀) ^ n by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring, mul_inv]
  field_simp

/-- The local residue density `δ_p(M)`: the limit of the normalized counts `c_p(p^k)`. -/
def localResidueDensity (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) (p : ℕ) : ℝ :=
  limUnder atTop fun k : ℕ ↦ L.normalizedResidueCount M (p ^ k)

/-- The normalized counts are eventually equal to the local residue density. -/
theorem eventually_normalizedResidueCount_eq_localResidueDensity (L : PositiveDefiniteIntegralLattice (n + 1))
    (p : ℕ) [Fact p.Prime] {M : ℤ} (hM : M ≠ 0) :
    ∀ᶠ k in atTop, L.normalizedResidueCount M (p ^ k) = L.localResidueDensity M p := by
  obtain ⟨k₀, hk₀⟩ := L.exists_normalizedResidueCount_primePow_eq p hM
  have hev : ∀ᶠ k in atTop,
      L.normalizedResidueCount M (p ^ k) = L.normalizedResidueCount M (p ^ k₀) :=
    Filter.eventually_atTop.2 ⟨k₀, hk₀⟩
  have htend : Tendsto (fun k : ℕ ↦ L.normalizedResidueCount M (p ^ k)) atTop
      (𝓝 (L.normalizedResidueCount M (p ^ k₀))) :=
    tendsto_const_nhds.congr' (hev.mono fun _ h ↦ h.symm)
  have hlim : L.localResidueDensity M p = L.normalizedResidueCount M (p ^ k₀) :=
    htend.limUnder_eq
  exact hev.mono fun k h ↦ h.trans hlim.symm

/-- At an odd prime `p ∤ M` the local residue density is the level-one factor. -/
theorem localResidueDensity_eq_levelOne (L : PositiveDefiniteIntegralLattice (n + 1)) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {M : ℤ} (hM0 : M ≠ 0) (hM : ¬ (p : ℤ) ∣ M) :
    L.localResidueDensity M p = L.normalizedResidueCount M (p ^ 1) := by
  obtain ⟨k, hk, hk1⟩ := ((L.eventually_normalizedResidueCount_eq_localResidueDensity p hM0).and
    (Filter.eventually_ge_atTop 1)).exists
  rw [← hk, L.normalizedResidueCount_primePow_eq hp hM hk1]

/-- The `p`-adic valuation of `k!` tends to infinity. -/
theorem tendsto_factorization_factorial (p : ℕ) [hp : Fact p.Prime] :
    Tendsto (fun k : ℕ ↦ (Nat.factorial k).factorization p) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun j ↦ ⟨p * j, fun k hk ↦ ?_⟩
  have hdvd : Nat.factorial (p * j) ∣ Nat.factorial k := Nat.factorial_dvd_factorial hk
  have hle := (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero _)
    (Nat.factorial_ne_zero _)).2 hdvd p
  rw [Nat.factorization_def _ hp.out, Nat.factorization_def _ hp.out] at hle
  rw [Nat.factorization_def _ hp.out]
  have hmul := padicValNat_factorial_mul (p := p) j
  omega

/-- The block limit is the product of the local residue densities. -/
theorem tendsto_blockResidueCount_prod_localResidueDensity (L : PositiveDefiniteIntegralLattice (n + 1))
    {M : ℤ} (hM : M ≠ 0) (T : Finset ℕ) :
    Tendsto (fun k : ℕ ↦ ∏ p ∈ T.filter Nat.Prime,
        L.normalizedResidueCount M (p ^ (Nat.factorial k).factorization p)) atTop
      (𝓝 (∏ p ∈ T.filter Nat.Prime, L.localResidueDensity M p)) := by
  have hev : ∀ᶠ k in atTop, ∀ p ∈ T.filter Nat.Prime,
      L.normalizedResidueCount M (p ^ (Nat.factorial k).factorization p) =
        L.localResidueDensity M p := by
    rw [Filter.eventually_all_finset]
    intro p hp
    haveI : Fact p.Prime := ⟨(Finset.mem_filter.1 hp).2⟩
    exact (tendsto_factorization_factorial p).eventually
      (L.eventually_normalizedResidueCount_eq_localResidueDensity p hM)
  exact tendsto_const_nhds.congr' (hev.mono fun k h ↦ (Finset.prod_congr rfl h).symm)

/-- The singular series as a full Euler product of local residue densities, rank at least five:
for every supplied residue bad block `T`, the local densities are multipliable over all primes
and the finite value density of the integral indicator at `M` is their product. -/
theorem finiteLocalValueDensity_integralIndicator_eq_tprod_localResidueDensity
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 4 ≤ n) {M : ℤ} {T : Finset ℕ}
    (hT : L.IsResidueBadBlock M T) :
    Multipliable (fun p : Nat.Primes ↦ L.localResidueDensity M p) ∧
      L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity
          rationalFiniteAdeleVectorIntegralIndicator (algebraMap ℚ RationalFiniteAdele (M : ℚ)) =
        ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ) := by
  classical
  have hM0 : M ≠ 0 := by
    rintro rfl
    obtain ⟨q, hq, hqT⟩ := Nat.exists_infinite_primes (T.sup id + 1)
    have := Finset.le_sup (f := id) (hT.2.1 q hqT (dvd_zero _))
    simp only [id] at this
    omega
  obtain ⟨B, hB, hfin⟩ := L.finiteLocalValueDensity_integralIndicator_eq_blockLimit_mul_tprod hn hT
  have hBeq : B = ∏ p ∈ T.filter Nat.Prime, L.localResidueDensity M p :=
    tendsto_nhds_unique hB (L.tendsto_blockResidueCount_prod_localResidueDensity hM0 T)
  obtain ⟨hmult, -⟩ := L.multipliable_goodResidueFactor_and_tprod_pos hn hT
  let h : Nat.Primes → ℝ := fun p ↦ if (p : ℕ) ∈ T then L.localResidueDensity M p else 1
  have hfinite : (Function.mulSupport h).Finite := by
    refine (T.finite_toSet.preimage (Nat.Primes.coe_nat_injective.injOn)).subset fun p hp ↦ ?_
    by_contra hpT
    exact hp (if_neg hpT)
  have hhmult : Multipliable h := multipliable_of_finite_mulSupport hfinite
  have hsplit : (fun p : Nat.Primes ↦ L.localResidueDensity M p) =
      fun p ↦ h p * L.goodResidueFactor M T p := by
    funext p
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    simp only [h, goodResidueFactor]
    by_cases hpT : (p : ℕ) ∈ T
    · rw [if_pos hpT, if_pos hpT, mul_one]
    · rw [if_neg hpT, if_neg hpT, one_mul]
      exact L.localResidueDensity_eq_levelOne (fun h2 ↦ hpT (by rw [h2]; exact hT.1)) hM0
        (fun hd ↦ hpT (hT.2.1 p p.2 hd))
  have htprod_h : ∏' p, h p = ∏ p ∈ T.filter Nat.Prime, L.localResidueDensity M p := by
    have hinj : Set.InjOn (fun p : Nat.Primes ↦ (p : ℕ))
        ((fun p : Nat.Primes ↦ (p : ℕ)) ⁻¹' (T : Set ℕ)) :=
      Nat.Primes.coe_nat_injective.injOn
    have hout : ∀ p ∉ T.preimage (fun p : Nat.Primes ↦ (p : ℕ)) hinj, h p = 1 :=
      fun p hp ↦ if_neg fun hpT ↦ hp (Finset.mem_preimage.2 hpT)
    rw [tprod_eq_prod hout, Finset.prod_filter,
      ← Finset.prod_preimage (fun p : Nat.Primes ↦ (p : ℕ)) T hinj
        (fun x ↦ if x.Prime then L.localResidueDensity M x else 1)
        (fun x _ hx ↦ if_neg fun hp ↦ hx ⟨⟨x, hp⟩, rfl⟩)]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    simp only [h, if_pos (Finset.mem_preimage.1 hp), if_pos p.2]
  refine ⟨hsplit ▸ hhmult.mul hmult, ?_⟩
  rw [hfin, hsplit, hhmult.tprod_mul hmult, htprod_h, hBeq]

/-- The Gram determinant is nonzero (positive definiteness). -/
theorem pairingMatrix_det_ne_zero (L : PositiveDefiniteIntegralLattice n) : L.pairingMatrix.det ≠ 0 := by
  intro h
  have hpos := L.form_posDef.det_pos
  rw [show L.pairingMatrix.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix L.pairingMatrix from rfl,
    ← RingHom.map_det, h, map_zero] at hpos
  exact lt_irrefl _ hpos

/-- The explicit residue bad block `{2} ∪ primes(M) ∪ primes(det F)`. -/
def residueBadBlock (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) : Finset ℕ :=
  insert 2 (M.natAbs.primeFactors ∪ L.pairingMatrix.det.natAbs.primeFactors)

theorem isResidueBadBlock_residueBadBlock (L : PositiveDefiniteIntegralLattice (n + 1)) {M : ℤ} (hM : M ≠ 0) :
    L.IsResidueBadBlock M (L.residueBadBlock M) := by
  refine ⟨Finset.mem_insert_self _ _, fun p hp hpM ↦ ?_, fun p hp hpd ↦ ?_⟩
  · refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
    exact Nat.mem_primeFactors.2 ⟨hp, Int.natCast_dvd.1 hpM, Int.natAbs_ne_zero.2 hM⟩
  · refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
    exact Nat.mem_primeFactors.2 ⟨hp, Int.natCast_dvd.1 hpd,
      Int.natAbs_ne_zero.2 L.pairingMatrix_det_ne_zero⟩

/-- The Siegel singular series, block-free: for `M ≠ 0` in rank at least five, the local
residue densities are multipliable and `d_fin(1_Zhat)(M) = ∏'_p δ_p(M)`. -/
theorem finiteLocalValueDensity_integralIndicator_eq_tprod_localResidueDensity_of_ne_zero
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 4 ≤ n) {M : ℤ} (hM : M ≠ 0) :
    Multipliable (fun p : Nat.Primes ↦ L.localResidueDensity M p) ∧
      L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity
          rationalFiniteAdeleVectorIntegralIndicator (algebraMap ℚ RationalFiniteAdele (M : ℚ)) =
        ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ) :=
  L.finiteLocalValueDensity_integralIndicator_eq_tprod_localResidueDensity hn
    (L.isResidueBadBlock_residueBadBlock hM)

/-! ## The residue-count singular series in rank at least four (no Fourier integral)

In rank `≥ 4` the good-prime deviation is `O(p⁻²)`, so the Euler product of the local residue
densities converges although the finite Bruhat coefficient is no longer integrable (the Gauss-sum
series `Σ φ(q) q^(-N/2)` diverges at `N = 4`).  The singular series is then the limit of residue
counts at `k!`, which needs no Fourier integral. -/

/-- The local residue densities split as the finite block factor times the good factor. -/
theorem localResidueDensity_eq_blockFactor_mul_goodResidueFactor (L : PositiveDefiniteIntegralLattice (n + 1))
    {M : ℤ} (hM : M ≠ 0) {T : Finset ℕ} (hT : L.IsResidueBadBlock M T) (p : Nat.Primes) :
    L.localResidueDensity M p =
      (if (p : ℕ) ∈ T then L.localResidueDensity M p else 1) * L.goodResidueFactor M T p := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  simp only [goodResidueFactor]
  by_cases hpT : (p : ℕ) ∈ T
  · rw [if_pos hpT, if_pos hpT, mul_one]
  · rw [if_neg hpT, if_neg hpT, one_mul]
    exact L.localResidueDensity_eq_levelOne (fun h2 ↦ hpT (by rw [h2]; exact hT.1)) hM
      (fun hd ↦ hpT (hT.2.1 p p.2 hd))

/-- The finite block factor has finite support and product the block product. -/
theorem multipliable_blockFactor_and_tprod (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) (T : Finset ℕ) :
    Multipliable (fun p : Nat.Primes ↦ if (p : ℕ) ∈ T then L.localResidueDensity M p else 1) ∧
      ∏' p : Nat.Primes, (if (p : ℕ) ∈ T then L.localResidueDensity M p else 1) =
        ∏ p ∈ T.filter Nat.Prime, L.localResidueDensity M p := by
  classical
  let h : Nat.Primes → ℝ := fun p ↦ if (p : ℕ) ∈ T then L.localResidueDensity M p else 1
  have hfinite : (Function.mulSupport h).Finite := by
    refine (T.finite_toSet.preimage (Nat.Primes.coe_nat_injective.injOn)).subset fun p hp ↦ ?_
    by_contra hpT
    exact hp (if_neg hpT)
  refine ⟨multipliable_of_finite_mulSupport hfinite, ?_⟩
  have hinj : Set.InjOn (fun p : Nat.Primes ↦ (p : ℕ))
      ((fun p : Nat.Primes ↦ (p : ℕ)) ⁻¹' (T : Set ℕ)) :=
    Nat.Primes.coe_nat_injective.injOn
  have hout : ∀ p ∉ T.preimage (fun p : Nat.Primes ↦ (p : ℕ)) hinj, h p = 1 :=
    fun p hp ↦ if_neg fun hpT ↦ hp (Finset.mem_preimage.2 hpT)
  change ∏' p, h p = _
  rw [tprod_eq_prod hout, Finset.prod_filter,
    ← Finset.prod_preimage (fun p : Nat.Primes ↦ (p : ℕ)) T hinj
      (fun x ↦ if x.Prime then L.localResidueDensity M x else 1)
      (fun x _ hx ↦ if_neg fun hp ↦ hx ⟨⟨x, hp⟩, rfl⟩)]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  simp only [h, if_pos (Finset.mem_preimage.1 hp), if_pos p.2]

/-- The local residue densities are multipliable in rank at least four, with product the block
product times the positive good Euler product. -/
theorem multipliable_localResidueDensity_of_three_le (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n)
    {M : ℤ} (hM : M ≠ 0) {T : Finset ℕ} (hT : L.IsResidueBadBlock M T) :
    Multipliable (fun p : Nat.Primes ↦ L.localResidueDensity M p) ∧
      ∏' p : Nat.Primes, L.localResidueDensity M p =
        (∏ p ∈ T.filter Nat.Prime, L.localResidueDensity M p) *
          ∏' p : Nat.Primes, L.goodResidueFactor M T p := by
  obtain ⟨hgood, -⟩ := L.multipliable_goodResidueFactor_and_tprod_pos_of_three_le hn hT
  obtain ⟨hblock, hblockprod⟩ := L.multipliable_blockFactor_and_tprod M T
  have hsplit : (fun p : Nat.Primes ↦ L.localResidueDensity M p) =
      fun p : Nat.Primes ↦
        (if (p : ℕ) ∈ T then L.localResidueDensity M p else 1) * L.goodResidueFactor M T p :=
    funext (L.localResidueDensity_eq_blockFactor_mul_goodResidueFactor hM hT)
  rw [hsplit]
  exact ⟨hblock.mul hgood, by rw [hblock.tprod_mul hgood, hblockprod]⟩

/-- The residue-count singular series in rank at least four: for `M ≠ 0` the normalized residue
counts at `k!` converge to the Euler product `∏'_p δ_p(M)` of the local residue densities.  No
Fourier integral or Bruhat integrability is used (these fail in rank four). -/
theorem tendsto_normalizedResidueCount_factorial_tprod_localResidueDensity
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) :
    Multipliable (fun p : Nat.Primes ↦ L.localResidueDensity M p) ∧
      Tendsto (fun k : ℕ ↦ L.normalizedResidueCount M (Nat.factorial k)) atTop
        (𝓝 (∏' p : Nat.Primes, L.localResidueDensity M p)) := by
  classical
  set T := L.residueBadBlock M
  have hT := L.isResidueBadBlock_residueBadBlock hM
  obtain ⟨hmult, hprod⟩ := L.multipliable_localResidueDensity_of_three_le hn hM hT
  obtain ⟨hgood, -⟩ := L.multipliable_goodResidueFactor_and_tprod_pos_of_three_le hn hT
  refine ⟨hmult, ?_⟩
  have hfin : Tendsto (fun k : ℕ ↦ (Finset.range (k + 1)).subtype Nat.Prime) atTop atTop := by
    apply Filter.tendsto_atTop_finset_of_monotone
    · intro a b hab
      exact Finset.subtype_mono (Finset.range_mono (by omega))
    · intro p
      exact ⟨p, Finset.mem_subtype.2 (Finset.mem_range.2 (Nat.lt_succ_self _))⟩
  have hpartial : Tendsto (fun k : ℕ ↦
      ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, L.goodResidueFactor M T p) atTop
        (𝓝 (∏' p : Nat.Primes, L.goodResidueFactor M T p)) := by
    refine (hgood.hasProd.comp hfin).congr fun k ↦ ?_
    exact Finset.prod_subtype_eq_prod_filter (fun p : ℕ ↦ L.goodResidueFactor M T p)
  have hlim := (L.tendsto_blockResidueCount_prod_localResidueDensity hM T).mul hpartial
  rw [← hprod] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (T.sup id)] with k hk
  have hkT : ∀ t ∈ T, t ≤ k := fun t ht ↦ le_trans (Finset.le_sup (f := id) ht) hk
  exact (L.normalizedResidueCount_factorial_eq_block_mul hT hkT).symm

set_option maxHeartbeats 2000000 in
/-- The Fourier-free finite value density in rank at least four: the `k!`-tube masses
`k! · ∫ 1_Ẑ(x) 1_Ẑ((Q(x) - M)/k!) dx` of the integral indicator at `M ≠ 0` converge to the singular
series `∏'_p δ_p(M)`.  In rank four the Bruhat coefficient is not integrable, so this tube limit (not
a Fourier integral) is the finite value density there. -/
theorem tendsto_factorial_mul_congruenceIntegral_tprod_localResidueDensity
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) :
    Tendsto (fun k : ℕ ↦ ((Nat.factorial k : ℕ) : ℂ) *
        ∫ x : Fin (n + 1) → RationalFiniteAdele,
          rationalFiniteAdeleVectorIntegralIndicator x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1))
      atTop (𝓝 ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp
    (L.tendsto_normalizedResidueCount_factorial_tprod_localResidueDensity hn hM).2
  refine h.congr fun k ↦ ?_
  have hk0 : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [Function.comp_apply, L.measure_congruenceSet_eq_residueCount (Nat.factorial_ne_zero k) M]
  unfold normalizedResidueCount
  push_cast
  rw [pow_succ]
  field_simp
  have hk0' : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [mul_div_mul_right _ _ hk0']

end PositiveDefiniteIntegralLattice

end
