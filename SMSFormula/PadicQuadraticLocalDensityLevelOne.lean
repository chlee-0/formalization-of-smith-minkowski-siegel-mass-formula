import SMSFormula.PadicQuadraticLocalDensityCount
import SMSFormula.RationalPadicSquareClass

/-! The local density at level one. At an odd prime every `t` with
`‖t − a‖ ≤ p^{-1}` is `u² a` for a `p`-adic unit `u` when `a` is a unit (the
residue square criterion), so the integral-point tube identity holds for every
ball `closedBall a p^{-k}` with `k ≥ 1`. With the scalar ball scaling
`p^k · ν(closedBall a p^{-k}) = ν(ℤ_p)` this gives, for every `k ≥ 1`,

`p^{k(N−1)} · λ(X_a(ℤ_p)) · ν(ℤ_p) = #R_k · ν_vec(ℤ_p^N)`;

at `k = 1` the local density is the finite-field count
`#{r ∈ F_p^N : r ⬝ F̄ r = ā}` divided by `p^{N−1}` (up to the supplied Haar
normalizations). The atlas and Haars are supplied; nothing is chosen. -/
noncomputable section
open MeasureTheory Set Metric Matrix
open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

local instance ldoPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance ldoPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance ldoPadicIntMeasurableSpace : MeasurableSpace ℤ_[p] := borel _
local instance ldoPadicIntBorelSpace : BorelSpace ℤ_[p] := ⟨rfl⟩

theorem measurableEmbedding_coe : MeasurableEmbedding (fun z : ℤ_[p] ↦ (z : ℚ_[p])) :=
  (show Topology.IsOpenEmbedding (fun z : ℤ_[p] ↦ (z : ℚ_[p])) from
    PadicInt.isOpenEmbedding_coe).measurableEmbedding

/-- Scalar ball scaling: `p^k · ν(closedBall a p^{-k}) = ν(ℤ_p)` for every additive
Haar measure on `ℚ_p`. -/
theorem pow_mul_measure_closedBall (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure] (a : ℚ_[p]) (k : ℕ) :
    (p ^ k : ℝ≥0∞) * ν (closedBall a ((p : ℝ) ^ (-(k : ℤ)))) = ν (closedBall 0 1) := by
  have hemb := measurableEmbedding_coe (p := p)
  set μ₀ := Measure.comap (fun z : ℤ_[p] ↦ (z : ℚ_[p])) ν with hμ₀
  haveI : μ₀.IsAddLeftInvariant := by
    refine ⟨fun y ↦ Measure.ext fun s hs ↦ ?_⟩
    rw [Measure.map_apply (measurable_const_add y) hs, hμ₀, hemb.comap_apply, hemb.comap_apply]
    have himage : (fun z : ℤ_[p] ↦ (z : ℚ_[p])) '' ((fun h ↦ y + h) ⁻¹' s) =
        (fun h ↦ (y : ℚ_[p]) + h) ⁻¹' ((fun z : ℤ_[p] ↦ (z : ℚ_[p])) '' s) := by
      ext v
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨y + t, ht, by push_cast; rfl⟩
      · rintro ⟨u, hu, huv⟩
        refine ⟨u - y, by simpa using hu, ?_⟩
        simp only [PadicInt.coe_sub, huv, add_sub_cancel_left]
    rw [himage, measure_preimage_add]
  -- the kernel of reduction modulo `p^k`
  set K := (toZModPow (p := p) k).toAddMonoidHom.ker with hK
  have hKimage : (fun z : ℤ_[p] ↦ (z : ℚ_[p])) '' (K : Set ℤ_[p]) =
      closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ))) := by
    ext v
    rw [mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [PadicInt.padic_norm_e_of_padicInt, ← toZModPow_eq_zero_iff]
      exact hz
    · intro hv
      have hv1 : ‖v‖ ≤ 1 := hv.trans (zpow_le_one_of_nonpos₀
        (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) (by simp))
      refine ⟨⟨v, hv1⟩, ?_, rfl⟩
      change toZModPow k ⟨v, hv1⟩ = 0
      rw [toZModPow_eq_zero_iff]
      exact hv
  have hunivImage : (fun z : ℤ_[p] ↦ (z : ℚ_[p])) '' univ = closedBall (0 : ℚ_[p]) 1 := by
    ext v
    rw [mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨z, -, rfl⟩
      rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one z
    · intro hv; exact ⟨⟨v, hv⟩, trivial, rfl⟩
  have hKm : MeasurableSet (K : Set ℤ_[p]) := by
    have : (K : Set ℤ_[p]) = (fun z : ℤ_[p] ↦ (z : ℚ_[p])) ⁻¹'
        closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ))) := by
      rw [← hKimage, hemb.injective.preimage_image]
    rw [this]
    exact isClosed_closedBall.measurableSet.preimage hemb.measurable
  have hindex : K.index = p ^ k := by
    rw [hK, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr
      (ZMod.ringHom_surjective (toZModPow (p := p) k)), AddSubgroup.card_top,
      Nat.card_eq_fintype_card, ZMod.card]
  haveI : K.FiniteIndex := ⟨by rw [hindex]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have h := AddSubgroup.index_mul_measure K hKm μ₀
  rw [hindex, hμ₀, hemb.comap_apply, hemb.comap_apply, hKimage, hunivImage] at h
  have htrans : ν (closedBall a ((p : ℝ) ^ (-(k : ℤ)))) =
      ν (closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ)))) := by
    have : closedBall a ((p : ℝ) ^ (-(k : ℤ))) =
        (fun h ↦ -a + h) ⁻¹' closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ))) := by
      ext v
      simp only [mem_closedBall, mem_preimage, dist_eq_norm, neg_add_eq_sub, sub_zero]
    rw [this, measure_preimage_add]
  rw [htrans]
  exact_mod_cast h

/-- At an odd prime, every element of `closedBall a p^{-1}` for a unit `a` lies in
the unit-square class of `a`. -/
theorem exists_unit_sq_mul_of_mem_closedBall (hp : p ≠ 2) {a : ℚ_[p]} (ha : ‖a‖ = 1) {k : ℕ}
    (hk : 1 ≤ k) {t : ℚ_[p]} (ht : t ∈ closedBall a ((p : ℝ) ^ (-(k : ℤ)))) :
    ∃ u : ℚ_[p], ‖u‖ = 1 ∧ t = u ^ 2 * a := by
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlt : ‖t - a‖ < 1 := by
    rw [mem_closedBall, dist_eq_norm] at ht
    refine lt_of_le_of_lt ht (zpow_lt_one_of_neg₀ hp1 ?_)
    have : (1 : ℤ) ≤ k := by exact_mod_cast hk
    omega
  set u : ℚ_[p] := t / a with hu
  have hu1 : ‖u - 1‖ < 1 := by
    rw [hu, show t / a - 1 = (t - a) / a by field_simp, norm_div, ha, div_one]
    exact hlt
  have hunorm : ‖u‖ = 1 := by
    have := Padic.norm_eq_of_norm_sub_lt_right (z1 := u) (z2 := 1) (by rwa [norm_one])
    rwa [norm_one] at this
  let U : ℤ_[p] := ⟨u, hunorm.le⟩
  have hU : IsUnit U := PadicInt.isUnit_iff.mpr hunorm
  have hres : toZMod U = 1 := by
    rw [← sub_eq_zero, ← map_one toZMod, ← map_sub, ← RingHom.mem_ker, ker_toZMod,
      IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    change ‖((U - 1 : ℤ_[p]) : ℚ_[p])‖ < 1
    push_cast
    exact hu1
  obtain ⟨c, hc⟩ := (PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hp hU).mpr
    (by rw [hres]; exact ⟨1, (mul_one 1).symm⟩)
  have hcnorm : ‖(c : ℚ_[p])‖ = 1 := by
    have h1 : ‖(c : ℚ_[p])‖ * ‖(c : ℚ_[p])‖ = 1 := by
      rw [← norm_mul, ← PadicInt.coe_mul, ← hc]; exact hunorm
    nlinarith [norm_nonneg (c : ℚ_[p])]
  refine ⟨c, hcnorm, ?_⟩
  have hcu : (c : ℚ_[p]) ^ 2 = u := by
    rw [pow_two, ← PadicInt.coe_mul, ← hc]
  rw [hcu, hu, div_mul_cancel₀ t ha0]

/-- Local density at every level `k ≥ 1`: at an odd prime, for a unit value `a`,
`p^{kN} · λ(X_a(ℤ_p)) · ν(closedBall a p^{-k}) = #R_k · ν_vec(ℤ_p^N)` holds for
every `k ≥ 1` (no Hensel threshold). -/
theorem card_eq_localDensity_of_one_le (hp : p ≠ 2) (F : Matrix (Fin N) (Fin N) ℤ_[p])
    (a : ℤ_[p]) (ha : ‖(a : ℚ_[p])‖ = 1) (point : ℕ → Fin N → ℚ_[p])
    (hpoint : ∀ i, (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure (((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin N → ℚ_[p])) [νv.IsAddHaarMeasure]
    (hcover : {v | (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' v ≠ 0} ⊆
      ⋃ i, ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
        p point hpoint i)
    {k : ℕ} (hk : 1 ≤ k) :
    ((p ^ k) ^ N : ℝ≥0∞) *
        (((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
            p point hpoint tH νs νv (a : ℚ_[p]) {x | ‖x.1‖ ≤ 1} *
          νs (closedBall (a : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ))))) =
      (Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
        r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a)).card * νv (closedBall 0 1) := by
  have ha0 : (a : ℚ_[p]) ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  rw [← ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue_integralPoints_mul
    p point hpoint tH νs νv hcover (a : ℚ_[p]) ha0 isClosed_closedBall.measurableSet
    (fun t ht ↦ exists_unit_sq_mul_of_mem_closedBall hp ha hk ht)]
  exact card_mul_measure_integralPoints_closedBall νv F a k

/-- Normalized local density: in dimension `n + 1`, for every `k ≥ 1`,
`p^{kn} · λ(X_a(ℤ_p)) · ν(ℤ_p) = #R_k · ν_vec(ℤ_p^{n+1})`. -/
theorem card_eq_pow_mul_localDensity (hp : p ≠ 2) {n : ℕ}
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p])
    (a : ℤ_[p]) (ha : ‖(a : ℚ_[p])‖ = 1) (point : ℕ → Fin (n + 1) → ℚ_[p])
    (hpoint : ∀ i, (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure (((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin (n + 1) → ℚ_[p]))
    [νv.IsAddHaarMeasure]
    (hcover : {v | (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' v ≠ 0} ⊆
      ⋃ i, ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
        p point hpoint i)
    {k : ℕ} (hk : 1 ≤ k) :
    ((p ^ k) ^ n : ℝ≥0∞) *
        ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
            p point hpoint tH νs νv (a : ℚ_[p]) {x | ‖x.1‖ ≤ 1} *
          νs (closedBall 0 1) =
      (Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ k) ↦
        r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a)).card * νv (closedBall 0 1) := by
  rw [← card_eq_localDensity_of_one_le hp F a ha point hpoint tH νs νv hcover hk,
    ← pow_mul_measure_closedBall νs (a : ℚ_[p]) k]
  ring

/-- Level one: `p^n · λ(X_a(ℤ_p)) · ν(ℤ_p) = #{r ∈ F_p^{n+1} : r ⬝ F̄ r = ā} · ν_vec(ℤ_p^{n+1})`. -/
theorem card_levelOne_eq_localDensity (hp : p ≠ 2) {n : ℕ}
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p])
    (a : ℤ_[p]) (ha : ‖(a : ℚ_[p])‖ = 1) (point : ℕ → Fin (n + 1) → ℚ_[p])
    (hpoint : ∀ i, (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure (((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin (n + 1) → ℚ_[p]))
    [νv.IsAddHaarMeasure]
    (hcover : {v | (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' v ≠ 0} ⊆
      ⋃ i, ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
        p point hpoint i) :
    (p ^ n : ℝ≥0∞) *
        ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
            p point hpoint tH νs νv (a : ℚ_[p]) {x | ‖x.1‖ ≤ 1} *
          νs (closedBall 0 1) =
      (Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ 1) ↦
        r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card * νv (closedBall 0 1) := by
  have h := card_eq_pow_mul_localDensity hp F a ha point hpoint tH νs νv hcover le_rfl
  rwa [pow_one] at h

end PadicInt
