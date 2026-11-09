import SMSFormula.PadicQuadraticLocalDensityCount
import SMSFormula.QuadraticPadicSquareBranchCompactOpenTube

/-!
# Restricted local densities as point counts, and the exact local count ratio

For an integral Gram matrix `F` over `ℤ_p`, a supplied level `e` and a supplied residue set
`R ⊆ (ℤ/p^eℤ)^N`, let `T_R ⊆ ℚ_p^N` be the integral vectors whose reduction modulo `p^e` lies in
`R`.  For every level `k ≥ e`

`p^{kN} · ν(T_R ∩ Q⁻¹(closedBall a p^{-k})) = #{r mod p^k : Q(r) = a, r mod p^e ∈ R} · ν(ℤ_p^N)`,

the restricted form of the `card_mul_measure_integralPoints_closedBall`.  `T_R` is compact
and open, so the compact-open tube law applies to it.  Comparing with the full count gives,
for a nonzero value `a` and all sufficiently large `k`, the exact identity

`#R_k(restricted) · glue_a(ℤ_p^N ∩ X_a) = #R_k(full) · glue_a(T_R ∩ X_a)`:

the local ratio of restricted to full counts is eventually constant, equal to the ratio of the
glued slice masses.  No Hensel lifting is used; it holds at every prime, including `2`.  The
atlas, Haars, `e` and `R` are supplied.
-/

noncomputable section

open MeasureTheory Set Metric Matrix
open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

local instance rldcPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance rldcPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance rldcPadicIntMeasurableSpace : MeasurableSpace ℤ_[p] := borel _
local instance rldcPadicIntBorelSpace : BorelSpace ℤ_[p] := ⟨rfl⟩

/-- Reduction modulo `p^e` factors through reduction modulo `p^k` for `e ≤ k`. -/
theorem castHom_vectorReduction {e k : ℕ} (hek : e ≤ k) (x : Fin N → ℤ_[p]) :
    (fun i ↦ ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ e)) (vectorReduction k x i)) =
      vectorReduction e x := by
  funext i
  simp only [vectorReduction_apply]
  exact RingHom.congr_fun (zmod_cast_comp_toZModPow e k hek) (x i)

/-- Restricted quadratic congruence mass on `ℤ_p^N`, for `e ≤ k`. -/
theorem card_mul_measure_restrictedQuadraticCongruence (μ : Measure (Fin N → ℤ_[p]))
    [μ.IsAddLeftInvariant] (F : Matrix (Fin N) (Fin N) ℤ_[p]) (a : ℤ_[p]) {e k : ℕ}
    (hek : e ≤ k) (R : Set (Fin N → ZMod (p ^ e))) [DecidablePred (· ∈ R)] :
    ((p ^ k) ^ N : ℝ≥0∞) *
        μ {x | ‖x ⬝ᵥ F *ᵥ x - a‖ ≤ (p : ℝ) ^ (-(k : ℤ)) ∧ vectorReduction e x ∈ R} =
      (Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
        r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a ∧
          (fun i ↦ ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ e)) (r i)) ∈ R)).card *
        μ univ := by
  classical
  have hset : {x : Fin N → ℤ_[p] |
      ‖x ⬝ᵥ F *ᵥ x - a‖ ≤ (p : ℝ) ^ (-(k : ℤ)) ∧ vectorReduction e x ∈ R} =
      vectorReduction k ⁻¹' ((Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
        r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a ∧
          (fun i ↦ ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ e)) (r i)) ∈ R) : Finset _) :
        Set _) := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, Finset.coe_filter, Finset.mem_univ, true_and]
    rw [castHom_vectorReduction hek x]
    rw [← toZModPow_eq_zero_iff, map_sub, sub_eq_zero, RingHom.map_dotProduct]
    have hmv : (toZModPow k) ∘ (F *ᵥ x) = F.map (toZModPow k) *ᵥ ((toZModPow k) ∘ x) := by
      funext i; exact RingHom.map_mulVec _ _ _ i
    rw [hmv]
    rfl
  rw [hset, measure_preimage_vectorReduction_finset, ← card_mul_measure_ker_vectorReduction μ k]
  ring

/-- The integral vectors of `ℚ_p^N` whose reduction modulo `p^e` lies in `R`. -/
def restrictedIntegralVectors (e : ℕ) (R : Set (Fin N → ZMod (p ^ e))) : Set (Fin N → ℚ_[p]) :=
  vectorInclusion '' (vectorReduction (p := p) (N := N) e ⁻¹' R)

theorem isOpen_preimage_vectorReduction (e : ℕ) (R : Set (Fin N → ZMod (p ^ e))) :
    IsOpen (vectorReduction (p := p) (N := N) e ⁻¹' R) := by
  have hR : R = ⋃ r ∈ R, {r} := by ext; simp
  rw [hR, Set.preimage_iUnion₂]
  refine isOpen_biUnion fun r _ ↦ ?_
  obtain ⟨y, rfl⟩ := vectorReduction_surjective (p := p) (N := N) e r
  rw [preimage_vectorReduction_singleton]
  exact IsUltrametricDist.isOpen_closedBall _
    (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _).ne'

theorem isClosed_preimage_vectorReduction (e : ℕ) (R : Set (Fin N → ZMod (p ^ e))) :
    IsClosed (vectorReduction (p := p) (N := N) e ⁻¹' R) := by
  have hR : R = ⋃ r ∈ R, {r} := by ext; simp
  rw [hR, Set.preimage_iUnion₂]
  refine (Set.toFinite R).isClosed_biUnion fun r _ ↦ ?_
  obtain ⟨y, rfl⟩ := vectorReduction_surjective (p := p) (N := N) e r
  rw [preimage_vectorReduction_singleton]
  exact isClosed_closedBall

theorem isOpen_restrictedIntegralVectors (e : ℕ) (R : Set (Fin N → ZMod (p ^ e))) :
    IsOpen (restrictedIntegralVectors (p := p) e R) := by
  have hemb := isometry_vectorInclusion (p := p) (N := N) |>.isEmbedding
  have hopen : IsOpen (Set.range (vectorInclusion (p := p) (N := N))) := by
    rw [range_vectorInclusion]
    exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  exact (⟨hemb, hopen⟩ : Topology.IsOpenEmbedding _).isOpenMap _
    (isOpen_preimage_vectorReduction e R)

theorem isCompact_restrictedIntegralVectors (e : ℕ) (R : Set (Fin N → ZMod (p ^ e))) :
    IsCompact (restrictedIntegralVectors (p := p) e R) :=
  ((isClosed_preimage_vectorReduction e R).isCompact).image
    (isometry_vectorInclusion (p := p) (N := N)).continuous

variable (ν : Measure (Fin N → ℚ_[p])) [ν.IsAddHaarMeasure]

/-- Restricted vector congruence mass on `ℚ_p^N`, for `e ≤ k`. -/
theorem card_mul_measure_restrictedIntegralPoints_closedBall
    (F : Matrix (Fin N) (Fin N) ℤ_[p]) (a : ℤ_[p]) {e k : ℕ} (hek : e ≤ k)
    (R : Set (Fin N → ZMod (p ^ e))) [DecidablePred (· ∈ R)] :
    ((p ^ k) ^ N : ℝ≥0∞) *
        ν (restrictedIntegralVectors e R ∩
          (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' ⁻¹'
            closedBall (a : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ)))) =
      (Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
        r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a ∧
          (fun i ↦ ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ e)) (r i)) ∈ R)).card *
        ν (closedBall 0 1) := by
  haveI := isAddLeftInvariant_comap_vectorInclusion (p := p) (N := N) ν
  have hemb := measurableEmbedding_vectorInclusion (p := p) (N := N)
  have h := card_mul_measure_restrictedQuadraticCongruence
    (Measure.comap (vectorInclusion (p := p) (N := N)) ν) F a hek R
  rw [comap_vectorInclusion_univ, hemb.comap_apply] at h
  convert h using 3
  have hval : ∀ x : Fin N → ℤ_[p],
      (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (vectorInclusion x) =
        ((x ⬝ᵥ F *ᵥ x : ℤ_[p]) : ℚ_[p]) := by
    intro x
    simp only [Matrix.toQuadraticMap', Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
    rw [show ((x ⬝ᵥ F *ᵥ x : ℤ_[p]) : ℚ_[p]) =
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) (x ⬝ᵥ F *ᵥ x) from rfl, RingHom.map_dotProduct]
    congr 1
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm
  ext v
  simp only [restrictedIntegralVectors, mem_inter_iff, mem_image, mem_preimage, mem_closedBall,
    dist_eq_norm, mem_setOf_eq]
  constructor
  · rintro ⟨⟨x, hxR, rfl⟩, hQ⟩
    refine ⟨x, ⟨?_, hxR⟩, rfl⟩
    rw [hval] at hQ
    rw [← PadicInt.padic_norm_e_of_padicInt]
    simpa using hQ
  · rintro ⟨x, ⟨hx, hxR⟩, rfl⟩
    refine ⟨⟨x, hxR, rfl⟩, ?_⟩
    rw [hval]
    rw [← PadicInt.padic_norm_e_of_padicInt] at hx
    simpa using hx

omit [ν.IsAddHaarMeasure] in
/-- Restricted local density as a point count: for a nonzero value, a covering atlas and supplied
Haars, for all large `k ≥ e`,
`p^{kN} · glue_a(T_R) · ν_s(closedBall a p^{-k}) = #R_k(restricted) · ν(ℤ_p^N)`. -/
theorem exists_card_eq_restrictedLocalDensity (F : Matrix (Fin N) (Fin N) ℤ_[p]) (a : ℤ_[p])
    (ha : (a : ℚ_[p]) ≠ 0) (point : ℕ → Fin N → ℚ_[p])
    (hpoint : ∀ i, (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure (((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin N → ℚ_[p])) [νv.IsAddHaarMeasure]
    (hcover : {v | (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' v ≠ 0} ⊆
      ⋃ i, ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
        p point hpoint i)
    (e : ℕ) (R : Set (Fin N → ZMod (p ^ e))) [DecidablePred (· ∈ R)] :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ hek : e ≤ k,
      ((p ^ k) ^ N : ℝ≥0∞) *
          (((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
              p point hpoint tH νs νv (a : ℚ_[p]) (Subtype.val ⁻¹' restrictedIntegralVectors e R) *
            νs (closedBall (a : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ))))) =
        (Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
          r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a ∧
            (fun i ↦ ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ e)) (r i)) ∈ R)).card *
          νv (closedBall 0 1) := by
  obtain ⟨B₀, hB₀o, haB₀, hB₀⟩ :=
    ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').exists_isOpen_padicSquareBranchAtlasGlue_compactOpen_mul
      p point hpoint tH νs νv hcover (a : ℚ_[p]) ha (isCompact_restrictedIntegralVectors e R)
      (isOpen_restrictedIntegralVectors e R)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hB₀o _ haB₀
  obtain ⟨k₀, hk₀⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨k₀, fun k hk hek ↦ ?_⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hrk : (p : ℝ) ^ (-(k : ℤ)) < ε :=
    lt_of_le_of_lt (zpow_le_zpow_right₀ hp1 (neg_le_neg (by exact_mod_cast hk))) hk₀
  have hsub : closedBall (a : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ))) ⊆ B₀ :=
    (closedBall_subset_ball hrk).trans hball
  rw [← hB₀ _ hsub isClosed_closedBall.measurableSet]
  exact card_mul_measure_restrictedIntegralPoints_closedBall νv F a hek R

omit [ν.IsAddHaarMeasure] in
/-- The exact local count ratio: for a nonzero value and all large `k ≥ e`,
`#R_k(restricted) · glue_a(ℤ_p^N) = #R_k(full) · glue_a(T_R)`. -/
theorem exists_card_restricted_mul_glue_eq (F : Matrix (Fin N) (Fin N) ℤ_[p]) (a : ℤ_[p])
    (ha : (a : ℚ_[p]) ≠ 0) (point : ℕ → Fin N → ℚ_[p])
    (hpoint : ∀ i, (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure (((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin N → ℚ_[p])) [νv.IsAddHaarMeasure]
    (hcover : {v | (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' v ≠ 0} ⊆
      ⋃ i, ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
        p point hpoint i)
    (e : ℕ) (R : Set (Fin N → ZMod (p ^ e))) [DecidablePred (· ∈ R)] :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ hek : e ≤ k,
      ((Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
          r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a ∧
            (fun i ↦ ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ e)) (r i)) ∈ R)).card : ℝ≥0∞) *
          ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
            p point hpoint tH νs νv (a : ℚ_[p]) {x | ‖x.1‖ ≤ 1} =
        ((Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
          r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a)).card : ℝ≥0∞) *
          ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
            p point hpoint tH νs νv (a : ℚ_[p]) (Subtype.val ⁻¹' restrictedIntegralVectors e R) := by
  obtain ⟨k₁, hk₁⟩ := exists_card_eq_localDensity F a ha point hpoint tH νs νv hcover
  obtain ⟨k₂, hk₂⟩ := exists_card_eq_restrictedLocalDensity F a ha point hpoint tH νs νv
    hcover e R
  refine ⟨max k₁ k₂, fun k hk hek ↦ ?_⟩
  have hA := hk₁ k (le_of_max_le_left hk)
  have hB := hk₂ k (le_of_max_le_right hk) hek
  set P : ℝ≥0∞ := ((p ^ k) ^ N : ℝ≥0∞)
  set gF := ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
    p point hpoint tH νs νv (a : ℚ_[p]) {x | ‖x.1‖ ≤ 1}
  set gR := ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
    p point hpoint tH νs νv (a : ℚ_[p]) (Subtype.val ⁻¹' restrictedIntegralVectors e R)
  set Bk := νs (closedBall (a : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ))))
  set C := νv (closedBall 0 1)
  set cR : ℝ≥0∞ := ((Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
    r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a ∧
      (fun i ↦ ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ e)) (r i)) ∈ R)).card : ℝ≥0∞)
  set cF : ℝ≥0∞ := ((Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
    r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a)).card : ℝ≥0∞)
  have hC0 : C ≠ 0 :=
    (IsUltrametricDist.isOpen_closedBall (0 : Fin N → ℚ_[p]) one_ne_zero).measure_ne_zero νv
      ⟨0, mem_closedBall_self zero_le_one⟩
  have hCt : C ≠ ⊤ := (isCompact_closedBall (0 : Fin N → ℚ_[p]) 1).measure_lt_top.ne
  refine (ENNReal.mul_left_inj hC0 hCt).mp ?_
  calc cR * gF * C = (cR * C) * gF := by ring
    _ = (P * (gR * Bk)) * gF := by rw [← hB]
    _ = (P * (gF * Bk)) * gR := by ring
    _ = (cF * C) * gR := by rw [hA]
    _ = cF * gR * C := by ring

end PadicInt
