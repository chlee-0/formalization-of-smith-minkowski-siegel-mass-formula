import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import SMSFormula.PadicIntQuadraticCongruenceMass
import SMSFormula.QuadraticPadicSquareBranchAtlasGlueScalar

/-! The local density as a point count. Let `F` be an integral Gram matrix over
`ℤ_p`, `Q` the quadratic form of `F` on `ℚ_p^N`, and `ν_vec` any additive Haar
measure on `ℚ_p^N`. The coordinate embedding `ι : ℤ_p^N → ℚ_p^N` pulls `ν_vec`
back to a left-invariant measure of total mass `ν_vec(ℤ_p^N)`, and carries the
level-`k` congruence set onto `ℤ_p^N ∩ Q⁻¹(closedBall a p^{-k})`. Hence

`p^{kN} · ν_vec(ℤ_p^N ∩ Q⁻¹(closedBall a p^{-k})) = #R_k · ν_vec(ℤ_p^N)`,

with `R_k = {r ∈ (ℤ/p^kℤ)^N : r ⬝ F̄ r = ā}`. Combined with the integral-point tube
identity, for every unit-square-class neighbourhood level `k ≥ k₀`

`p^{kN} · λ(X_a(ℤ_p)) · ν(closedBall a p^{-k}) = #R_k · ν_vec(ℤ_p^N)`,

the classical point-count description of `d_p(a) = λ(X_a(ℤ_p))`. The atlas and
Haars are supplied; no representative or normalization is chosen. -/
noncomputable section
open MeasureTheory Set Metric Matrix
open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

local instance ldcPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance ldcPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance ldcPadicIntMeasurableSpace : MeasurableSpace ℤ_[p] := borel _
local instance ldcPadicIntBorelSpace : BorelSpace ℤ_[p] := ⟨rfl⟩

/-- The coordinate embedding `ℤ_p^N → ℚ_p^N`. -/
def vectorInclusion : (Fin N → ℤ_[p]) →+ (Fin N → ℚ_[p]) :=
  (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toAddMonoidHom.compLeft (Fin N)

@[simp] theorem vectorInclusion_apply (x : Fin N → ℤ_[p]) (i : Fin N) :
    vectorInclusion x i = (x i : ℚ_[p]) := rfl

theorem norm_vectorInclusion (x : Fin N → ℤ_[p]) : ‖vectorInclusion x‖ = ‖x‖ := by
  simp only [Pi.norm_def, vectorInclusion_apply]
  rfl

theorem range_vectorInclusion :
    Set.range (vectorInclusion (p := p) (N := N)) = closedBall 0 1 := by
  ext v
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  constructor
  · rintro ⟨x, rfl⟩ i
    rw [vectorInclusion_apply, PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_le_one _
  · intro h
    exact ⟨fun i ↦ ⟨v i, h i⟩, funext fun i ↦ rfl⟩

theorem isometry_vectorInclusion : Isometry (vectorInclusion (p := p) (N := N)) :=
  AddMonoidHomClass.isometry_of_norm _ norm_vectorInclusion

theorem measurableEmbedding_vectorInclusion :
    MeasurableEmbedding (vectorInclusion (p := p) (N := N)) := by
  have hemb := isometry_vectorInclusion (p := p) (N := N) |>.isEmbedding
  have hopen : IsOpen (Set.range (vectorInclusion (p := p) (N := N))) := by
    rw [range_vectorInclusion]
    exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  exact (⟨hemb, hopen⟩ : Topology.IsOpenEmbedding _).measurableEmbedding

variable (ν : Measure (Fin N → ℚ_[p])) [ν.IsAddHaarMeasure]

/-- The pulled-back measure on `ℤ_p^N` is left-invariant. -/
theorem isAddLeftInvariant_comap_vectorInclusion :
    (Measure.comap (vectorInclusion (p := p) (N := N)) ν).IsAddLeftInvariant := by
  have hemb := measurableEmbedding_vectorInclusion (p := p) (N := N)
  refine ⟨fun y ↦ Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply (measurable_const_add y) hs, hemb.comap_apply, hemb.comap_apply]
  have himage : vectorInclusion '' ((fun h ↦ y + h) ⁻¹' s) =
      (fun h ↦ vectorInclusion y + h) ⁻¹' (vectorInclusion '' s) := by
    ext v
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨y + t, ht, by rw [map_add]⟩
    · rintro ⟨u, hu, huv⟩
      refine ⟨u - y, by simpa using hu, ?_⟩
      rw [map_sub, huv, add_sub_cancel_left]
  rw [himage, measure_preimage_add]

omit [ν.IsAddHaarMeasure] in
theorem comap_vectorInclusion_univ :
    Measure.comap (vectorInclusion (p := p) (N := N)) ν univ = ν (closedBall 0 1) := by
  rw [(measurableEmbedding_vectorInclusion (p := p) (N := N)).comap_apply, Set.image_univ,
    range_vectorInclusion]

/-- Vector congruence mass on `ℚ_p^N`:
`p^{kN} · ν(ℤ_p^N ∩ Q⁻¹(closedBall a p^{-k})) = #R_k · ν(ℤ_p^N)`. -/
theorem card_mul_measure_integralPoints_closedBall (F : Matrix (Fin N) (Fin N) ℤ_[p]) (a : ℤ_[p])
    (k : ℕ) :
    ((p ^ k) ^ N : ℝ≥0∞) *
        ν ({v : Fin N → ℚ_[p] | ‖v‖ ≤ 1} ∩
          (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' ⁻¹'
            closedBall (a : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ)))) =
      (Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
        r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a)).card * ν (closedBall 0 1) := by
  haveI := isAddLeftInvariant_comap_vectorInclusion (p := p) (N := N) ν
  have hemb := measurableEmbedding_vectorInclusion (p := p) (N := N)
  have h := card_mul_measure_quadraticCongruence
    (Measure.comap (vectorInclusion (p := p) (N := N)) ν) F a k
  rw [comap_vectorInclusion_univ, hemb.comap_apply] at h
  convert h using 3
  ext v
  simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_closedBall, dist_eq_norm, mem_image]
  constructor
  · rintro ⟨hv, hQ⟩
    have hv' : v ∈ closedBall (0 : Fin N → ℚ_[p]) 1 := by rwa [mem_closedBall, dist_zero_right]
    rw [← range_vectorInclusion] at hv'
    obtain ⟨x, rfl⟩ := hv'
    refine ⟨x, ?_, rfl⟩
    have hval : (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (vectorInclusion x) =
        ((x ⬝ᵥ F *ᵥ x : ℤ_[p]) : ℚ_[p]) := by
      simp only [Matrix.toQuadraticMap', Matrix.toQuadraticForm',
        LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
      rw [show ((x ⬝ᵥ F *ᵥ x : ℤ_[p]) : ℚ_[p]) =
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) (x ⬝ᵥ F *ᵥ x) from rfl, RingHom.map_dotProduct]
      congr 1
      funext i
      exact (RingHom.map_mulVec _ _ _ i).symm
    rw [hval] at hQ
    rw [← PadicInt.padic_norm_e_of_padicInt]
    simpa using hQ
  · rintro ⟨x, hx, rfl⟩
    refine ⟨by
      rw [norm_vectorInclusion (p := p) x]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i ↦ PadicInt.norm_le_one (x i), ?_⟩
    have hval : (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (vectorInclusion x) =
        ((x ⬝ᵥ F *ᵥ x : ℤ_[p]) : ℚ_[p]) := by
      simp only [Matrix.toQuadraticMap', Matrix.toQuadraticForm',
        LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
      rw [show ((x ⬝ᵥ F *ᵥ x : ℤ_[p]) : ℚ_[p]) =
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) (x ⬝ᵥ F *ᵥ x) from rfl, RingHom.map_dotProduct]
      congr 1
      funext i
      exact (RingHom.map_mulVec _ _ _ i).symm
    rw [hval]
    rw [← PadicInt.padic_norm_e_of_padicInt] at hx
    simpa using hx

omit [ν.IsAddHaarMeasure] in
/-- Local density as a point count: for an integral Gram matrix, a nonzero value
`a ∈ ℤ_p`, a supplied atlas covering the nonisotropic vectors and supplied Haars,
for every large level `k`,
`p^{kN} · λ(X_a(ℤ_p)) · ν(closedBall a p^{-k}) = #R_k · ν_vec(ℤ_p^N)`. -/
theorem exists_card_eq_localDensity (F : Matrix (Fin N) (Fin N) ℤ_[p]) (a : ℤ_[p])
    (ha : (a : ℚ_[p]) ≠ 0) (point : ℕ → Fin N → ℚ_[p])
    (hpoint : ∀ i, (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure (((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin N → ℚ_[p])) [νv.IsAddHaarMeasure]
    (hcover : {v | (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' v ≠ 0} ⊆
      ⋃ i, ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
        p point hpoint i) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ((p ^ k) ^ N : ℝ≥0∞) *
          (((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
              p point hpoint tH νs νv (a : ℚ_[p]) {x | ‖x.1‖ ≤ 1} *
            νs (closedBall (a : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ))))) =
        (Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
          r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a)).card * νv (closedBall 0 1) := by
  obtain ⟨B₀, hB₀o, haB₀, hB₀⟩ :=
    ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').exists_isOpen_padicSquareBranchAtlasGlue_integralPoints_mul
      p point hpoint tH νs νv hcover (a : ℚ_[p]) ha
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hB₀o _ haB₀
  obtain ⟨k₀, hk₀⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hrk : (p : ℝ) ^ (-(k : ℤ)) < ε :=
    lt_of_le_of_lt (zpow_le_zpow_right₀ hp1 (neg_le_neg (by exact_mod_cast hk))) hk₀
  have hsub : closedBall (a : ℚ_[p]) ((p : ℝ) ^ (-(k : ℤ))) ⊆ B₀ :=
    (closedBall_subset_ball hrk).trans hball
  rw [← hB₀ _ hsub isClosed_closedBall.measurableSet]
  exact card_mul_measure_integralPoints_closedBall νv F a k

end PadicInt
