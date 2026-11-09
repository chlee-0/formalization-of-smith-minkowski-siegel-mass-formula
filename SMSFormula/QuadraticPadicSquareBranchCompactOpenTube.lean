import SMSFormula.QuadraticPadicSquareBranchAtlasGlueScalar

/-!
# Local tube law for compact open vector sets

A compact open set `T ⊆ ℚ_p^m` is preserved by every scalar `u` with `‖u - 1‖` small: `T` is
bounded, and some thickening of the compact `T` stays inside the open `T`.  Restricting the
unit-square identity chart to such units, the glued slice mass of `T` is constant on a
neighbourhood of a nonzero value `a` (one-unit invariance
`padicSquareBranchAtlasGlue_preimage_unit_sq_mul`), and the atlas tube identity gives

`vol(T ∩ Q⁻¹B) = glue_a(T ∩ X_a) · ν(B)` for every measurable `B` inside an open `B₀ ∋ a`.

This holds at every prime, including `2`: only the actual small dyadic chart is used, never
surjectivity of squaring on all units.  It extends the integral-points statement
`exists_isOpen_padicSquareBranchAtlasGlue_integralPoints_mul` from `ℤ_p^m` to arbitrary compact
open `T`.  The atlas and Haars are supplied; no chart, cutoff or Haar is chosen.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicCompactOpenTubeMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicCompactOpenTubeBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {rank : ℕ}

local notation "E" => Fin rank → ℚ_[prime]

/-- A scalar close to one has norm one. -/
theorem norm_eq_one_of_norm_sub_one_lt_one {u : ℚ_[prime]} (hu : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (x := (1 : ℚ_[prime])) (y := u - 1) (by rw [norm_one]; exact hu.ne')
  rw [add_sub_cancel, norm_one, max_eq_left hu.le] at h
  exact h

/-- Small units preserve a compact open set: there is `ε > 0` such that `u • x ∈ T ↔ x ∈ T`
whenever `‖u - 1‖ < ε`. -/
theorem exists_pos_forall_smul_mem_iff_of_isCompact_isOpen {T : Set E} (hTc : IsCompact T)
    (hTo : IsOpen T) :
    ∃ ε > 0, ∀ u : ℚ_[prime], ‖u - 1‖ < ε → ∀ x, u • x ∈ T ↔ x ∈ T := by
  obtain ⟨δ, hδ, hsub⟩ := hTc.exists_thickening_subset_open hTo subset_rfl
  obtain ⟨R, hR⟩ := hTc.isBounded.exists_norm_le
  set R' : ℝ := max R 0 + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  set ε : ℝ := min 1 (δ / R') with hε
  have hεpos : 0 < ε := lt_min one_pos (div_pos hδ hR'pos)
  have hmove : ∀ w : ℚ_[prime], ‖w - 1‖ < ε → ∀ x ∈ T, w • x ∈ T := by
    intro w hw x hx
    apply hsub
    rw [Metric.mem_thickening_iff]
    refine ⟨x, hx, ?_⟩
    rw [dist_eq_norm, show w • x - x = (w - 1) • x by rw [sub_smul, one_smul], norm_smul]
    have hxR : ‖x‖ ≤ R' := (hR x hx).trans (by rw [hR']; linarith [le_max_left R 0])
    calc ‖w - 1‖ * ‖x‖ ≤ ‖w - 1‖ * R' := mul_le_mul_of_nonneg_left hxR (norm_nonneg _)
      _ < (δ / R') * R' := mul_lt_mul_of_pos_right (hw.trans_le (min_le_right _ _)) hR'pos
      _ = δ := div_mul_cancel₀ δ hR'pos.ne'
  refine ⟨ε, hεpos, fun u hu x ↦ ⟨fun hux ↦ ?_, hmove u hu x⟩⟩
  have hu1 : ‖u‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one prime (hu.trans_le (min_le_left _ _))
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  have hinv : ‖u⁻¹ - 1‖ < ε := by
    rw [show u⁻¹ - 1 = -(u - 1) * u⁻¹ by field_simp; ring, norm_mul, norm_neg, norm_inv, hu1,
      inv_one, mul_one]
    exact hu
  have := hmove u⁻¹ hinv (u • x) hux
  rwa [smul_smul, inv_mul_cancel₀ hu0, one_smul] at this

/-- The local tube law for a compact open set: for a nonzero value `a` and an atlas covering the
nonisotropic vectors there is an open `B₀ ∋ a` such that every measurable `B ⊆ B₀` satisfies
`vol(T ∩ Q⁻¹B) = glue_a(T ∩ X_a) · ν(B)`. -/
theorem exists_isOpen_padicSquareBranchAtlasGlue_compactOpen_mul
    (form : QuadraticForm ℚ_[prime] E)
    (point : ℕ → E) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure E)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    (hcover : {vector | form vector ≠ 0} ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    (value : ℚ_[prime]) (hvalue : value ≠ 0) {T : Set E} (hTc : IsCompact T) (hTo : IsOpen T) :
    ∃ B₀ : Set ℚ_[prime], IsOpen B₀ ∧ value ∈ B₀ ∧ ∀ B ⊆ B₀, MeasurableSet B →
      vectorHaar (T ∩ form ⁻¹' B) =
        form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
          value (Subtype.val ⁻¹' T) * scalarHaar B := by
  obtain ⟨ε, hε, hst⟩ := exists_pos_forall_smul_mem_iff_of_isCompact_isOpen prime hTc hTo
  have hform : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  set chart := Rat.unitSquareIdentityChart ℚ_[prime] with hchart
  set N : Set ℚ_[prime]ˣ := {u | ‖(u : ℚ_[prime]) - 1‖ < ε} with hN
  have hNo : IsOpen N :=
    isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  set O : Set ℚ_[prime]ˣ := chart.target ∩ chart.symm ⁻¹' N with hO
  have hOo : IsOpen O := chart.isOpen_inter_preimage_symm hNo
  have hOv : IsOpen (Units.val '' O) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℚ_[prime])).isOpenMap _ hOo
  have hone : (1 : ℚ_[prime]ˣ) ∈ chart.source := Rat.one_mem_unitSquareIdentityChart_source _
  have hc1 : chart 1 = 1 := by rw [hchart, Rat.unitSquareIdentityChart_apply, one_pow]
  refine ⟨(fun t ↦ t / value) ⁻¹' (Units.val '' O ∩ Metric.sphere 0 1),
    (hOv.inter (IsUltrametricDist.isOpen_sphere (0 : ℚ_[prime]) one_ne_zero)).preimage
      (continuous_id.div_const value), ?_, fun B hB hBm ↦ ?_⟩
  · refine ⟨⟨1, ⟨?_, ?_⟩, by simp [div_self hvalue]⟩, by simp [div_self hvalue]⟩
    · rw [← hc1]; exact chart.map_source hone
    · change ‖((chart.symm 1 : ℚ_[prime]ˣ) : ℚ_[prime]) - 1‖ < ε
      rw [← hc1, chart.left_inv hone, Units.val_one, sub_self, norm_zero]
      exact hε
  set T' : Set E := T ∩ {vector | form vector ≠ 0} with hT'
  have hT'm : MeasurableSet T' :=
    hTo.measurableSet.inter (isOpen_ne_fun hform continuous_const).measurableSet
  have hne : ∀ t ∈ B, t ≠ 0 := by
    intro t ht h
    have := (hB ht).2
    simp [h] at this
  have htube : T' ∩ form ⁻¹' B = T ∩ form ⁻¹' B := by
    ext v
    simp only [hT', Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hne _ h.2⟩, h.2⟩⟩
  have hslice : ∀ t, t ≠ 0 →
      (Subtype.val ⁻¹' T' : Set {vector : E // form vector = t}) = Subtype.val ⁻¹' T := by
    intro t ht
    ext x
    simp only [hT', Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, x.property]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, ht⟩⟩
  rw [← htube, ← hslice value hvalue]
  refine form.padicSquareBranchAtlasGlue_measure_inter_preimage_eq_mul prime point hpoint
    transverseHaar scalarHaar vectorHaar hT'm (Set.inter_subset_right.trans hcover) hBm
    fun t ht ↦ ?_
  obtain ⟨⟨w, ⟨hwt, hwN⟩, hwv⟩, hsph⟩ := hB ht
  set u : ℚ_[prime] := ((chart.symm w : ℚ_[prime]ˣ) : ℚ_[prime]) with hu
  have hsq : u ^ 2 = (w : ℚ_[prime]) := by
    have h := chart.right_inv hwt
    rw [hchart, Rat.unitSquareIdentityChart_apply] at h
    rw [hu, ← Units.val_pow_eq_pow_val, h]
  have hnorm : ‖t / value‖ = 1 := mem_sphere_zero_iff_norm.mp hsph
  have hu1 : ‖u‖ = 1 := by
    have h2 : ‖u‖ ^ 2 = 1 := by rw [← norm_pow, hsq, hwv, hnorm]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  have hstable : ∀ vector, u • vector ∈ T' ↔ vector ∈ T' := by
    intro vector
    simp only [hT', Set.mem_inter_iff, Set.mem_setOf_eq, QuadraticMap.map_smul, smul_eq_mul,
      ne_eq, mul_eq_zero, hu0, false_or,
      hst u hwN vector]
  have ht' : t = u ^ 2 * value := by rw [hsq, hwv, div_mul_cancel₀ t hvalue]
  rw [ht']
  exact form.padicSquareBranchAtlasGlue_preimage_unit_sq_mul prime point hpoint transverseHaar
    scalarHaar vectorHaar hT'm (Set.inter_subset_right.trans hcover) u hu1 hstable value

/-- Two compact open sets on one value neighbourhood (the local input of the finite-place
replacement lemma): there is an open `B₀ ∋ a` on which both tube laws hold, so
`vol(T₁ ∩ Q⁻¹B) · glue_a(T₂) = vol(T₂ ∩ Q⁻¹B) · glue_a(T₁)` for every measurable `B ⊆ B₀`. -/
theorem exists_isOpen_padicSquareBranchAtlasGlue_compactOpen_pair
    (form : QuadraticForm ℚ_[prime] E)
    (point : ℕ → E) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure E)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    (hcover : {vector | form vector ≠ 0} ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    (value : ℚ_[prime]) (hvalue : value ≠ 0) {T₁ T₂ : Set E} (hT₁c : IsCompact T₁)
    (hT₁o : IsOpen T₁) (hT₂c : IsCompact T₂) (hT₂o : IsOpen T₂) :
    ∃ B₀ : Set ℚ_[prime], IsOpen B₀ ∧ value ∈ B₀ ∧ ∀ B ⊆ B₀, MeasurableSet B →
      vectorHaar (T₁ ∩ form ⁻¹' B) =
          form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
            value (Subtype.val ⁻¹' T₁) * scalarHaar B ∧
        vectorHaar (T₂ ∩ form ⁻¹' B) =
          form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
            value (Subtype.val ⁻¹' T₂) * scalarHaar B := by
  obtain ⟨B₁, hB₁o, hB₁a, hB₁⟩ := exists_isOpen_padicSquareBranchAtlasGlue_compactOpen_mul prime
    form point hpoint transverseHaar scalarHaar vectorHaar hcover value hvalue hT₁c hT₁o
  obtain ⟨B₂, hB₂o, hB₂a, hB₂⟩ := exists_isOpen_padicSquareBranchAtlasGlue_compactOpen_mul prime
    form point hpoint transverseHaar scalarHaar vectorHaar hcover value hvalue hT₂c hT₂o
  exact ⟨B₁ ∩ B₂, hB₁o.inter hB₂o, ⟨hB₁a, hB₂a⟩, fun B hB hBm ↦
    ⟨hB₁ B (hB.trans inter_subset_left) hBm, hB₂ B (hB.trans inter_subset_right) hBm⟩⟩

end QuadraticMap
