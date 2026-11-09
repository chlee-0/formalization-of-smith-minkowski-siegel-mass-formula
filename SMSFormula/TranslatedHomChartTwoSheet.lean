import SMSFormula.RationalCliffordSpinCandidatePlacewiseChartMeasureGluing

/-! Two-sheet pushforward of a glued homomorphism-chart measure. Let `f : G →* H`
be a continuous homomorphism with an identity-centred local chart `e` literally
equal to `f`, and let `μ` be a measure on `H`. The glued measure on `G` is
`μ` pulled back through `f` on every translated chart source. If every fiber of
`f` is a two-point set `{x, x z}` (`z ≠ 1`, as for the scalar `-1` in the
central-fiber map of `GSpin`), then for every measurable `B ⊆ H`

`glued(f⁻¹ B) = 2 · μ(B ∩ range f)`.

The proof counts, for each `y = f x`, the two disjoint cover pieces containing
`x` and `x z`; no section or sheet choice enters the statement. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.TranslatedHomChart

set_option linter.unusedSectionVars false

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]

/-- On a measurable subset of a translated source, the ambient chart measure is
`μ` of the image. -/
theorem ambientSourceMeasure_apply_of_subset (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (g : G) (μ : Measure H) {T : Set G} (hT : MeasurableSet T)
    (hsub : T ⊆ source e g) :
    ambientSourceMeasure f e g μ T = μ (f '' T) := by
  have hj : MeasurableEmbedding (fun x : source e g ↦ f x.1) :=
    (isOpenEmbedding_pointMap f e hfe g).measurableEmbedding
  rw [ambientSourceMeasure, Measure.map_apply continuous_subtype_val.measurable hT,
    sourceMeasure_eq_comap_pointMap f e hfe g μ,
    hj.comap_apply]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hsub hx⟩, hx, rfl⟩

/-- The glued measure of a measurable set is the sum over the disjoint cover
pieces of `μ` of the images. -/
theorem gluedMeasure_apply_eq_tsum (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (μ : Measure H) {S : Set G} (hS : MeasurableSet S) :
    gluedMeasure f e μ S = ∑' k, μ (f '' (S ∩ coverPiece e k)) := by
  rw [gluedMeasure, Measure.sum_apply _ hS]
  refine tsum_congr fun k ↦ ?_
  rw [coverPieceMeasure_eq_restrict_ambient, Measure.restrict_apply hS]
  exact ambientSourceMeasure_apply_of_subset f e hfe _ μ (hS.inter (measurableSet_coverPiece e k))
    (Set.inter_subset_right.trans (coverPiece_subset_source e k))

theorem injOn_coverPiece (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (k : ℕ) : Set.InjOn f (coverPiece e k) := by
  intro x hx y hy hxy
  have hinj := (isOpenEmbedding_pointMap f e hfe (coverCenter e k)).injective
  have := @hinj ⟨x, coverPiece_subset_source e k hx⟩ ⟨y, coverPiece_subset_source e k hy⟩ hxy
  exact congrArg Subtype.val this

theorem measurableSet_image_coverPiece (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (k : ℕ) {S : Set G} (hS : MeasurableSet S) :
    MeasurableSet (f '' (S ∩ coverPiece e k)) := by
  have hj : MeasurableEmbedding (fun x : source e (coverCenter e k) ↦ f x.1) :=
    (isOpenEmbedding_pointMap f e hfe _).measurableEmbedding
  have h := hj.measurableSet_image.mpr
    ((hS.inter (measurableSet_coverPiece e k)).preimage continuous_subtype_val.measurable)
  convert h using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, coverPiece_subset_source e k hx.2⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, hx, rfl⟩

theorem exists_mem_coverPiece (e : OpenPartialHomeomorph G H) (hone : (1 : G) ∈ e.source)
    (x : G) : ∃ k, x ∈ coverPiece e k := by
  have hx : x ∈ ⋃ k, coverPiece e k := by rw [iUnion_coverPiece e hone]; trivial
  exact Set.mem_iUnion.mp hx

theorem eq_of_mem_coverPiece (e : OpenPartialHomeomorph G H) {x : G} {k k' : ℕ}
    (hk : x ∈ coverPiece e k) (hk' : x ∈ coverPiece e k') : k = k' := by
  by_contra hne
  exact Set.disjoint_left.mp (pairwiseDisjoint_coverPiece e hne) hk hk'

/-- Two-sheet pushforward: if every fiber of `f` is `{x, x z}` with `z ≠ 1`, then
`glued(f⁻¹ B) = 2 · μ(B ∩ range f)` for every measurable `B`. -/
theorem gluedMeasure_preimage_eq_two_mul (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (hone : (1 : G) ∈ e.source) (μ : Measure H)
    (z : G) (hz : z ≠ 1) (hfib : ∀ x y, f x = f y ↔ y = x ∨ y = x * z)
    (hf : Continuous f) {B : Set H} (hB : MeasurableSet B) :
    gluedMeasure f e μ (f ⁻¹' B) = 2 * μ (B ∩ Set.range f) := by
  classical
  have hpre : MeasurableSet (f ⁻¹' B) := hf.measurable hB
  rw [gluedMeasure_apply_eq_tsum f e hfe μ hpre]
  simp_rw [Set.image_preimage_inter]
  have hmeas : ∀ k, MeasurableSet (B ∩ f '' coverPiece e k) := fun k ↦ by
    have := measurableSet_image_coverPiece f e hfe k (MeasurableSet.univ)
    rw [Set.univ_inter] at this
    exact hB.inter this
  have hrange : Set.range f = ⋃ k, f '' coverPiece e k := by
    rw [← Set.image_univ, ← iUnion_coverPiece e hone, Set.image_iUnion]
  have hrangeM : MeasurableSet (B ∩ Set.range f) := by
    rw [hrange]
    exact hB.inter (MeasurableSet.iUnion fun k ↦ by
      have := measurableSet_image_coverPiece f e hfe k (MeasurableSet.univ)
      rwa [Set.univ_inter] at this)
  -- pointwise count
  have hcount : ∀ y, ∑' k, (B ∩ f '' coverPiece e k).indicator (1 : H → ℝ≥0∞) y =
      (B ∩ Set.range f).indicator (fun _ ↦ (2 : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ B ∩ Set.range f
    · obtain ⟨hyB, x, rfl⟩ := hy
      obtain ⟨k, hk⟩ := exists_mem_coverPiece e hone x
      obtain ⟨k', hk'⟩ := exists_mem_coverPiece e hone (x * z)
      have hxz : x * z ≠ x := by
        intro h; exact hz (mul_eq_left.mp h)
      have hkk' : k ≠ k' := by
        intro h
        subst h
        exact hxz (injOn_coverPiece f e hfe k hk' hk ((hfib x (x * z)).mpr (Or.inr rfl)).symm)
      have hmem : ∀ j, f x ∈ B ∩ f '' coverPiece e j ↔ j = k ∨ j = k' := by
        intro j
        constructor
        · rintro ⟨-, w, hw, hwx⟩
          rcases (hfib x w).mp hwx.symm with rfl | rfl
          · exact Or.inl (eq_of_mem_coverPiece e hw hk)
          · exact Or.inr (eq_of_mem_coverPiece e hw hk')
        · rintro (rfl | rfl)
          · exact ⟨hyB, x, hk, rfl⟩
          · exact ⟨hyB, x * z, hk', ((hfib x (x * z)).mpr (Or.inr rfl)).symm⟩
      rw [Set.indicator_of_mem (show f x ∈ B ∩ Set.range f from ⟨hyB, x, rfl⟩),
        tsum_eq_sum (s := {k, k'}) (fun j hj ↦ by
          rw [Set.indicator_of_notMem]
          intro hmemj
          rcases (hmem j).mp hmemj with rfl | rfl <;> simp at hj)]
      rw [Finset.sum_pair hkk', Set.indicator_of_mem ((hmem k).mpr (Or.inl rfl)),
        Set.indicator_of_mem ((hmem k').mpr (Or.inr rfl))]
      simp only [Pi.one_apply]
      norm_num
    · rw [Set.indicator_of_notMem hy]
      refine ENNReal.tsum_eq_zero.mpr fun k ↦ Set.indicator_of_notMem ?_ _
      rintro ⟨hyB, w, -, rfl⟩
      exact hy ⟨hyB, w, rfl⟩
  calc ∑' k, μ (B ∩ f '' coverPiece e k)
      = ∑' k, ∫⁻ y, (B ∩ f '' coverPiece e k).indicator 1 y ∂μ := by
        refine tsum_congr fun k ↦ ?_
        rw [lintegral_indicator_one (hmeas k)]
    _ = ∫⁻ y, ∑' k, (B ∩ f '' coverPiece e k).indicator 1 y ∂μ :=
        (lintegral_tsum fun k ↦ (measurable_one.indicator (hmeas k)).aemeasurable).symm
    _ = ∫⁻ y, (B ∩ Set.range f).indicator (fun _ ↦ (2 : ℝ≥0∞)) y ∂μ :=
        lintegral_congr hcount
    _ = 2 * μ (B ∩ Set.range f) := by
        rw [lintegral_indicator hrangeM, setLIntegral_const]

end MeasureTheory.TranslatedHomChart
