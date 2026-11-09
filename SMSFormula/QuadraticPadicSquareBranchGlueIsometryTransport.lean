import SMSFormula.QuadraticPadicSquareBranchCompactOpenTube

/-!
# Glue masses under a linear isometry of quadratic spaces

Let `f : ℚ_p^{r₁} ≃ ℚ_p^{r₂}` be a continuous linear equivalence carrying `Q₁` to `Q₂`, and
let `map f μ₁ = c • μ₂` for the vector Haars (such a `c ∈ (0,∞)` exists by Haar uniqueness).
For every compact open `T ⊆ ℚ_p^{r₁}` and nonzero value `a`, with atlases covering the
nonisotropic vectors on both sides,

`glue¹_a(T) = c · glue²_a(f T)`.

Indeed the compact-open tube laws hold on a common small open `B ∋ a` of positive finite
scalar mass, and `μ₁(T ∩ Q₁⁻¹B) = (map f μ₁)(f T ∩ Q₂⁻¹B) = c · μ₂(f T ∩ Q₂⁻¹B)`.  So the
glue ratio of two compact open sets is invariant under isometric transport: the Jacobian constant
cancels.  This compares the lattice (ambient) and block glue masses without touching the glue
construction.  The atlases, Haars and `c` are supplied or existential; nothing is chosen.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance glueIsoPadicMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance glueIsoPadicBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {r₁ r₂ : ℕ}

/-- The Haar comparison constant of a continuous linear equivalence exists and is positive
finite. -/
theorem exists_map_continuousLinearEquiv_eq_smul (f : (Fin r₁ → ℚ_[prime]) ≃L[ℚ_[prime]]
    (Fin r₂ → ℚ_[prime])) (μ₁ : Measure (Fin r₁ → ℚ_[prime])) (μ₂ : Measure (Fin r₂ → ℚ_[prime]))
    [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ Measure.map f μ₁ = c • μ₂ := by
  haveI : (Measure.map f μ₁).IsAddHaarMeasure := f.isAddHaarMeasure_map μ₁
  refine ⟨(Measure.addHaarScalarFactor (Measure.map f μ₁) μ₂ : ℝ≥0∞),
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    ENNReal.coe_ne_top, ?_⟩
  exact Measure.isAddLeftInvariant_eq_smul _ _

/-- Glue masses under a linear isometry: `glue¹_a(T) = c · glue²_a(f T)` for compact open `T`. -/
theorem padicSquareBranchAtlasGlue_linearIsometry
    (form₁ : QuadraticForm ℚ_[prime] (Fin r₁ → ℚ_[prime]))
    (form₂ : QuadraticForm ℚ_[prime] (Fin r₂ → ℚ_[prime]))
    (f : (Fin r₁ → ℚ_[prime]) ≃L[ℚ_[prime]] (Fin r₂ → ℚ_[prime])) (hf : ∀ x, form₂ (f x) = form₁ x)
    (point₁ : ℕ → Fin r₁ → ℚ_[prime]) (hpoint₁ : ∀ i, form₁ (point₁ i) ≠ 0)
    (tH₁ : ∀ i, Measure (form₁.anisotropicOrthogonal (point₁ i))) [∀ i, (tH₁ i).IsAddHaarMeasure]
    (hcover₁ : {w | form₁ w ≠ 0} ⊆ ⋃ i, form₁.padicSquareBranchAtlasRegion prime point₁ hpoint₁ i)
    (point₂ : ℕ → Fin r₂ → ℚ_[prime]) (hpoint₂ : ∀ i, form₂ (point₂ i) ≠ 0)
    (tH₂ : ∀ i, Measure (form₂.anisotropicOrthogonal (point₂ i))) [∀ i, (tH₂ i).IsAddHaarMeasure]
    (hcover₂ : {w | form₂ w ≠ 0} ⊆ ⋃ i, form₂.padicSquareBranchAtlasRegion prime point₂ hpoint₂ i)
    (νs : Measure ℚ_[prime]) [νs.IsAddHaarMeasure]
    (μ₁ : Measure (Fin r₁ → ℚ_[prime])) (μ₂ : Measure (Fin r₂ → ℚ_[prime]))
    [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] {c : ℝ≥0∞} (hmap : Measure.map f μ₁ = c • μ₂)
    {value : ℚ_[prime]} (hvalue : value ≠ 0)
    {T : Set (Fin r₁ → ℚ_[prime])} (hTc : IsCompact T) (hTo : IsOpen T) :
    form₁.padicSquareBranchAtlasGlue prime point₁ hpoint₁ tH₁ νs μ₁ value (Subtype.val ⁻¹' T) =
      c * form₂.padicSquareBranchAtlasGlue prime point₂ hpoint₂ tH₂ νs μ₂ value
        (Subtype.val ⁻¹' (f '' T)) := by
  have hfTc : IsCompact (f '' T) := hTc.image f.continuous
  have hfTo : IsOpen (f '' T) := f.toHomeomorph.isOpenMap T hTo
  obtain ⟨B₁, hB₁o, hB₁a, hB₁⟩ := form₁.exists_isOpen_padicSquareBranchAtlasGlue_compactOpen_mul
    prime point₁ hpoint₁ tH₁ νs μ₁ hcover₁ value hvalue hTc hTo
  obtain ⟨B₂, hB₂o, hB₂a, hB₂⟩ := form₂.exists_isOpen_padicSquareBranchAtlasGlue_compactOpen_mul
    prime point₂ hpoint₂ tH₂ νs μ₂ hcover₂ value hvalue hfTc hfTo
  set B := B₁ ∩ B₂ ∩ ball value 1 with hBdef
  have hBo : IsOpen B := (hB₁o.inter hB₂o).inter isOpen_ball
  have hBm : MeasurableSet B := hBo.measurableSet
  have hνB0 : νs B ≠ 0 := hBo.measure_ne_zero νs ⟨value, ⟨hB₁a, hB₂a⟩, mem_ball_self one_pos⟩
  have hνBt : νs B ≠ ⊤ :=
    ((measure_mono (inter_subset_right.trans ball_subset_closedBall)).trans_lt
      (isCompact_closedBall value 1).measure_lt_top).ne
  have h1 := hB₁ B (inter_subset_left.trans inter_subset_left) hBm
  have h2 := hB₂ B (inter_subset_left.trans inter_subset_right) hBm
  have hform₂ : Continuous form₂ := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form₂.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  have hset : T ∩ form₁ ⁻¹' B = f ⁻¹' (f '' T ∩ form₂ ⁻¹' B) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_image, hf]
    constructor
    · rintro ⟨hx, hB⟩; exact ⟨⟨x, hx, rfl⟩, hB⟩
    · rintro ⟨⟨y, hy, hyx⟩, hB⟩
      rw [f.injective hyx] at hy
      exact ⟨hy, hB⟩
  have hmeas : MeasurableSet (f '' T ∩ form₂ ⁻¹' B) :=
    hfTo.measurableSet.inter (hBm.preimage hform₂.measurable)
  have hμ : μ₁ (T ∩ form₁ ⁻¹' B) = c * μ₂ (f '' T ∩ form₂ ⁻¹' B) := by
    rw [hset, ← Measure.map_apply f.continuous.measurable hmeas, hmap, Measure.smul_apply,
      smul_eq_mul]
  rw [h1, h2, ← mul_assoc] at hμ
  exact (ENNReal.mul_left_inj hνB0 hνBt).mp hμ

/-- The glue ratio is invariant under isometric transport: for compact open `T, T'`,
`glue¹(T) · glue²(f T') = glue¹(T') · glue²(f T)`. -/
theorem padicSquareBranchAtlasGlue_linearIsometry_cross
    (form₁ : QuadraticForm ℚ_[prime] (Fin r₁ → ℚ_[prime]))
    (form₂ : QuadraticForm ℚ_[prime] (Fin r₂ → ℚ_[prime]))
    (f : (Fin r₁ → ℚ_[prime]) ≃L[ℚ_[prime]] (Fin r₂ → ℚ_[prime])) (hf : ∀ x, form₂ (f x) = form₁ x)
    (point₁ : ℕ → Fin r₁ → ℚ_[prime]) (hpoint₁ : ∀ i, form₁ (point₁ i) ≠ 0)
    (tH₁ : ∀ i, Measure (form₁.anisotropicOrthogonal (point₁ i))) [∀ i, (tH₁ i).IsAddHaarMeasure]
    (hcover₁ : {w | form₁ w ≠ 0} ⊆ ⋃ i, form₁.padicSquareBranchAtlasRegion prime point₁ hpoint₁ i)
    (point₂ : ℕ → Fin r₂ → ℚ_[prime]) (hpoint₂ : ∀ i, form₂ (point₂ i) ≠ 0)
    (tH₂ : ∀ i, Measure (form₂.anisotropicOrthogonal (point₂ i))) [∀ i, (tH₂ i).IsAddHaarMeasure]
    (hcover₂ : {w | form₂ w ≠ 0} ⊆ ⋃ i, form₂.padicSquareBranchAtlasRegion prime point₂ hpoint₂ i)
    (νs : Measure ℚ_[prime]) [νs.IsAddHaarMeasure]
    (μ₁ : Measure (Fin r₁ → ℚ_[prime])) (μ₂ : Measure (Fin r₂ → ℚ_[prime]))
    [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure]
    {value : ℚ_[prime]} (hvalue : value ≠ 0)
    {T T' : Set (Fin r₁ → ℚ_[prime])} (hTc : IsCompact T) (hTo : IsOpen T)
    (hT'c : IsCompact T') (hT'o : IsOpen T') :
    form₁.padicSquareBranchAtlasGlue prime point₁ hpoint₁ tH₁ νs μ₁ value (Subtype.val ⁻¹' T) *
        form₂.padicSquareBranchAtlasGlue prime point₂ hpoint₂ tH₂ νs μ₂ value
          (Subtype.val ⁻¹' (f '' T')) =
      form₁.padicSquareBranchAtlasGlue prime point₁ hpoint₁ tH₁ νs μ₁ value (Subtype.val ⁻¹' T') *
        form₂.padicSquareBranchAtlasGlue prime point₂ hpoint₂ tH₂ νs μ₂ value
          (Subtype.val ⁻¹' (f '' T)) := by
  obtain ⟨c, -, -, hmap⟩ := exists_map_continuousLinearEquiv_eq_smul prime f μ₁ μ₂
  rw [padicSquareBranchAtlasGlue_linearIsometry prime form₁ form₂ f hf point₁ hpoint₁ tH₁ hcover₁
      point₂ hpoint₂ tH₂ hcover₂ νs μ₁ μ₂ hmap hvalue hTc hTo,
    padicSquareBranchAtlasGlue_linearIsometry prime form₁ form₂ f hf point₁ hpoint₁ tH₁ hcover₁
      point₂ hpoint₂ tH₂ hcover₂ νs μ₁ μ₂ hmap hvalue hT'c hT'o]
  ring

end QuadraticMap
