import SMSFormula.UltrametricApproximatesLinearImage

/-!
# Local change of variables on a clopen ball, ultrametric case

For a strictly differentiable map with invertible derivative `A` on an
ultrametric proper space, a small closed ball `U` around the point is clopen, `f`
is injective on it, and the ball law holds on every closed ball meeting `U`: two
ultrametric closed balls are nested or disjoint. Closed balls of positive radius
form a basis and a π-system, so the two finite measures `S ↦ ν (f '' (S ∩ U))`
and `S ↦ mod(A) μ (S ∩ U)` coincide. This gives an integrated change of
variables on the exact set `U`, for every function, with the constant modulus of
`A` (a genuinely non-archimedean feature). Haar measures are supplied; no chart,
section or normalization is chosen.
-/

noncomputable section

open Metric Set Function MeasureTheory
open scoped NNReal ENNReal Topology

section UltrametricBalls

variable {E : Type*} [PseudoMetricSpace E] [IsUltrametricDist E]

/-- Closed balls of positive radius form a topological basis, ultrametric case. -/
theorem IsUltrametricDist.isTopologicalBasis_closedBall :
    TopologicalSpace.IsTopologicalBasis {U : Set E | ∃ y : E, ∃ s : ℝ, 0 < s ∧ U = closedBall y s} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨y, s, hs, rfl⟩
    exact IsUltrametricDist.isOpen_closedBall y hs.ne'
  · intro x U hx hU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
    refine ⟨closedBall x (ε / 2), ⟨x, ε / 2, half_pos hε, rfl⟩, mem_closedBall_self (half_pos hε).le,
      (closedBall_subset_ball (half_lt_self hε)).trans hball⟩

/-- Closed balls of positive radius form a π-system, ultrametric case. -/
theorem IsUltrametricDist.isPiSystem_closedBall :
    IsPiSystem {U : Set E | ∃ y : E, ∃ s : ℝ, 0 < s ∧ U = closedBall y s} := by
  rintro _ ⟨x, r, hr, rfl⟩ _ ⟨y, s, hs, rfl⟩ hne
  rcases IsUltrametricDist.closedBall_subset_trichotomy (x := x) (y := y) (r := r) (s := s) with
    h | h | h
  · exact ⟨x, r, hr, inter_eq_left.mpr h⟩
  · exact ⟨y, s, hs, inter_eq_right.mpr h⟩
  · exact absurd hne (not_nonempty_iff_eq_empty.mpr h.inter_eq)

end UltrametricBalls

namespace HasStrictFDerivAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [IsUltrametricDist E] [CompleteSpace E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology E]
    {f : E → F} {A : E ≃L[𝕜] F} {a : E}

/-- Local change of variables on every sufficiently small exact clopen ball
around the point, with the constant Haar modulus of the strict derivative. -/
theorem exists_forall_lintegral_image_closedBall
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] [ν.IsAddLeftInvariant]
    (hf : HasStrictFDerivAt f (A : E →L[𝕜] F) a) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → IsOpen (closedBall a r) ∧ InjOn f (closedBall a r) ∧
      ContinuousOn f (closedBall a r) ∧ ∀ g : F → ℝ≥0∞, ∫⁻ y in f '' closedBall a r, g y ∂ν =
        (Measure.addHaarScalarFactor (ν.map A.symm) μ : ℝ≥0∞) *
          ∫⁻ x in closedBall a r, g (f x) ∂μ := by
  classical
  set N : ℝ≥0 := ‖(A.symm : F →L[𝕜] E)‖₊ with hN
  set c : ℝ≥0 := N⁻¹ / 2 with hcdef
  have hc : N * c < 1 := by
    rcases eq_or_ne N 0 with h0 | h0
    · rw [h0, zero_mul]; exact one_pos
    · rw [hcdef, mul_div_assoc', mul_inv_cancel₀ h0]
      exact NNReal.half_lt_self one_ne_zero
  have hpos : Subsingleton E ∨ 0 < c :=
    A.subsingleton_or_nnnorm_symm_pos.imp id fun h ↦ half_pos (inv_pos.2 h)
  have hinj : Subsingleton E ∨ c < N⁻¹ :=
    A.subsingleton_or_nnnorm_symm_pos.imp id fun h ↦
      NNReal.half_lt_self (inv_pos.2 h).ne'
  obtain ⟨s, hs, happ⟩ := hf.approximates_deriv_on_nhds hpos
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨δ, hδ, fun r hr0 hrδ ↦ ?_⟩
  set U := closedBall a r with hU
  have hUs : U ⊆ s := (closedBall_subset_ball hrδ).trans hball
  have hUapp := happ.mono_set hUs
  have hUopen : IsOpen U := IsUltrametricDist.isOpen_closedBall a hr0.ne'
  have hUmeas : MeasurableSet U := isClosed_closedBall.measurableSet
  have hUinj : InjOn f U := hUapp.injOn hinj
  -- the ball law on every closed ball inside `U`
  set m : ℝ≥0 := Measure.addHaarScalarFactor (ν.map A.symm) μ with hm
  have hlaw : ∀ (y : E) (t : ℝ), closedBall y t ⊆ U →
      ν (f '' closedBall y t) = m * μ (closedBall y t) := fun y t hsub ↦
    (hUapp.mono_set hsub).measure_image_closedBall μ ν hc
  -- `f` restricted to `U` is a measurable embedding
  let e := hUapp.toOpenPartialHomeomorph f U hinj hUopen
  let φ : U → F := fun x ↦ f x
  have hφ : MeasurableEmbedding φ := by
    have h1 : MeasurableEmbedding (e.toHomeomorphSourceTarget : e.source → e.target) :=
      e.toHomeomorphSourceTarget.measurableEmbedding
    have h2 : MeasurableEmbedding (Subtype.val : e.target → F) :=
      MeasurableEmbedding.subtype_coe e.open_target.measurableSet
    exact h2.comp h1
  have hcoe : MeasurableEmbedding (Subtype.val : U → E) := MeasurableEmbedding.subtype_coe hUmeas
  have hrange : range φ = f '' U := (image_eq_range f U).symm
  -- the two measures on `E`
  set lam₁ : Measure E := (ν.comap φ).map Subtype.val with hlam₁
  set lam₂ : Measure E := (m : ℝ≥0∞) • μ.restrict U with hlam₂
  have hlam₁apply : ∀ S, MeasurableSet S → lam₁ S = ν (f '' (S ∩ U)) := by
    intro S hS
    rw [hlam₁, Measure.map_apply measurable_subtype_coe hS, hφ.comap_apply]
    congr 1
    ext w
    simp only [mem_image, mem_preimage, mem_inter_iff, φ, Subtype.exists]
    constructor
    · rintro ⟨x, hxU, hxS, rfl⟩; exact ⟨x, ⟨hxS, hxU⟩, rfl⟩
    · rintro ⟨x, ⟨hxS, hxU⟩, rfl⟩; exact ⟨x, hxU, hxS, rfl⟩
  have hlam₂apply : ∀ S, MeasurableSet S → lam₂ S = m * μ (S ∩ U) := by
    intro S hS
    rw [hlam₂, Measure.smul_apply, Measure.restrict_apply hS, smul_eq_mul]
  have hUlt : μ U < ∞ := (isCompact_closedBall a r).measure_lt_top
  haveI : IsFiniteMeasure lam₂ := by
    refine ⟨?_⟩
    rw [hlam₂apply univ MeasurableSet.univ, univ_inter]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hUlt
  have hball_eq : ∀ (y : E) (t : ℝ), 0 < t → lam₁ (closedBall y t) = lam₂ (closedBall y t) := by
    intro y t ht
    rw [hlam₁apply _ isClosed_closedBall.measurableSet, hlam₂apply _ isClosed_closedBall.measurableSet]
    rcases IsUltrametricDist.closedBall_subset_trichotomy (x := y) (y := a) (r := t) (s := r) with
      h | h | h
    · rw [inter_eq_left.mpr h]; exact hlaw y t h
    · rw [inter_eq_right.mpr h]; exact hlaw a r subset_rfl
    · rw [h.inter_eq, image_empty, measure_empty, measure_empty, mul_zero]
  have hext : lam₁ = lam₂ := by
    refine (MeasureTheory.ext_of_generate_finite _
      ((BorelSpace.measurable_eq).trans
        IsUltrametricDist.isTopologicalBasis_closedBall.borel_eq_generateFrom)
      IsUltrametricDist.isPiSystem_closedBall ?_ ?_).symm
    · rintro _ ⟨y, t, ht, rfl⟩
      exact (hball_eq y t ht).symm
    · rw [hlam₁apply univ MeasurableSet.univ, hlam₂apply univ MeasurableSet.univ, univ_inter]
      exact (hlaw a r subset_rfl).symm
  refine ⟨hUopen, hUinj, hUapp.continuousOn, fun g ↦ ?_⟩
  calc ∫⁻ y in f '' U, g y ∂ν
      = ∫⁻ y, g y ∂((ν.comap φ).map φ) := by rw [hφ.map_comap, hrange]
    _ = ∫⁻ x, g (φ x) ∂(ν.comap φ) := hφ.lintegral_map g
    _ = ∫⁻ x, g (f x) ∂lam₁ := by rw [hlam₁, hcoe.lintegral_map]
    _ = ∫⁻ x, g (f x) ∂lam₂ := by rw [hext]
    _ = (m : ℝ≥0∞) * ∫⁻ x in U, g (f x) ∂μ := by rw [hlam₂, lintegral_smul_measure, smul_eq_mul]

/-- Local change of variables on an exact clopen ball around the point: images
of lintegrals carry the constant Haar modulus of the strict derivative. -/
theorem exists_lintegral_image_closedBall
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] [ν.IsAddLeftInvariant]
    (hf : HasStrictFDerivAt f (A : E →L[𝕜] F) a) :
    ∃ r > 0, IsOpen (closedBall a r) ∧ InjOn f (closedBall a r) ∧
      ∀ g : F → ℝ≥0∞, ∫⁻ y in f '' closedBall a r, g y ∂ν =
        (Measure.addHaarScalarFactor (ν.map A.symm) μ : ℝ≥0∞) *
          ∫⁻ x in closedBall a r, g (f x) ∂μ := by
  obtain ⟨δ, hδ, h⟩ := hf.exists_forall_lintegral_image_closedBall μ ν
  obtain ⟨h1, h2, -, h4⟩ := h _ (half_pos hδ) (half_lt_self hδ)
  exact ⟨δ / 2, half_pos hδ, h1, h2, h4⟩

end HasStrictFDerivAt
