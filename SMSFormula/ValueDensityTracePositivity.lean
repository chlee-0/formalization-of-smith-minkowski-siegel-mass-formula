import SMSFormula.ValueDensityPositiveFunctional
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!
# The density depends only on the trace

This file proves two general lemmas showing that the density of a test depends only on its
restriction to the fiber.  Neither lemma mentions a Gaussian.

Why an extension operator is not enough.  An operator satisfying only "lands in the class" and
"sends nonnegative tests to ones with nonnegative density" is satisfied by the zero operator, and
more generally, with one test of density one at the value, by `f |-> (int f dnu) Psi` for any
positive Radon measure `nu`, whose Riesz measure is exactly `nu`.  So these conditions select no
measure.  The statement that carries the content is that the density depends only on the
restriction to the fiber -- equivalently that a test vanishing on the fiber has density zero there.

Lemma 1, A local sign is a pointwise sign.  If the weighted pushforward has a continuous density and
the test is nonnegative on the preimage of an open set, the density is nonnegative throughout that
open set.  If it were negative somewhere, continuity gives a whole neighbourhood where it is below a
negative constant, and a locally compact base with a measure positive on nonempty open sets and
finite on compacts turns that into a strictly negative integral -- impossible for a nonnegative
integrand.

Lemma 2, trace positivity gives density positivity.  If the test is nonnegative on the fiber and its
negative part is confined to a compact set missing the fiber after adding an arbitrarily small
multiple of a nonnegative auxiliary test, then the density at that value is nonnegative.  The
amplitude `eps` is chosen once, to produce a contradiction; there is no limit, and in particular no
shrinking of a shell thickness.  The image of the compact bad
set is compact, hence closed, hence its complement is an open neighbourhood of the value on whose
preimage lemma 1 applies.

The consequences.  Applying lemma 2 to a test and its negative gives: a test whose restriction to the
fiber vanishes has density zero there; hence two tests with the same restriction have the same
density, so the density descends to a well-defined functional on the image of the restriction map --
with no operator choosing an extension of anything.

Scope.  The compact bad set is a hypothesis here; producing it for the fixed-width Gaussian family
is not done in this file.  Nothing constructs a measure, nothing is adelic, and no test is
exhibited.  The auxiliary test's own density nonnegativity at the value is assumed, not derived.
-/

namespace SMSFormula.TracePositivity

open MeasureTheory Set

variable {M Y : Type*} [TopologicalSpace M] [MeasurableSpace M] [TopologicalSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y] {μ : Measure M} {ν : Measure Y}

/-! ## A local sign is a pointwise sign -/

/-- The analytic core: a continuous function whose integral over every measurable subset of an open
set is nonnegative is itself nonnegative on that open set.  Negativity at a point would, by
continuity, give a whole neighbourhood below a negative constant, and the base measure turns that
into a strictly negative integral. -/
theorem nonneg_of_setIntegral_nonneg [T2Space Y] [LocallyCompactSpace Y] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {d : Y → ℝ} (hd : Continuous d) {V : Set Y} (hV : IsOpen V)
    (h : ∀ s : Set Y, MeasurableSet s → s ⊆ V → 0 ≤ ∫ y in s, d y ∂ν) {y₀ : Y} (hy₀ : y₀ ∈ V) :
    0 ≤ d y₀ := by
  by_contra hneg
  push_neg at hneg
  set c : ℝ := d y₀ / 2 with hc
  have hcneg : c < 0 := by rw [hc]; linarith
  have hy₀c : d y₀ < c := by rw [hc]; linarith
  have hO : IsOpen (V ∩ {y | d y < c}) := hV.inter (isOpen_lt hd continuous_const)
  obtain ⟨K, hK, hy₀K, hKO⟩ := exists_compact_subset hO ⟨hy₀, hy₀c⟩
  set W : Set Y := interior K with hW
  have hWopen : IsOpen W := isOpen_interior
  have hWK : W ⊆ K := interior_subset
  have hWV : W ⊆ V := fun y hy ↦ (hKO (hWK hy)).1
  have hWc : ∀ y ∈ W, d y ≤ c := fun y hy ↦ (hKO (hWK hy)).2.le
  have hνWpos : 0 < ν W := hWopen.measure_pos ν ⟨y₀, hy₀K⟩
  have hνWtop : ν W < ⊤ := lt_of_le_of_lt (measure_mono hWK) hK.measure_lt_top
  have hintK : IntegrableOn d K ν := hd.continuousOn.integrableOn_compact hK
  have hintW : IntegrableOn d W ν := hintK.mono_set hWK
  have hle : ∫ y in W, d y ∂ν ≤ ∫ _y in W, c ∂ν :=
    setIntegral_mono_on hintW (integrableOn_const hνWtop.ne) hWopen.measurableSet hWc
  have hreal : (0 : ℝ) < ν.real W := ENNReal.toReal_pos hνWpos.ne' hνWtop.ne
  have hconst : ∫ _y in W, c ∂ν = ν.real W * c := by
    rw [setIntegral_const, smul_eq_mul]
  have hneg' : ∫ _y in W, c ∂ν < 0 := by
    rw [hconst]
    exact mul_neg_of_pos_of_neg hreal hcneg
  have := h W hWopen.measurableSet hWV
  linarith

omit [TopologicalSpace M] in
/-- Lemma 2.1: nonnegativity of the test on the preimage of an open set gives nonnegativity of the
continuous density throughout that open set. -/
theorem density_nonneg_on_open_of_nonneg_on_preimage [T2Space Y] [LocallyCompactSpace Y]
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {H : M → ℝ} {d : Y → ℝ} {q : M → Y}
    (hqm : Measurable q) (hd : Continuous d)
    (hpush : ∀ s : Set Y, MeasurableSet s → ∫ x in q ⁻¹' s, H x ∂μ = ∫ y in s, d y ∂ν)
    {V : Set Y} (hV : IsOpen V) (hH : ∀ x ∈ q ⁻¹' V, 0 ≤ H x) {y₀ : Y} (hy₀ : y₀ ∈ V) :
    0 ≤ d y₀ := by
  refine nonneg_of_setIntegral_nonneg (ν := ν) hd hV (fun s hs hsV ↦ ?_) hy₀
  rw [← hpush s hs]
  exact setIntegral_nonneg (hs.preimage hqm) fun x hx ↦ hH x (hsV hx)

/-! ## Trace positivity gives density positivity -/

/-- Lemma 2.2, the one-shot argument: if the test is nonnegative on the fiber and, after adding a
small multiple of a nonnegative auxiliary test, its negative part is confined to a compact set
missing the fiber, then the density at that value is nonnegative.  The amplitude is chosen once and
there is no limit -- in particular no shrinking shell thickness. -/
theorem density_nonneg_of_trace_nonneg_of_compact_bad_set [T2Space Y] [LocallyCompactSpace Y]
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {Φ Ψ : M → ℝ} {dΦ dΨ : Y → ℝ} {q : M → Y}
    (hq : Continuous q) (hqm : Measurable q) (hdΦ : Continuous dΦ) (hdΨ : Continuous dΨ) {a : Y}
    (hpush : ∀ c : ℝ, ∀ s : Set Y, MeasurableSet s →
      ∫ x in q ⁻¹' s, (Φ x + c * Ψ x) ∂μ = ∫ y in s, (dΦ y + c * dΨ y) ∂ν)
    (hΨa : 0 ≤ dΨ a)
    (hbad : ∀ ε : ℝ, 0 < ε → ∃ C : Set M, IsCompact C ∧ Disjoint C (q ⁻¹' {a}) ∧
      {x : M | Φ x + ε * Ψ x < 0} ⊆ C) :
    0 ≤ dΦ a := by
  by_contra hneg
  push_neg at hneg
  set ε : ℝ := -dΦ a / (2 * (1 + dΨ a)) with hε
  have hden : (0 : ℝ) < 2 * (1 + dΨ a) := by linarith
  have hεpos : 0 < ε := by
    rw [hε]
    exact div_pos (by linarith) hden
  have hεmul : ε * (2 * (1 + dΨ a)) = -dΦ a := by
    rw [hε]
    field_simp
  have hprod : 0 ≤ ε * dΨ a := mul_nonneg hεpos.le hΨa
  have hcomb : dΦ a + ε * dΨ a < 0 := by nlinarith [hεmul, hεpos, hprod]
  obtain ⟨C, hC, hCdisj, hCsub⟩ := hbad ε hεpos
  have hqC : IsCompact (q '' C) := hC.image hq
  have haC : a ∉ q '' C := by
    rintro ⟨x, hxC, rfl⟩
    exact Set.disjoint_left.mp hCdisj hxC rfl
  have hV : IsOpen ((q '' C)ᶜ) := hqC.isClosed.isOpen_compl
  have hH : ∀ x ∈ q ⁻¹' ((q '' C)ᶜ), 0 ≤ Φ x + ε * Ψ x := by
    intro x hx
    by_contra hlt
    push_neg at hlt
    exact hx ⟨x, hCsub hlt, rfl⟩
  have hkey : 0 ≤ dΦ a + ε * dΨ a :=
    density_nonneg_on_open_of_nonneg_on_preimage (μ := μ) (ν := ν) hqm
      (hdΦ.add (continuous_const.mul hdΨ)) (hpush ε) hV hH haC
  linarith

/-! ## The consequence: the density sees only the trace -/

/-- A test vanishing on the fiber has density zero there -- the statement that actually carries the
coarea content, obtained by running the previous lemma on the test and on its negative. -/
theorem density_eq_zero_of_trace_eq_zero [T2Space Y] [LocallyCompactSpace Y] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {Φ Ψ : M → ℝ} {dΦ dΨ : Y → ℝ} {q : M → Y} (hq : Continuous q)
    (hqm : Measurable q) (hdΦ : Continuous dΦ) (hdΨ : Continuous dΨ) {a : Y}
    (hpush : ∀ c : ℝ, ∀ s : Set Y, MeasurableSet s →
      ∫ x in q ⁻¹' s, (Φ x + c * Ψ x) ∂μ = ∫ y in s, (dΦ y + c * dΨ y) ∂ν)
    (hpushneg : ∀ c : ℝ, ∀ s : Set Y, MeasurableSet s →
      ∫ x in q ⁻¹' s, (-Φ x + c * Ψ x) ∂μ = ∫ y in s, (-dΦ y + c * dΨ y) ∂ν)
    (hΨa : 0 ≤ dΨ a)
    (hbad : ∀ ε : ℝ, 0 < ε → ∃ C : Set M, IsCompact C ∧ Disjoint C (q ⁻¹' {a}) ∧
      {x : M | Φ x + ε * Ψ x < 0} ⊆ C)
    (hbadneg : ∀ ε : ℝ, 0 < ε → ∃ C : Set M, IsCompact C ∧ Disjoint C (q ⁻¹' {a}) ∧
      {x : M | -Φ x + ε * Ψ x < 0} ⊆ C) :
    dΦ a = 0 := by
  have h1 : 0 ≤ dΦ a :=
    density_nonneg_of_trace_nonneg_of_compact_bad_set hq hqm hdΦ hdΨ hpush hΨa hbad
  have h2 : 0 ≤ -dΦ a :=
    density_nonneg_of_trace_nonneg_of_compact_bad_set hq hqm hdΦ.neg hdΨ hpushneg hΨa hbadneg
  linarith

end SMSFormula.TracePositivity

namespace SMSFormula.TracePositivity

variable {M Y : Type*} [TopologicalSpace M]

/-! ## Where the compact bad set comes from, in the compactly supported case -/

/-- The bad set is compact and misses the fiber whenever the test is continuous with compact support
and the auxiliary test is a continuous nonnegative majorant-support function, at least one on that
support.  This needs no Gaussian. -/
theorem isCompact_badSet_of_hasCompactSupport {Φ Ψ : M → ℝ} {q : M → Y} {a : Y} {K : Set M}
    (hK : IsCompact K) (hΦc : Continuous Φ) (hΨc : Continuous Ψ)
    (hsupp : ∀ x ∉ K, Φ x = 0) (hΨnn : ∀ x, 0 ≤ Ψ x) (hΨone : ∀ x ∈ K, 1 ≤ Ψ x)
    (htrace : ∀ x ∈ q ⁻¹' {a}, 0 ≤ Φ x) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set M, IsCompact C ∧ Disjoint C (q ⁻¹' {a}) ∧
      {x : M | Φ x + ε * Ψ x < 0} ⊆ C := by
  have hclosed : IsClosed {x : M | Φ x + ε * Ψ x ≤ 0} :=
    isClosed_le (hΦc.add (continuous_const.mul hΨc)) continuous_const
  refine ⟨K ∩ {x : M | Φ x + ε * Ψ x ≤ 0}, hK.inter_right hclosed, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro x ⟨hxK, hxle⟩ hxa
    have h1 : 0 ≤ Φ x := htrace x hxa
    have h2 : 1 ≤ Ψ x := hΨone x hxK
    simp only [Set.mem_setOf_eq] at hxle
    nlinarith
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    have hxK : x ∈ K := by
      by_contra hxK
      rw [hsupp x hxK] at hx
      nlinarith [hΨnn x]
    exact ⟨hxK, le_of_lt hx⟩

end SMSFormula.TracePositivity
