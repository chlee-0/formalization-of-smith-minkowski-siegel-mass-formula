import SMSFormula.HaarMeasureUnimodularInversion
import SMSFormula.RationalCliffordSpinCandidatePlacewiseTranslatedChartMeasure

/-!
# Haar measures under a two-sheet local group chart

A continuous group homomorphism which is a homeomorphism on one identity
neighborhood and whose kernel has at most two points sends Haar measure to
Haar measure on its actual range.  The proof needs no global pointwise
surjectivity onto the ambient target: it uses the tautological surjection onto
the range and one compact positive patch inside the local target chart.

The second result records the unimodularity consequence.  If the range has
one inversion-invariant Haar measure, then the pushed-forward source Haar is
inversion invariant; Haar uniqueness then descends inversion invariance to
the source even though the homomorphism need not be injective.
-/

noncomputable section

open MeasureTheory
open Topology
open TopologicalSpace
open scoped ENNReal

namespace MeasureTheory.TranslatedHomChart

set_option linter.unusedSectionVars false

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H]

/-- A homomorphism whose restriction is a local homeomorphism at the identity
has open range.  The chart target is an open identity neighborhood contained
in the range, so subgroup translations open the whole image. -/
theorem isOpen_range_of_local_chart
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (hone : (1 : G) ∈ e.source) :
    IsOpen (f.range : Set H) := by
  apply Subgroup.isOpen_of_mem_nhds f.range
  have heone : e 1 = (1 : H) := by
    rw [← congrFun hfe 1, map_one]
  have honeTarget : (1 : H) ∈ e.target := by
    simpa [heone] using e.map_source hone
  refine Filter.mem_of_superset (e.open_target.mem_nhds honeTarget) ?_
  intro y hy
  have hyImage : y ∈ e '' e.source := by
    rw [e.image_source_eq_target]
    exact hy
  rcases hyImage with ⟨x, hx, hxy⟩
  exact ⟨x, (congrFun hfe x).trans hxy⟩

/-- The target of an identity chart, viewed inside the actual range of the
homomorphism. -/
def identityTargetToRange (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) : e.target → f.range :=
  fun y => ⟨y.1, by
    have hy : y.1 ∈ e '' e.source := by
      rw [e.image_source_eq_target]
      exact y.2
    rcases hy with ⟨x, hx, hxy⟩
    exact ⟨x, (congrFun hfe x).trans hxy⟩⟩

theorem identityTargetToRange_isOpenEmbedding
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e)
    (hrange : IsOpen (f.range : Set H)) :
    IsOpenEmbedding (identityTargetToRange f e hfe) := by
  let j := identityTargetToRange f e hfe
  apply IsOpenEmbedding.of_comp j hrange.isOpenEmbedding_subtypeVal
  simpa [j, identityTargetToRange, Function.comp_def] using
    e.open_target.isOpenEmbedding_subtypeVal

/-- A two-point-kernel local chart makes the pushforward of Haar measure a
Haar measure on the actual image subgroup. -/
theorem isHaarMeasure_map_rangeRestrict_of_two_point_local_chart
    [LocallyCompactSpace H]
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hf : Continuous f) (hfe : (f : G → H) = e)
    (hone : (1 : G) ∈ e.source)
    (hrange : IsOpen (f.range : Set H))
    (k : G) (hk : f k = 1)
    (hker : ∀ x : G, f x = 1 → x = 1 ∨ x = k)
    (μ : Measure G) [Measure.IsHaarMeasure μ] :
    Measure.IsHaarMeasure (Measure.map f.rangeRestrict μ) := by
  let R := f.range
  let fR : G →* R := f.rangeRestrict
  let j : e.target → R := identityTargetToRange f e hfe
  have hj : IsOpenEmbedding j :=
    identityTargetToRange_isOpenEmbedding f e hfe hrange
  letI : LocallyCompactSpace e.target := e.open_target.locallyCompactSpace
  let y0 : e.target := ⟨e 1, e.map_source hone⟩
  letI : Nonempty e.target := ⟨y0⟩
  let K0 : PositiveCompacts e.target := Classical.arbitrary _
  let K : PositiveCompacts R := K0.map j hj.continuous hj.isOpenMap
  have hKcoe : (K : Set R) = j '' (K0 : Set e.target) := by
    exact PositiveCompacts.coe_map hj.continuous hj.isOpenMap K0
  let b : e.target → G := fun y => (e.toHomeomorphSourceTarget.symm y).1
  let B : Set G := b '' (K0 : Set e.target)
  have hbcont : Continuous b :=
    continuous_subtype_val.comp e.toHomeomorphSourceTarget.symm.continuous
  have hBcompact : IsCompact B := K0.isCompact.image hbcont
  have hpre : fR ⁻¹' (K : Set R) = B ∪ (fun x => k * x) '' B := by
    ext x
    constructor
    · intro hx
      have hx' : fR x ∈ (K : Set R) := hx
      rw [hKcoe] at hx'
      rcases hx' with ⟨y, hyK, hfy⟩
      let u : G := b y
      have huB : u ∈ B := ⟨y, hyK, rfl⟩
      have hfu : f u = y.1 := by
        change f (e.toHomeomorphSourceTarget.symm y).1 = y.1
        rw [congrFun hfe]
        exact congrArg Subtype.val
          (e.toHomeomorphSourceTarget.apply_symm_apply y)
      have hfxu : f (x * u⁻¹) = 1 := by
        rw [map_mul, map_inv, hfu]
        have hfx : f x = y.1 := by
          simpa [j, identityTargetToRange, fR] using
            (congrArg Subtype.val hfy).symm
        rw [hfx]
        simp
      rcases hker (x * u⁻¹) hfxu with hxone | hxk
      · left
        have : x = u := by
          calc
            x = (x * u⁻¹) * u := by simp
            _ = u := by rw [hxone, one_mul]
        rwa [this]
      · right
        refine ⟨u, huB, ?_⟩
        calc
          k * u = (x * u⁻¹) * u := by rw [hxk]
          _ = x := by simp
    · rintro (hx | hx)
      · rcases hx with ⟨y, hyK, rfl⟩
        show fR (b y) ∈ (K : Set R)
        rw [hKcoe]
        refine ⟨y, hyK, Subtype.ext ?_⟩
        change y.1 = f (e.toHomeomorphSourceTarget.symm y).1
        rw [congrFun hfe]
        exact (congrArg Subtype.val
          (e.toHomeomorphSourceTarget.apply_symm_apply y)).symm
      · rcases hx with ⟨u, huB, rfl⟩
        change fR (k * u) ∈ K
        have hu : fR u ∈ K := by
          apply (show u ∈ B → fR u ∈ K from ?_) huB
          rintro ⟨y, hyK, rfl⟩
          show fR (b y) ∈ (K : Set R)
          rw [hKcoe]
          refine ⟨y, hyK, Subtype.ext ?_⟩
          change y.1 = f (e.toHomeomorphSourceTarget.symm y).1
          rw [congrFun hfe]
          exact (congrArg Subtype.val
            (e.toHomeomorphSourceTarget.apply_symm_apply y)).symm
        have hfRk : fR k = 1 := Subtype.ext hk
        rw [map_mul, hfRk, one_mul]
        exact hu
  have hprecompact : IsCompact (fR ⁻¹' (K : Set R)) := by
    rw [hpre]
    exact hBcompact.union (hBcompact.image (continuous_const.mul continuous_id))
  have hfR : Continuous fR :=
    continuous_induced_rng.mpr hf
  let m : Measure R := Measure.map fR μ
  letI : Measure.IsMulLeftInvariant m :=
    MeasureTheory.isMulLeftInvariant_map fR.toMulHom hfR.measurable
      f.rangeRestrict_surjective
  have hmopen : Measure.IsOpenPosMeasure m :=
    hfR.isOpenPosMeasure_map f.rangeRestrict_surjective
  letI : Measure.IsOpenPosMeasure m := hmopen
  have hmKpos : m (K : Set R) ≠ 0 :=
    ne_of_gt (Measure.measure_pos_of_nonempty_interior
      m K.interior_nonempty)
  have hmKfinite : m (K : Set R) ≠ ∞ := by
    change (Measure.map fR μ) (K : Set R) ≠ ∞
    rw [Measure.map_apply hfR.measurable K.isCompact.measurableSet]
    exact ne_of_lt hprecompact.measure_lt_top
  exact Measure.isHaarMeasure_of_isCompact_nonempty_interior
    m K K.isCompact K.interior_nonempty hmKpos hmKfinite

end MeasureTheory.TranslatedHomChart

namespace MeasureTheory.Measure

/-- If one Haar measure on a group is inversion invariant, then every regular
Haar measure on that group is inversion invariant. -/
theorem isInvInvariant_of_isHaarMeasure_of_exists
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [IsHaarMeasure μ]
    [IsHaarMeasure ν] [IsInvInvariant ν] :
    IsInvInvariant μ := by
  have hμ : μ = haarScalarFactor μ ν • ν :=
    isMulLeftInvariant_eq_smul μ ν
  constructor
  rw [hμ, Measure.inv_def, Measure.map_smul, Measure.map_inv_eq_self]

/-- A two-sided Haar measure on a second-countable locally compact group is
inversion invariant. -/
theorem isInvInvariant_of_isMulRightInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ] :
    IsInvInvariant μ := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul μ.inv μ
  have hdouble : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc,
      smul_smul, pow_two]
  have mueq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at hdouble
    simpa only [inv_involutive, Function.Involutive.comp_self,
      Measure.map_id] using hdouble
  have K : PositiveCompacts G := Classical.arbitrary _
  have hc_sq : c ^ 2 = 1 ^ 2 := by
    apply (ENNReal.mul_left_inj
      (measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1
    conv_rhs => rw [mueq]
    simp
  have hc_one : c = 1 :=
    (ENNReal.pow_right_strictMono two_ne_zero).injective hc_sq
  rw [hc, hc_one, one_smul]

/-- Inversion invariance descends from a Haar pushforward through a group
homomorphism. Injectivity of the homomorphism is not required. -/
theorem isInvInvariant_of_map_of_isHaarMeasure
    {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) [IsHaarMeasure μ]
    (f : G →* H) (hf : Measurable f)
    [IsHaarMeasure (Measure.map f μ)]
    [IsInvInvariant (Measure.map f μ)] :
    IsInvInvariant μ := by
  letI : IsMulRightInvariant (Measure.map f μ) :=
    isMulRightInvariant_of_isInvInvariant (Measure.map f μ)
  have hright : IsMulRightInvariant μ := by
    refine ⟨fun g => ?_⟩
    let νg : Measure G := Measure.map (fun x => x * g) μ
    let c : ℝ≥0∞ := haarScalarFactor νg μ
    have hc : νg = c • μ :=
      isMulLeftInvariant_eq_smul_of_regular νg μ
    have hpush : Measure.map f νg = Measure.map f μ := by
      change Measure.map f (Measure.map (fun x => x * g) μ) =
        Measure.map f μ
      calc
        Measure.map f (Measure.map (fun x => x * g) μ) =
            Measure.map (fun y => y * f g) (Measure.map f μ) := by
          rw [Measure.map_map hf (measurable_mul_const g),
            Measure.map_map (measurable_mul_const (f g)) hf]
          congr 1
          funext x
          simp
        _ = Measure.map f μ := map_mul_right_eq_self (Measure.map f μ) (f g)
    have hm : Measure.map f μ = c • Measure.map f μ := by
      calc
        Measure.map f μ = Measure.map f νg := hpush.symm
        _ = Measure.map f (c • μ) := by rw [hc]
        _ = c • Measure.map f μ := Measure.map_smul c μ f
    have K : PositiveCompacts H := Classical.arbitrary _
    have hc_one : c = 1 := by
      apply (ENNReal.mul_left_inj
        (measure_pos_of_nonempty_interior
          (Measure.map f μ) K.interior_nonempty).ne'
        K.isCompact.measure_lt_top.ne).1
      conv_rhs => rw [hm]
      simp
    change νg = μ
    rw [hc, hc_one, one_smul]
  letI : IsMulRightInvariant μ := hright
  exact isInvInvariant_of_isMulRightInvariant μ

end MeasureTheory.Measure
