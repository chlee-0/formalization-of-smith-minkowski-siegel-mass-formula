import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The compact open orbit, and why the positivity witness is free

The general homogeneous-space uniqueness theorem is not needed. Instead of a
quotient-measure development one takes a compact open subgroup `K` of the acting group, forms
`U = K x_0`, which is compact open because the orbit map is already known to be open, and averages
over the probability Haar measure of `K` -- never over the noncompact stabilizer.  One finite-measure
Fubini argument gives proportionality on `U`, and transitivity with regularity propagates it.  No
Bruhat function, no stabilizer Haar, no modular character, no section.

This file proves that no separate positivity witness for the fiber measure is needed: for a
nonzero invariant regular measure on a space the group acts on transitively, every nonempty open
set already has positive measure.  Regularity produces one compact set of positive measure,
transitivity covers it by translates of the open set, a finite subcover suffices, and invariance
makes every member null if the open set were null.

Combined with compactness of `U`, this gives `0 < mu U < infinity` -- exactly the two side
conditions of the lemma that fixes the fiber scalar.

Scope.  This supplies positivity of a nonzero measure on an open set.  It does not prove any
measure nonzero, does not prove the two measures proportional (that is the averaging identity,
`CompactOrbitAveraging`), and does not evaluate either side: the numerical identity
`Lambda(1_U) = mu_nat(U)` is a separate calculation that invariance never performs.  Nothing here
is adelic.
-/

namespace SMSFormula.CompactOrbit

open MeasureTheory Set Pointwise
open scoped ENNReal

variable {G X : Type*} [Group G] [TopologicalSpace X] [MeasurableSpace X] [MulAction G X]
  [TopologicalSpace G] [ContinuousConstSMul G X]

/-- Transitivity, in the form used below: every point is reachable from every other. -/
def IsTransitiveAction (G X : Type*) [Group G] [MulAction G X] : Prop :=
  ∀ x y : X, ∃ g : G, g • x = y

omit [TopologicalSpace G] in
/-- Positivity on open sets.  A nonzero invariant regular measure
on a transitive action gives positive measure to every nonempty open set.  Regularity supplies one
compact set of positive measure, transitivity covers it by translates, compactness reduces to a
finite subcover, and invariance makes each translate as null as the set itself. -/
theorem measure_pos_of_isOpen (μ : Measure X) [SMulInvariantMeasure G X μ] [μ.Regular]
    (htrans : IsTransitiveAction G X) {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (hμ : μ ≠ 0) : 0 < μ U := by
  rcases hUne with ⟨u₀, hu₀⟩
  rw [pos_iff_ne_zero]
  intro hU0
  obtain ⟨C, hCc, hCne⟩ := (Measure.Regular.exists_isCompact_not_null (μ := μ)).2 hμ
  have hcover : C ⊆ ⋃ g : G, g • U := by
    intro x _
    obtain ⟨g, hg⟩ := htrans u₀ x
    exact mem_iUnion.2 ⟨g, ⟨u₀, hu₀, hg⟩⟩
  obtain ⟨t, ht⟩ := hCc.elim_finite_subcover (fun g : G ↦ g • U) (fun g ↦ hU.smul g) hcover
  have hzero : ∀ g : G, μ (g • U) = 0 := fun g ↦ by
    rw [measure_smul]; exact hU0
  have : μ C = 0 := by
    refine le_antisymm ?_ zero_le
    calc μ C ≤ μ (⋃ g ∈ t, g • U) := measure_mono ht
      _ ≤ ∑ g ∈ t, μ (g • U) := measure_biUnion_finset_le _ _
      _ = 0 := by simp [hzero]
  exact hCne this

omit [MeasurableSpace X] [ContinuousConstSMul G X] in
/-- The compact open orbit of the answer's section 2: the image of a compact open set of group
elements under the orbit map is compact (continuity) and open (openness of the orbit map, which is
already available).  Both hypotheses on the set are used, and for different conclusions. -/
theorem isCompact_isOpen_orbit {x₀ : X} {Kset : Set G} (hKc : IsCompact Kset)
    (hKo : IsOpen Kset) (hq : Continuous fun g : G ↦ g • x₀)
    (hqopen : IsOpenMap fun g : G ↦ g • x₀) :
    IsCompact ((fun g : G ↦ g • x₀) '' Kset) ∧ IsOpen ((fun g : G ↦ g • x₀) '' Kset) :=
  ⟨hKc.image hq, hqopen _ hKo⟩

/-- The two side conditions the pinning lemma consumes, both discharged at once on a compact
open orbit: the mass is strictly positive and finite.  Positivity is the previous theorem; finiteness
is compactness against a regular measure. -/
theorem measure_pos_lt_top_of_compactOpen_orbit (μ : Measure X) [SMulInvariantMeasure G X μ]
    [μ.Regular] (htrans : IsTransitiveAction G X) {x₀ : X} {Kset : Set G} (hKc : IsCompact Kset)
    (hKo : IsOpen Kset) (hKne : Kset.Nonempty) (hq : Continuous fun g : G ↦ g • x₀)
    (hqopen : IsOpenMap fun g : G ↦ g • x₀) (hμ : μ ≠ 0) :
    0 < μ ((fun g : G ↦ g • x₀) '' Kset) ∧ μ ((fun g : G ↦ g • x₀) '' Kset) < ⊤ := by
  obtain ⟨hcpt, hopen⟩ := isCompact_isOpen_orbit hKc hKo hq hqopen
  exact ⟨measure_pos_of_isOpen μ htrans hopen (hKne.image _) hμ, hcpt.measure_lt_top⟩

omit [TopologicalSpace G] in
/-- A corollary worth naming, since it is the shape the earlier support statement had: on a
transitive action a nonzero invariant regular measure has no nonempty open null set.  So "support in
the shell" can never be strengthened to emptiness of the complement by this route, but neither can a
fiber measure vanish on a nonempty open piece unless it vanishes identically. -/
theorem eq_zero_of_isOpen_measure_zero (μ : Measure X) [SMulInvariantMeasure G X μ] [μ.Regular]
    (htrans : IsTransitiveAction G X) {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (hU0 : μ U = 0) : μ = 0 := by
  by_contra hμ
  exact absurd hU0 (measure_pos_of_isOpen μ htrans hU hUne hμ).ne'

/-! ## Propagation from one open set to the whole space -/

omit [TopologicalSpace X] [TopologicalSpace G] [ContinuousConstSMul G X] in
/-- A scaled invariant measure is still invariant.  Stated separately because the comparison carries
the scalar explicitly and must never normalise it away. -/
theorem smul_measure_smul_set (nu : Measure X) [SMulInvariantMeasure G X nu] (c : ℝ≥0∞) (g : G)
    (s : Set X) : (c • nu) (g • s) = (c • nu) s := by
  simp [Measure.smul_apply, measure_smul]

omit [TopologicalSpace G] in
/-- Invariance transports the local comparison to every translate.  No measurability of the tested
set is needed: `restrict_apply'` only asks that the restricting set be measurable, and the translate
of an open set is open. -/
theorem restrict_smul_eq [OpensMeasurableSpace X] (μ nu : Measure X) [SMulInvariantMeasure G X μ]
    [SMulInvariantMeasure G X nu] {c : ℝ≥0∞} {U : Set X} (hU : IsOpen U)
    (h : μ.restrict U = (c • nu).restrict U) (g : G) :
    μ.restrict (g • U) = (c • nu).restrict (g • U) := by
  have hUm : MeasurableSet U := hU.measurableSet
  have hgUm : MeasurableSet (g • U) := (hU.smul g).measurableSet
  refine Measure.ext fun s _ ↦ ?_
  have key : ∀ eta : Measure X, (∀ t : Set X, eta (g • t) = eta t) →
      eta.restrict (g • U) s = eta.restrict U (g⁻¹ • s) := by
    intro eta heta
    rw [Measure.restrict_apply' hgUm, Measure.restrict_apply' hUm, ← heta (g⁻¹ • s ∩ U),
      smul_set_inter, smul_inv_smul]
  rw [key μ (measure_smul μ g), key (c • nu) (smul_measure_smul_set nu c g), h]

omit [TopologicalSpace G] in
/-- The propagation step of the answer's section 3.3: a comparison holding on one nonempty open set
propagates to the whole space.  Transitivity makes the translates cover, second countability reduces
that cover to a countable one, and mathlib's spanning-collection extensionality finishes -- no
disjointification, no partition of unity, no section. -/
theorem eq_smul_of_restrict_eq [OpensMeasurableSpace X] [SecondCountableTopology X]
    (μ nu : Measure X) [SMulInvariantMeasure G X μ] [SMulInvariantMeasure G X nu]
    (htrans : IsTransitiveAction G X) {c : ℝ≥0∞} {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (h : μ.restrict U = (c • nu).restrict U) : μ = c • nu := by
  obtain ⟨u₀, hu₀⟩ := hUne
  have hcov : (⋃ g : G, g • U) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨g, hg⟩ := htrans u₀ x
    exact Set.mem_iUnion.2 ⟨g, ⟨u₀, hu₀, hg⟩⟩
  obtain ⟨T, hTc, hT⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun g : G ↦ g • U) fun g ↦ hU.smul g
  rw [hcov] at hT
  exact Measure.ext_of_biUnion_eq_univ hTc hT fun g _ ↦ restrict_smul_eq μ nu hU h g

omit [TopologicalSpace G] in
/-- The cross-multiplied form the answer boxes as (3.1), which is what keeps both raw normalisations
visible: no division is performed and no measure is normalised. -/
theorem smul_measure_eq_smul_measure [OpensMeasurableSpace X] [SecondCountableTopology X]
    (μ nu : Measure X) [SMulInvariantMeasure G X μ] [SMulInvariantMeasure G X nu]
    (htrans : IsTransitiveAction G X) {c : ℝ≥0∞} {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (h : μ.restrict U = (c • nu).restrict U) : (nu U) • μ = (μ U) • nu := by
  have hμ := eq_smul_of_restrict_eq μ nu htrans hU hUne h
  have hmass : μ U = c * nu U := by rw [hμ]; simp
  rw [hmass, hμ, smul_smul, mul_comm]

omit [TopologicalSpace X] [TopologicalSpace G] [ContinuousConstSMul G X] in
/-- The scalar is the ratio of the two local masses, and this is where the earlier positivity and
finiteness are consumed: without `0 < nu U` and `nu U < infinity` the division is meaningless in
`ENNReal`, where `0/0` and `top/top` are both zero. -/
theorem scalar_eq_ratio (μ nu : Measure X) {c : ℝ≥0∞} {U : Set X} (hμ : μ = c • nu)
    (h0 : nu U ≠ 0) (htop : nu U ≠ ⊤) : c = μ U / nu U := by
  have hmass : μ U = c * nu U := by rw [hμ]; simp
  rw [hmass, mul_div_assoc, ENNReal.div_self h0 htop, mul_one]

end SMSFormula.CompactOrbit
