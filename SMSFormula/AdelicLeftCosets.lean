import SMSFormula.AdelicMeasureLemmas
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Adelic left-action quotients and transversals

This module contains the project-local orbit relation for left multiplication
by a subgroup, the quotient `Gamma \ G`, quotient maps, chosen and measurable
transversal APIs, and fundamental-domain mass formulae used by the
finite-adelic quotient-volume interface.

In the names `IsLeftCosetRelated`, `leftCosetSet`, and `leftCosetMap`,
"left" records the **action side**: the equivalence classes are the orbits
`Gamma * x`.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

universe u
universe v
universe w

variable {n : ℕ}

open MeasureTheory
open scoped ENNReal

/-! ## Left-action quotients -/

/-- The orbit relation for the left action of a subgroup `Gamma` on a group
`G`: two elements are related when they differ by a left factor from
`Gamma`. -/
def IsLeftCosetRelated {G : Type u} [Group G]
    (Gamma : Subgroup G) (x y : G) : Prop :=
  ∃ gamma : Gamma, y = (gamma : G) * x

lemma IsLeftCosetRelated.refl {G : Type u} [Group G]
    (Gamma : Subgroup G) (x : G) :
    IsLeftCosetRelated Gamma x x := by
  refine ⟨1, ?_⟩
  simp

lemma IsLeftCosetRelated.symm {G : Type u} [Group G]
    {Gamma : Subgroup G} {x y : G}
    (hxy : IsLeftCosetRelated Gamma x y) :
    IsLeftCosetRelated Gamma y x := by
  rcases hxy with ⟨gamma, rfl⟩
  refine ⟨gamma⁻¹, ?_⟩
  simp

lemma IsLeftCosetRelated.trans {G : Type u} [Group G]
    {Gamma : Subgroup G} {x y z : G}
    (hxy : IsLeftCosetRelated Gamma x y)
    (hyz : IsLeftCosetRelated Gamma y z) :
    IsLeftCosetRelated Gamma x z := by
  rcases hxy with ⟨gamma1, rfl⟩
  rcases hyz with ⟨gamma2, rfl⟩
  refine ⟨gamma2 * gamma1, ?_⟩
  simp [mul_assoc]

/-- The setoid attached to the left-action orbit relation. -/
def leftCosetSetoid {G : Type u} [Group G]
    (Gamma : Subgroup G) : Setoid G where
  r := IsLeftCosetRelated Gamma
  iseqv := ⟨
    fun x => IsLeftCosetRelated.refl Gamma x,
    fun {_x _y} h => IsLeftCosetRelated.symm h,
    fun {_x _y _z} hxy hyz => IsLeftCosetRelated.trans hxy hyz⟩

/-- The quotient `Gamma \ G` by the left action of `Gamma`. -/
def leftCosetSet {G : Type u} [Group G]
    (Gamma : Subgroup G) : Type u :=
  Quot (leftCosetSetoid Gamma)

/-- Preferred descriptive alias for the quotient by the left action of
`Gamma`. -/
abbrev LeftActionQuotient {G : Type u} [Group G]
    (Gamma : Subgroup G) : Type u :=
  leftCosetSet Gamma

/-- The quotient map `G -> Gamma \ G` for the project-local left-action
quotient. -/
def leftCosetMap {G : Type u} [Group G]
    (Gamma : Subgroup G) : G → leftCosetSet Gamma :=
  Quot.mk (leftCosetSetoid Gamma)

/-- Preferred descriptive alias for the left-action quotient map. -/
abbrev leftActionQuotientMap {G : Type u} [Group G]
    (Gamma : Subgroup G) : G → LeftActionQuotient Gamma :=
  leftCosetMap Gamma

lemma leftCoset_mk_eq_iff {G : Type u} [Group G]
    (Gamma : Subgroup G) (x y : G) :
    Quot.mk (leftCosetSetoid Gamma) x =
        Quot.mk (leftCosetSetoid Gamma) y ↔
      IsLeftCosetRelated Gamma x y := by
  constructor
  · intro hxy
    simpa [leftCosetSetoid] using Quotient.exact hxy
  · intro hxy
    exact Quotient.sound hxy

/-- A fixed choice of one representative from each left-action orbit, using
Lean's quotient representative `Quot.out`.  "Chosen" is intentional: this is
not a claim of mathematical naturality. -/
noncomputable def leftCosetRepresentativeSlice {G : Type u} [Group G]
    (Gamma : Subgroup G) : Set G :=
  Set.range (fun C : leftCosetSet Gamma => Quot.out C)

/-- The chosen quotient-representative slice is countable when the
left-coset quotient is countable. -/
theorem leftCosetRepresentativeSlice_countable {G : Type u} [Group G]
    (Gamma : Subgroup G) [Countable (leftCosetSet Gamma)] :
    (leftCosetRepresentativeSlice Gamma).Countable := by
  simpa [leftCosetRepresentativeSlice] using
    Set.countable_range (fun C : leftCosetSet Gamma => Quot.out C)

/-- The chosen quotient-representative slice is measurable when the
left-coset quotient is countable and singleton sets are measurable. -/
theorem leftCosetRepresentativeSlice_measurableSet_of_countable
    {G : Type u} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (Gamma : Subgroup G) [Countable (leftCosetSet Gamma)] :
    MeasurableSet (leftCosetRepresentativeSlice Gamma) :=
  (leftCosetRepresentativeSlice_countable Gamma).measurableSet

/-- The chosen left-coset representatives cover the ambient group up to a
left factor from the subgroup. -/
theorem leftCosetRepresentativeSlice_decomp {G : Type u} [Group G]
    (Gamma : Subgroup G) :
    ∀ x : G, ∃ gamma : Gamma, ∃ c : G,
      c ∈ leftCosetRepresentativeSlice Gamma ∧ x = (gamma : G) * c := by
  intro x
  let C : leftCosetSet Gamma := Quot.mk (leftCosetSetoid Gamma) x
  let c : G := Quot.out C
  have hc : c ∈ leftCosetRepresentativeSlice Gamma := ⟨C, rfl⟩
  have hmk :
      Quot.mk (leftCosetSetoid Gamma) c =
        Quot.mk (leftCosetSetoid Gamma) x := by
    simp [C, c]
  rcases (leftCoset_mk_eq_iff Gamma c x).mp hmk with ⟨gamma, hx⟩
  exact ⟨gamma, c, hc, hx⟩

set_option backward.isDefEq.respectTransparency false in
/-- The chosen left-coset representative in a coset is unique: two chosen
representatives that differ by a left subgroup element are equal. -/
theorem leftCosetRepresentativeSlice_unique {G : Type u} [Group G]
    (Gamma : Subgroup G) :
    ∀ c₁ c₂ : G,
      c₁ ∈ leftCosetRepresentativeSlice Gamma →
      c₂ ∈ leftCosetRepresentativeSlice Gamma →
      c₂ * c₁⁻¹ ∈ Gamma →
      c₂ = c₁ := by
  intro c₁ c₂ hc₁ hc₂ hmem
  rcases hc₁ with ⟨C₁, rfl⟩
  rcases hc₂ with ⟨C₂, rfl⟩
  have hrel :
      IsLeftCosetRelated Gamma (Quot.out C₁) (Quot.out C₂) := by
    refine ⟨⟨Quot.out C₂ * (Quot.out C₁)⁻¹, hmem⟩, ?_⟩
    simp [mul_assoc]
  have hmk :
      Quot.mk (leftCosetSetoid Gamma) (Quot.out C₁) =
        Quot.mk (leftCosetSetoid Gamma) (Quot.out C₂) :=
    (leftCoset_mk_eq_iff Gamma (Quot.out C₁) (Quot.out C₂)).mpr hrel
  have hC : C₁ = C₂ := by
    calc
      C₁ = Quot.mk (leftCosetSetoid Gamma) (Quot.out C₁) := (Quot.out_eq C₁).symm
      _ = Quot.mk (leftCosetSetoid Gamma) (Quot.out C₂) := hmk
      _ = C₂ := Quot.out_eq C₂
  rw [hC]

/-- A concrete left-coset transversal for a subgroup.

This packages the two set-theoretic facts needed downstream from any
measurable selector: every element has a representative in the slice, and two
chosen slice representatives differing by a left subgroup factor are equal. -/
structure IsLeftCosetTransversal {G : Type u} [Group G]
    (Gamma : Subgroup G) (S : Set G) : Prop where
  decomp : ∀ x : G, ∃ gamma : Gamma, ∃ c : G,
    c ∈ S ∧ x = (gamma : G) * c
  unique : ∀ c₁ c₂ : G,
    c₁ ∈ S →
    c₂ ∈ S →
    c₂ * c₁⁻¹ ∈ Gamma →
    c₂ = c₁

/-- The chosen `Quot.out` representative slice is a left-coset
transversal. -/
theorem leftCosetRepresentativeSlice_isLeftCosetTransversal {G : Type u}
    [Group G] (Gamma : Subgroup G) :
    IsLeftCosetTransversal Gamma (leftCosetRepresentativeSlice Gamma) where
  decomp := leftCosetRepresentativeSlice_decomp Gamma
  unique := leftCosetRepresentativeSlice_unique Gamma

namespace IsLeftCosetTransversal

/-- The left translates of any concrete left-coset transversal cover the
ambient group. -/
theorem iUnion_leftTranslate {G : Type u} [Group G]
    {Gamma : Subgroup G} {S : Set G}
    (hS : IsLeftCosetTransversal Gamma S) :
    (⋃ gamma : Gamma, (fun c : G => (gamma : G) * c) '' S) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    rcases hS.decomp x with ⟨gamma, c, hc, rfl⟩
    exact Set.mem_iUnion.mpr ⟨gamma, ⟨c, hc, rfl⟩⟩

/-- Distinct left translates of any concrete left-coset transversal are
disjoint. -/
theorem pairwiseDisjoint_leftTranslate {G : Type u} [Group G]
    {Gamma : Subgroup G} {S : Set G}
    (hS : IsLeftCosetTransversal Gamma S) :
    Pairwise fun gamma delta : Gamma =>
      Disjoint
        ((fun c : G => (gamma : G) * c) '' S)
        ((fun c : G => (delta : G) * c) '' S) := by
  intro gamma delta hne
  rw [Set.disjoint_left]
  intro x hxgamma hxdelta
  rcases hxgamma with ⟨c₁, hc₁, rfl⟩
  rcases hxdelta with ⟨c₂, hc₂, hx₂⟩
  have hc₂_eq : c₂ = ((delta : G)⁻¹ * (gamma : G)) * c₁ := by
    calc
      c₂ = 1 * c₂ := by simp
      _ = (delta : G)⁻¹ * ((delta : G) * c₂) := by
          simp
      _ = (delta : G)⁻¹ * ((gamma : G) * c₁) := by
          exact congrArg (fun y : G => (delta : G)⁻¹ * y) hx₂
      _ = ((delta : G)⁻¹ * (gamma : G)) * c₁ := by
          simp [mul_assoc]
  have hfactor_mem : ((delta : G)⁻¹ * (gamma : G)) ∈ Gamma := by
    simpa using ((delta⁻¹ * gamma : Gamma).property)
  have hmem : c₂ * c₁⁻¹ ∈ Gamma := by
    have hcalc :
        c₂ * c₁⁻¹ = (delta : G)⁻¹ * (gamma : G) := by
      calc
        c₂ * c₁⁻¹ = (((delta : G)⁻¹ * (gamma : G)) * c₁) * c₁⁻¹ := by
            rw [hc₂_eq]
        _ = (delta : G)⁻¹ * (gamma : G) := by
            simp [mul_assoc]
    rw [hcalc]
    exact hfactor_mem
  have hc₂c₁ : c₂ = c₁ := hS.unique c₁ c₂ hc₁ hc₂ hmem
  have hgamma_delta_coe : (gamma : G) = (delta : G) := by
    have hmul : (delta : G) * c₁ = (gamma : G) * c₁ := by
      simpa [hc₂c₁] using hx₂
    exact (mul_right_cancel hmul).symm
  exact hne (Subtype.ext hgamma_delta_coe)

/-- The balanced arbitrary-scale mass identity for a measurable transversal
of a finite subgroup.  The finite family of disjoint left translates of the
transversal covers the ambient group, and left invariance gives every
translate the same mass. -/
theorem natCard_mul_measure_eq_univ {G : Type u}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    {Gamma : Subgroup G} [Fintype Gamma] {S : Set G}
    {μ : Measure G} [Measure.IsMulLeftInvariant μ]
    (hS : IsLeftCosetTransversal Gamma S)
    (hmeas : MeasurableSet S) :
    (Nat.card Gamma : ℝ≥0∞) * μ S = μ Set.univ := by
  have htranslate_meas :
      ∀ gamma : Gamma, MeasurableSet ((fun c : G => (gamma : G) * c) '' S) := by
    intro gamma
    exact (measurableEmbedding_mulLeft (gamma : G)).measurableSet_image.2 hmeas
  have htranslate_measure :
      ∀ gamma : Gamma, μ ((fun c : G => (gamma : G) * c) '' S) = μ S := by
    intro gamma
    let L : G → G := fun c => (gamma : G) * c
    have hpre : L ⁻¹' (L '' S) = S := by
      ext c
      constructor
      · intro hc
        rcases hc with ⟨s, hs, hcs⟩
        have hcs' : c = s := by
          exact (mul_left_cancel hcs).symm
        simpa [hcs'] using hs
      · intro hc
        exact ⟨c, hc, rfl⟩
    calc
      μ (L '' S) = (Measure.map L μ) (L '' S) := by
          rw [map_mul_left_eq_self μ (gamma : G)]
      _ = μ (L ⁻¹' (L '' S)) := by
          rw [Measure.map_apply (measurable_const_mul (gamma : G))
            (htranslate_meas gamma)]
      _ = μ S := by
          rw [hpre]
  have hsum_univ :
      μ Set.univ =
        ∑ gamma : Gamma, μ ((fun c : G => (gamma : G) * c) '' S) := by
    calc
      μ Set.univ =
          μ (⋃ gamma : Gamma, (fun c : G => (gamma : G) * c) '' S) := by
            rw [hS.iUnion_leftTranslate]
      _ = ∑' gamma : Gamma, μ ((fun c : G => (gamma : G) * c) '' S) := by
            exact measure_iUnion
              (fun gamma delta hne => hS.pairwiseDisjoint_leftTranslate hne)
              htranslate_meas
      _ = ∑ gamma : Gamma, μ ((fun c : G => (gamma : G) * c) '' S) := by
            rw [tsum_fintype]
  have hsum_const :
      (∑ gamma : Gamma, μ S) = (Nat.card Gamma : ℝ≥0∞) * μ S := by
    rw [Finset.sum_const, Nat.card_eq_fintype_card]
    simp [nsmul_eq_mul]
  calc
    (Nat.card Gamma : ℝ≥0∞) * μ S =
        ∑ gamma : Gamma, μ S := hsum_const.symm
    _ = ∑ gamma : Gamma, μ ((fun c : G => (gamma : G) * c) '' S) := by
        exact Finset.sum_congr rfl fun gamma _ => (htranslate_measure gamma).symm
    _ = μ Set.univ := hsum_univ.symm

/-- Arbitrary-scale measure of a measurable finite left-coset transversal.

No normalization or finiteness hypothesis on the ambient measure is needed:
the positive finite subgroup cardinality can be inverted safely in
`ENNReal`. -/
theorem measure_eq_univ_mul_inv_natCard {G : Type u}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    {Gamma : Subgroup G} [Fintype Gamma] {S : Set G}
    {μ : Measure G} [Measure.IsMulLeftInvariant μ]
    (hS : IsLeftCosetTransversal Gamma S)
    (hmeas : MeasurableSet S) :
    μ S =
      μ Set.univ * ENNReal.ofReal (1 / (Nat.card Gamma : ℝ)) := by
  have hcard_pos : 0 < Nat.card Gamma := by
    haveI : Nonempty Gamma := ⟨1⟩
    exact Nat.card_pos
  have hprod :
      (Nat.card Gamma : ℝ≥0∞) * μ S = μ Set.univ :=
    hS.natCard_mul_measure_eq_univ hmeas
  let c : ℝ≥0∞ := (Nat.card Gamma : ℝ≥0∞)
  have hc0 : c ≠ 0 := by
    change (Nat.card Gamma : ℝ≥0∞) ≠ 0
    exact_mod_cast Nat.ne_of_gt hcard_pos
  have hctop : c ≠ ∞ := by
    simp [c]
  have hcR : 0 < (Nat.card Gamma : ℝ) := by
    exact_mod_cast hcard_pos
  calc
    μ S = 1 * μ S := by simp
    _ = (c⁻¹ * c) * μ S := by
        rw [mul_comm c⁻¹ c, ENNReal.mul_inv_cancel hc0 hctop]
    _ = c⁻¹ * (c * μ S) := by
        rw [mul_assoc]
    _ = c⁻¹ * μ Set.univ := by
        rw [hprod]
    _ = μ Set.univ * (ENNReal.ofReal 1 / c) := by
        simp [div_eq_mul_inv, mul_comm]
    _ =
        μ Set.univ *
          (ENNReal.ofReal 1 / ENNReal.ofReal (Nat.card Gamma : ℝ)) := by
        rw [ENNReal.ofReal_natCast]
    _ =
        μ Set.univ *
          ENNReal.ofReal (1 / (Nat.card Gamma : ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (x := 1) hcR]

/-- Normalized measure of any measurable finite left-coset transversal.

This is the probability-measure specialization of the arbitrary-scale
transversal formula. -/
theorem measure_eq_inv_natCard {G : Type u}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    {Gamma : Subgroup G} [Fintype Gamma] {S : Set G}
    {μ : Measure G} [Measure.IsMulLeftInvariant μ]
    (hS : IsLeftCosetTransversal Gamma S)
    (hmeas : MeasurableSet S)
    (hμ_univ : μ Set.univ = ENNReal.ofReal 1) :
    μ S = ENNReal.ofReal (1 / (Nat.card Gamma : ℝ)) := by
  rw [hS.measure_eq_univ_mul_inv_natCard hmeas, hμ_univ]
  simp

end IsLeftCosetTransversal

/-- The real-valued minimum selector for the left action of a finite subgroup.

For a separating map `phi : G → ℝ`, this is the set of elements whose
`phi`-value is minimal among their finite left `Gamma`-orbit. -/
def finiteSubgroupMinimizerSlice {G : Type u} [Group G]
    (Gamma : Subgroup G) (phi : G → ℝ) : Set G :=
  {x : G | ∀ gamma : Gamma, phi x ≤ phi ((gamma : G) * x)}

/-- The finite-subgroup minimum selector is measurable when the ordering map
and the finite family of left translations are measurable. -/
theorem finiteSubgroupMinimizerSlice_measurableSet {G : Type u}
    [Group G] [MeasurableSpace G] (Gamma : Subgroup G) [Fintype Gamma]
    {phi : G → ℝ}
    (hphi : Measurable phi)
    (hleft_meas : ∀ gamma : Gamma,
      Measurable fun x : G => (gamma : G) * x) :
    MeasurableSet (finiteSubgroupMinimizerSlice Gamma phi) := by
  have hslice :
      finiteSubgroupMinimizerSlice Gamma phi =
        ⋂ gamma : Gamma, {x : G | phi x ≤ phi ((gamma : G) * x)} := by
    ext x
    simp [finiteSubgroupMinimizerSlice]
  rw [hslice]
  exact
    MeasurableSet.iInter fun gamma =>
      measurableSet_le hphi (hphi.comp (hleft_meas gamma))

/-- The real-valued finite-orbit minimum selector is a left-coset
transversal.

The only separation input is injectivity of `phi`: finite minima give a
representative in every orbit, and injectivity turns the two opposite
minimality inequalities into uniqueness. -/
theorem finiteSubgroupMinimizerSlice_isLeftCosetTransversal_of_injective
    {G : Type u} [Group G] (Gamma : Subgroup G) [Fintype Gamma]
    {phi : G → ℝ} (hphi_inj : Function.Injective phi) :
    IsLeftCosetTransversal Gamma (finiteSubgroupMinimizerSlice Gamma phi) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨gamma0, _hgamma0_mem, hgamma0_min⟩ :=
      Finset.exists_min_image (s := (Finset.univ : Finset Gamma))
        (f := fun gamma : Gamma => phi ((gamma : G) * x))
        ⟨1, Finset.mem_univ 1⟩
    refine ⟨gamma0⁻¹, (gamma0 : G) * x, ?_, ?_⟩
    · intro gamma
      have hmin :=
        hgamma0_min (gamma * gamma0) (Finset.mem_univ (gamma * gamma0))
      simpa [finiteSubgroupMinimizerSlice, mul_assoc] using hmin
    · simp
  · intro c₁ c₂ hc₁ hc₂ hmem
    let gamma : Gamma := ⟨c₂ * c₁⁻¹, hmem⟩
    have hgamma_c₁ : (gamma : G) * c₁ = c₂ := by
      change (c₂ * c₁⁻¹) * c₁ = c₂
      simp
    have hgamma_inv_c₂ : (gamma : G)⁻¹ * c₂ = c₁ := by
      calc
        (gamma : G)⁻¹ * c₂ =
            (gamma : G)⁻¹ * ((gamma : G) * c₁) := by
              rw [hgamma_c₁]
        _ = c₁ := by
              simp
    have hle₁₂ : phi c₁ ≤ phi c₂ := by
      have h := hc₁ gamma
      simpa [finiteSubgroupMinimizerSlice, hgamma_c₁] using h
    have hle₂₁ : phi c₂ ≤ phi c₁ := by
      have h := hc₂ gamma⁻¹
      simpa [finiteSubgroupMinimizerSlice, hgamma_inv_c₂] using h
    exact (hphi_inj (le_antisymm hle₁₂ hle₂₁)).symm

/-- Measurable-embedding form of the finite-orbit minimum selector. -/
theorem finiteSubgroupMinimizerSlice_isLeftCosetTransversal
    {G : Type u} [Group G] [MeasurableSpace G]
    (Gamma : Subgroup G) [Fintype Gamma]
    {phi : G → ℝ} (hphi : MeasurableEmbedding phi) :
    IsLeftCosetTransversal Gamma (finiteSubgroupMinimizerSlice Gamma phi) :=
  finiteSubgroupMinimizerSlice_isLeftCosetTransversal_of_injective
    Gamma hphi.injective

/-- The ordered-embedding selector package for a finite subgroup: a measurable
embedding into `ℝ` and measurable left translations produce a measurable
left-coset transversal. -/
theorem finiteSubgroupMinimizerSlice_measurableSet_and_isLeftCosetTransversal
    {G : Type u} [Group G] [MeasurableSpace G]
    (Gamma : Subgroup G) [Fintype Gamma]
    {phi : G → ℝ} (hphi : MeasurableEmbedding phi)
    (hleft_meas : ∀ gamma : Gamma,
      Measurable fun x : G => (gamma : G) * x) :
    MeasurableSet (finiteSubgroupMinimizerSlice Gamma phi) ∧
      IsLeftCosetTransversal Gamma (finiteSubgroupMinimizerSlice Gamma phi) :=
  ⟨finiteSubgroupMinimizerSlice_measurableSet Gamma
      hphi.measurable hleft_meas,
    finiteSubgroupMinimizerSlice_isLeftCosetTransversal Gamma hphi⟩

/-- The concrete standard-Borel finite-subgroup selector.

It chooses the element of each finite left orbit whose
`MeasureTheory.embeddingReal` value is minimal. -/
def finiteSubgroupEmbeddingRealSlice {G : Type u}
    [Group G] [MeasurableSpace G] [StandardBorelSpace G]
    (Gamma : Subgroup G) : Set G :=
  finiteSubgroupMinimizerSlice Gamma (MeasureTheory.embeddingReal G)

/-- The `embeddingReal` finite-subgroup selector is measurable when the finite
family of left translations is measurable. -/
theorem finiteSubgroupEmbeddingRealSlice_measurableSet {G : Type u}
    [Group G] [MeasurableSpace G] [StandardBorelSpace G]
    (Gamma : Subgroup G) [Fintype Gamma]
    (hleft_meas : ∀ gamma : Gamma,
      Measurable fun x : G => (gamma : G) * x) :
    MeasurableSet (finiteSubgroupEmbeddingRealSlice Gamma) := by
  simpa [finiteSubgroupEmbeddingRealSlice] using
    finiteSubgroupMinimizerSlice_measurableSet Gamma
      (MeasureTheory.measurable_embeddingReal G) hleft_meas

/-- The `embeddingReal` finite-subgroup selector is a left-coset transversal. -/
theorem finiteSubgroupEmbeddingRealSlice_isLeftCosetTransversal {G : Type u}
    [Group G] [MeasurableSpace G] [StandardBorelSpace G]
    (Gamma : Subgroup G) [Fintype Gamma] :
    IsLeftCosetTransversal Gamma (finiteSubgroupEmbeddingRealSlice Gamma) := by
  simpa [finiteSubgroupEmbeddingRealSlice] using
    finiteSubgroupMinimizerSlice_isLeftCosetTransversal Gamma
      (MeasureTheory.measurableEmbedding_embeddingReal G)

/-- The concrete `embeddingReal` selector package for a finite subgroup. -/
theorem finiteSubgroupEmbeddingRealSlice_measurableSet_and_isLeftCosetTransversal
    {G : Type u} [Group G] [MeasurableSpace G] [StandardBorelSpace G]
    (Gamma : Subgroup G) [Fintype Gamma]
    (hleft_meas : ∀ gamma : Gamma,
      Measurable fun x : G => (gamma : G) * x) :
    MeasurableSet (finiteSubgroupEmbeddingRealSlice Gamma) ∧
      IsLeftCosetTransversal Gamma (finiteSubgroupEmbeddingRealSlice Gamma) :=
  ⟨finiteSubgroupEmbeddingRealSlice_measurableSet Gamma hleft_meas,
    finiteSubgroupEmbeddingRealSlice_isLeftCosetTransversal Gamma⟩

/-- Normalized Haar measure of the concrete `embeddingReal` finite-subgroup
selector. -/
theorem finiteSubgroupEmbeddingRealSlice_measure_eq_inv_natCard {G : Type u}
    [Group G] [MeasurableSpace G] [StandardBorelSpace G] [MeasurableMul G]
    (Gamma : Subgroup G) [Fintype Gamma]
    {μ : Measure G} [Measure.IsMulLeftInvariant μ]
    (hμ_univ : μ Set.univ = ENNReal.ofReal 1) :
    μ (finiteSubgroupEmbeddingRealSlice Gamma) =
      ENNReal.ofReal (1 / (Nat.card Gamma : ℝ)) := by
  exact
    (finiteSubgroupEmbeddingRealSlice_isLeftCosetTransversal Gamma).measure_eq_inv_natCard
      (finiteSubgroupEmbeddingRealSlice_measurableSet Gamma
        (fun gamma => measurable_const_mul (gamma : G)))
      hμ_univ

/-- Standard-Borel existence of a measurable finite-subgroup left-coset
transversal.

This wraps the ordered-embedding selector core using mathlib's measurable
embedding of any standard Borel space into `ℝ`. -/
theorem exists_measurableSet_isLeftCosetTransversal_of_standardBorel
    {G : Type u} [Group G] [MeasurableSpace G] [StandardBorelSpace G]
    (Gamma : Subgroup G) [Fintype Gamma]
    (hleft_meas : ∀ gamma : Gamma,
      Measurable fun x : G => (gamma : G) * x) :
    ∃ S : Set G, MeasurableSet S ∧ IsLeftCosetTransversal Gamma S := by
  obtain ⟨phi, hphi⟩ := MeasureTheory.exists_measurableEmbedding_real G
  exact
    ⟨finiteSubgroupMinimizerSlice Gamma phi,
      finiteSubgroupMinimizerSlice_measurableSet Gamma
        hphi.measurable hleft_meas,
      finiteSubgroupMinimizerSlice_isLeftCosetTransversal Gamma hphi⟩

/-- Standard-Borel measurable-transversal Haar identity for a finite subgroup.

Under measurable multiplication and normalized left-invariant Haar measure,
the standard-Borel selector has the reciprocal subgroup cardinality measure. -/
theorem exists_measurableSet_isLeftCosetTransversal_measure_eq_inv_natCard_of_standardBorel
    {G : Type u} [Group G] [MeasurableSpace G] [StandardBorelSpace G]
    [MeasurableMul G]
    (Gamma : Subgroup G) [Fintype Gamma]
    {μ : Measure G} [Measure.IsMulLeftInvariant μ]
    (hμ_univ : μ Set.univ = ENNReal.ofReal 1) :
    ∃ S : Set G,
      MeasurableSet S ∧
      IsLeftCosetTransversal Gamma S ∧
      μ S = ENNReal.ofReal (1 / (Nat.card Gamma : ℝ)) := by
  obtain ⟨S, hS_meas, hS_trans⟩ :=
    exists_measurableSet_isLeftCosetTransversal_of_standardBorel
      Gamma (fun gamma => measurable_const_mul (gamma : G))
  exact
    ⟨S, hS_meas, hS_trans,
      hS_trans.measure_eq_inv_natCard hS_meas hμ_univ⟩

/-- The left translates of the chosen `Quot.out` representative slice cover
the ambient group. -/
theorem leftCosetRepresentativeSlice_iUnion_leftTranslate {G : Type u}
    [Group G] (Gamma : Subgroup G) :
    (⋃ gamma : Gamma,
      (fun c : G => (gamma : G) * c) '' leftCosetRepresentativeSlice Gamma) =
        Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    rcases leftCosetRepresentativeSlice_decomp Gamma x with
      ⟨gamma, c, hc, rfl⟩
    exact Set.mem_iUnion.mpr ⟨gamma, ⟨c, hc, rfl⟩⟩

/-- Distinct left translates of the chosen `Quot.out` representative slice
are disjoint. -/
theorem leftCosetRepresentativeSlice_pairwiseDisjoint_leftTranslate
    {G : Type u} [Group G] (Gamma : Subgroup G) :
    Pairwise fun gamma delta : Gamma =>
      Disjoint
        ((fun c : G => (gamma : G) * c) '' leftCosetRepresentativeSlice Gamma)
        ((fun c : G => (delta : G) * c) '' leftCosetRepresentativeSlice Gamma) := by
  intro gamma delta hne
  rw [Set.disjoint_left]
  intro x hxgamma hxdelta
  rcases hxgamma with ⟨c₁, hc₁, rfl⟩
  rcases hxdelta with ⟨c₂, hc₂, hx₂⟩
  have hc₂_eq : c₂ = ((delta : G)⁻¹ * (gamma : G)) * c₁ := by
    calc
      c₂ = 1 * c₂ := by simp
      _ = (delta : G)⁻¹ * ((delta : G) * c₂) := by
          simp
      _ = (delta : G)⁻¹ * ((gamma : G) * c₁) := by
          exact congrArg (fun y : G => (delta : G)⁻¹ * y) hx₂
      _ = ((delta : G)⁻¹ * (gamma : G)) * c₁ := by
          simp [mul_assoc]
  have hfactor_mem : ((delta : G)⁻¹ * (gamma : G)) ∈ Gamma := by
    simpa using ((delta⁻¹ * gamma : Gamma).property)
  have hmem : c₂ * c₁⁻¹ ∈ Gamma := by
    have hcalc :
        c₂ * c₁⁻¹ = (delta : G)⁻¹ * (gamma : G) := by
      calc
        c₂ * c₁⁻¹ = (((delta : G)⁻¹ * (gamma : G)) * c₁) * c₁⁻¹ := by
            rw [hc₂_eq]
        _ = (delta : G)⁻¹ * (gamma : G) := by
            simp [mul_assoc]
    rw [hcalc]
    exact hfactor_mem
  have hc₂c₁ : c₂ = c₁ :=
    leftCosetRepresentativeSlice_unique Gamma c₁ c₂ hc₁ hc₂ hmem
  have hgamma_delta_coe : (gamma : G) = (delta : G) := by
    have hmul : (delta : G) * c₁ = (gamma : G) * c₁ := by
      simpa [hc₂c₁] using hx₂
    exact (mul_right_cancel hmul).symm
  exact hne (Subtype.ext hgamma_delta_coe)

/-- Normalized measure of the chosen finite left-action orbit representative
slice.

If a finite subgroup acts by left multiplication preserving a normalized
measure, then the chosen `Quot.out` slice has measure the reciprocal of the
subgroup cardinality.  This is the abstract measure-theoretic input behind
the pointwise chosen local-stabilizer slice computation. -/
theorem leftCosetRepresentativeSlice_measure_eq_inv_natCard
    {G : Type u} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Gamma : Subgroup G) [Fintype Gamma]
    {μ : Measure G} [Measure.IsMulLeftInvariant μ]
    (hmeas : MeasurableSet (leftCosetRepresentativeSlice Gamma))
    (hμ_univ : μ Set.univ = ENNReal.ofReal 1) :
    μ (leftCosetRepresentativeSlice Gamma) =
      ENNReal.ofReal (1 / (Nat.card Gamma : ℝ)) := by
  let S : Set G := leftCosetRepresentativeSlice Gamma
  have hcard_pos : 0 < Nat.card Gamma := by
    haveI : Nonempty Gamma := ⟨1⟩
    exact Nat.card_pos
  have htranslate_meas :
      ∀ gamma : Gamma, MeasurableSet ((fun c : G => (gamma : G) * c) '' S) := by
    intro gamma
    exact (measurableEmbedding_mulLeft (gamma : G)).measurableSet_image.2 hmeas
  have htranslate_measure :
      ∀ gamma : Gamma, μ ((fun c : G => (gamma : G) * c) '' S) = μ S := by
    intro gamma
    let L : G → G := fun c => (gamma : G) * c
    have hpre : L ⁻¹' (L '' S) = S := by
      ext c
      constructor
      · intro hc
        rcases hc with ⟨s, hs, hcs⟩
        have hcs' : c = s := by
          exact (mul_left_cancel hcs).symm
        simpa [hcs'] using hs
      · intro hc
        exact ⟨c, hc, rfl⟩
    calc
      μ (L '' S) = (Measure.map L μ) (L '' S) := by
          rw [map_mul_left_eq_self μ (gamma : G)]
      _ = μ (L ⁻¹' (L '' S)) := by
          rw [Measure.map_apply (measurable_const_mul (gamma : G))
            (htranslate_meas gamma)]
      _ = μ S := by
          rw [hpre]
  have hsum_univ :
      μ Set.univ =
        ∑ gamma : Gamma, μ ((fun c : G => (gamma : G) * c) '' S) := by
    calc
      μ Set.univ =
          μ (⋃ gamma : Gamma, (fun c : G => (gamma : G) * c) '' S) := by
            rw [leftCosetRepresentativeSlice_iUnion_leftTranslate Gamma]
      _ = ∑' gamma : Gamma, μ ((fun c : G => (gamma : G) * c) '' S) := by
            exact measure_iUnion
              (fun gamma delta hne =>
                leftCosetRepresentativeSlice_pairwiseDisjoint_leftTranslate
                  Gamma hne)
              htranslate_meas
      _ = ∑ gamma : Gamma, μ ((fun c : G => (gamma : G) * c) '' S) := by
            rw [tsum_fintype]
  have hsum_const :
      (∑ gamma : Gamma, μ S) = (Nat.card Gamma : ℝ≥0∞) * μ S := by
    rw [Finset.sum_const, Nat.card_eq_fintype_card]
    simp [nsmul_eq_mul]
  have hprod :
      (Nat.card Gamma : ℝ≥0∞) * μ S = ENNReal.ofReal 1 := by
    calc
      (Nat.card Gamma : ℝ≥0∞) * μ S =
          ∑ gamma : Gamma, μ S := hsum_const.symm
      _ = ∑ gamma : Gamma, μ ((fun c : G => (gamma : G) * c) '' S) := by
          exact Finset.sum_congr rfl fun gamma _ => (htranslate_measure gamma).symm
      _ = μ Set.univ := hsum_univ.symm
      _ = ENNReal.ofReal 1 := hμ_univ
  let c : ℝ≥0∞ := (Nat.card Gamma : ℝ≥0∞)
  have hc0 : c ≠ 0 := by
    change (Nat.card Gamma : ℝ≥0∞) ≠ 0
    exact_mod_cast Nat.ne_of_gt hcard_pos
  have hctop : c ≠ ∞ := by
    simp [c]
  have hcR : 0 < (Nat.card Gamma : ℝ) := by
    exact_mod_cast hcard_pos
  calc
    μ S = 1 * μ S := by simp
    _ = (c⁻¹ * c) * μ S := by
        rw [mul_comm c⁻¹ c, ENNReal.mul_inv_cancel hc0 hctop]
    _ = c⁻¹ * (c * μ S) := by
        rw [mul_assoc]
    _ = c⁻¹ * ENNReal.ofReal 1 := by
        rw [hprod]
    _ = ENNReal.ofReal 1 / c := by
        rw [div_eq_mul_inv, mul_comm]
    _ = ENNReal.ofReal 1 / ENNReal.ofReal (Nat.card Gamma : ℝ) := by
        rw [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (1 / (Nat.card Gamma : ℝ)) := by
        exact (ENNReal.ofReal_div_of_pos (x := 1) hcR).symm

/-- The left quotient map is measurable for the quotient measurable space
defined as the map of the ambient measurable space. -/
theorem leftCosetMap_measurable_map {G : Type u} [Group G]
    (Gamma : Subgroup G) [mG : MeasurableSpace G] :
    @Measurable G (leftCosetSet Gamma) mG
      (MeasurableSpace.map (leftCosetMap Gamma) mG)
      (leftCosetMap Gamma) := by
  exact measurable_iff_comap_le.2
    (MeasurableSpace.comap_le_iff_le_map.2 le_rfl)

end PositiveDefiniteIntegralLattice

end
