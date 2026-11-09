import SMSFormula.AdelicPeriodization

/-!
# Adelic left Weil quotient measures

This module contains the project-local left Weil quotient-measure interface,
its fundamental-domain quotient measure presentation, compact-slice integral
identities, and the discrete cardinality normalization for left quotients.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

universe u
universe v
universe w

variable {n : ℕ}

open MeasureTheory
open scoped ENNReal

/-! ## Left Weil quotient measures -/

/-- Ambient Weil quotient-measure interface for the project-local non-normal
left quotient.

Concrete locally compact presentations should prove this from the usual Weil
formula.  The compact-slice finite-adelic step can then use the theorem below
with `f = 1_S`; the quotient-lift well-definedness is already handled by
`leftPeriodize`. -/
structure IsLeftWeilQuotientMeasure {G : Type u} [Group G] [MeasurableSpace G]
    (Gamma : Subgroup G) [MeasurableSpace (leftCosetSet Gamma)]
    (μG : Measure G) (μX : Measure (leftCosetSet Gamma)) : Prop where
  lintegral_leftPeriodize_eq :
    ∀ f : G → ℝ≥0∞,
      ∫⁻ X, leftPeriodize Gamma f X ∂μX = ∫⁻ y, f y ∂μG

/-- Setwise formula for the pushforward of a measure restricted to a
fundamental-domain candidate. -/
theorem map_restrict_apply_eq_inter_preimage
    {G : Type u} {X : Type v} [MeasurableSpace G] [MeasurableSpace X]
    {μG : Measure G} {F : Set G} {q : G → X}
    (hq : Measurable q)
    {A : Set X} (hA : MeasurableSet A) :
    (Measure.map q (μG.restrict F)) A = μG (F ∩ q ⁻¹' A) := by
  calc
    (Measure.map q (μG.restrict F)) A =
        (μG.restrict F) (q ⁻¹' A) := by
          exact Measure.map_apply hq hA
    _ = μG ((q ⁻¹' A) ∩ F) := by
          rw [Measure.restrict_apply (hq hA)]
    _ = μG (F ∩ q ⁻¹' A) := by
          rw [Set.inter_comm]

/-- The ambient left-quotient measure attached to a fundamental-domain
candidate.

For the finite-adelic quotient-volume package this is the concrete measure
`μX = map (G → Γ \ G) (μG.restrict F)` that the selected fibers inherit by
subtype/comap. -/
noncomputable def leftQuotientFundamentalDomainMeasure
    {G : Type u} [Group G] [MeasurableSpace G] (Gamma : Subgroup G)
    {mX : MeasurableSpace (leftCosetSet Gamma)}
    (μG : Measure G) (F : Set G) : @Measure (leftCosetSet Gamma) mX :=
  @Measure.map G (leftCosetSet Gamma)
    (inferInstance : MeasurableSpace G) mX
    (leftCosetMap Gamma) (μG.restrict F)

/-- The named fundamental-domain quotient measure is the pushforward
`map (G → Γ \ G) (μG.restrict F)`.

This exposes the concrete quotient-measure presentation field used by the
finite-adelic package instead of requiring downstream proofs to unfold the
definition directly. -/
theorem leftQuotientFundamentalDomainMeasure_eq_map_restrict
    {G : Type u} [Group G] [MeasurableSpace G] (Gamma : Subgroup G)
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (μG : Measure G) (F : Set G) :
    leftQuotientFundamentalDomainMeasure Gamma (mX := mX) μG F =
      Measure.map (leftCosetMap Gamma) (μG.restrict F) :=
  rfl

/-- The total mass of the quotient measure obtained from a fundamental-domain
pushforward is the ambient measure of the fundamental domain. -/
theorem leftQuotientMapRestrictFundamentalDomain_univ
    {G : Type u} [Group G] [MeasurableSpace G] {Gamma : Subgroup G}
    [MeasurableSpace (leftCosetSet Gamma)] {μG : Measure G} {F : Set G}
    (hmap : AEMeasurable (leftCosetMap Gamma) (μG.restrict F)) :
    (Measure.map (leftCosetMap Gamma) (μG.restrict F)) Set.univ = μG F := by
  rw [Measure.map_apply_of_aemeasurable hmap MeasurableSet.univ]
  simp

/-- Setwise formula for the fundamental-domain pushforward quotient measure
when the left quotient carries the standard map measurable structure. -/
theorem leftQuotientMapRestrictFundamentalDomain_apply_map_mspace
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G}
    {A : Set (leftCosetSet Gamma)} (hA : MeasurableSet A) :
    (Measure.map (leftCosetMap Gamma) (μG.restrict F)) A =
      μG (F ∩ (leftCosetMap Gamma) ⁻¹' A) := by
  have hmap :
      @Measurable G (leftCosetSet Gamma) mG mX (leftCosetMap Gamma) := by
    rw [hmX]
    exact leftCosetMap_measurable_map Gamma
  exact map_restrict_apply_eq_inter_preimage hmap hA

/-- Real-valued total-mass normalization for the fundamental-domain
pushforward quotient measure. -/
theorem leftQuotientMapRestrictFundamentalDomain_univ_toReal
    {G : Type u} [Group G] [MeasurableSpace G] {Gamma : Subgroup G}
    [MeasurableSpace (leftCosetSet Gamma)] {μG : Measure G} {F : Set G}
    (hmap : AEMeasurable (leftCosetMap Gamma) (μG.restrict F)) :
    ((Measure.map (leftCosetMap Gamma) (μG.restrict F)) Set.univ).toReal =
      (μG F).toReal := by
  rw [leftQuotientMapRestrictFundamentalDomain_univ (Gamma := Gamma) hmap]

/-- Total-mass normalization for the standard map measurable structure on the
left quotient.  In this setup measurability of the quotient map is formal, so
the only remaining mathematical input is the ambient volume of the chosen
fundamental domain. -/
theorem leftQuotientMapRestrictFundamentalDomain_univ_toReal_map_mspace
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} :
    ((Measure.map (leftCosetMap Gamma) (μG.restrict F)) Set.univ).toReal =
      (μG F).toReal := by
  have hmap :
      @Measurable G (leftCosetSet Gamma) mG mX (leftCosetMap Gamma) := by
    rw [hmX]
    exact leftCosetMap_measurable_map Gamma
  exact leftQuotientMapRestrictFundamentalDomain_univ_toReal
    (Gamma := Gamma) (μG := μG) (F := F) hmap.aemeasurable

/-- Total-mass normalization for the named fundamental-domain quotient
measure at the `ℝ≥0∞` level.

The standard map measurable structure makes the quotient map measurable, so
the pushforward of `μG.restrict F` gives total mass exactly `μG F`, not only
after coercion to real numbers. -/
theorem leftQuotientFundamentalDomainMeasure_univ_map_mspace
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} :
    (leftQuotientFundamentalDomainMeasure Gamma (mX := mX) μG F) Set.univ =
      μG F := by
  have hmap :
      @Measurable G (leftCosetSet Gamma) mG mX (leftCosetMap Gamma) := by
    rw [hmX]
    exact leftCosetMap_measurable_map Gamma
  simpa [leftQuotientFundamentalDomainMeasure_eq_map_restrict] using
    leftQuotientMapRestrictFundamentalDomain_univ
      (Gamma := Gamma) (μG := μG) (F := F) hmap.aemeasurable

/-- Setwise formula for the named fundamental-domain quotient measure.

For any measurable subset of the left quotient, the named measure
`leftQuotientFundamentalDomainMeasure Γ μG F` evaluates as the ambient
measure of the fundamental-domain slice over that subset. -/
theorem leftQuotientFundamentalDomainMeasure_apply_map_mspace
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G}
    {A : Set (leftCosetSet Gamma)} (hA : MeasurableSet A) :
    (leftQuotientFundamentalDomainMeasure Gamma (mX := mX) μG F) A =
      μG (F ∩ (leftCosetMap Gamma) ⁻¹' A) := by
  simpa [leftQuotientFundamentalDomainMeasure_eq_map_restrict] using
    leftQuotientMapRestrictFundamentalDomain_apply_map_mspace
      (Gamma := Gamma) (mG := mG) (mX := mX) (μG := μG) (F := F)
      (hmX := hmX) hA

/-- Total-mass normalization for the named fundamental-domain quotient
measure. -/
theorem leftQuotientFundamentalDomainMeasure_univ_toReal_map_mspace
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} :
    ((leftQuotientFundamentalDomainMeasure Gamma (mX := mX) μG F)
        Set.univ).toReal =
      (μG F).toReal := by
  simpa [leftQuotientFundamentalDomainMeasure_eq_map_restrict] using
    leftQuotientMapRestrictFundamentalDomain_univ_toReal_map_mspace
      (Gamma := Gamma) (μG := μG) (F := F) hmX

/-- For the named fundamental-domain quotient measure, the real total-mass
normalization is equivalent to the ambient fundamental-domain volume
normalization.

This lets a concrete quotient-measure construction prove the total finite
adelic volume on `μX = map (G → Γ \ G) (μG.restrict F)` and then transfer it
to the package field `(μG F).toReal = volume`. -/
theorem leftQuotientFundamentalDomainMeasure_univ_toReal_eq_iff
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} {V : ℝ} :
    ((leftQuotientFundamentalDomainMeasure Gamma (mX := mX) μG F)
        Set.univ).toReal = V ↔
      (μG F).toReal = V := by
  rw [leftQuotientFundamentalDomainMeasure_univ_toReal_map_mspace
    (Gamma := Gamma) (μG := μG) (F := F) hmX]

/-- Build the ambient Weil quotient-measure interface from a strict
fundamental-domain measure construction.

If the quotient measure is the pushforward of `μG.restrict F` along the
left-quotient map, then it is enough for a source theorem to prove the
periodization integral over the chosen fundamental domain `F`.  This is the
formal bridge suggested by the strict measurable fundamental-domain
construction: no finite-adelic presentation has to state the quotient
lintegral identity directly once it has chosen the quotient measure in this
way. -/
theorem IsLeftWeilQuotientMeasure.of_map_restrict_fundamentalDomain
    {G : Type u} [Group G] [MeasurableSpace G] {Gamma : Subgroup G}
    [MeasurableSpace (leftCosetSet Gamma)] {μG : Measure G} {F : Set G}
    (hmap : AEMeasurable (leftCosetMap Gamma) (μG.restrict F))
    (hperiodize :
      ∀ f : G → ℝ≥0∞,
        AEMeasurable (leftPeriodize Gamma f)
          (Measure.map (leftCosetMap Gamma) (μG.restrict F)))
    (hfund :
      ∀ f : G → ℝ≥0∞,
        ∫⁻ y, leftPeriodize Gamma f (leftCosetMap Gamma y) ∂μG.restrict F =
          ∫⁻ y, f y ∂μG) :
    IsLeftWeilQuotientMeasure Gamma μG
      (Measure.map (leftCosetMap Gamma) (μG.restrict F)) := by
  refine ⟨?_⟩
  intro f
  calc
    ∫⁻ X, leftPeriodize Gamma f X
        ∂Measure.map (leftCosetMap Gamma) (μG.restrict F) =
        ∫⁻ y, leftPeriodize Gamma f (leftCosetMap Gamma y)
          ∂μG.restrict F := by
          exact lintegral_map' (hperiodize f) hmap
    _ = ∫⁻ y, f y ∂μG := hfund f

/-- Build the ambient Weil quotient-measure interface from a strict
fundamental-domain construction when the left quotient carries the standard
map measurable space.

Compared with `of_map_restrict_fundamentalDomain`, this version does not need
a separate a.e. measurability proof for the quotient map: it follows from the measurable-space construction on `Gamma \ G`. -/
theorem IsLeftWeilQuotientMeasure.of_map_restrict_fundamentalDomain_map_mspace
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G}
    (hperiodize :
      ∀ f : G → ℝ≥0∞,
        AEMeasurable (leftPeriodize Gamma f)
          (Measure.map (leftCosetMap Gamma) (μG.restrict F)))
    (hfund :
      ∀ f : G → ℝ≥0∞,
        ∫⁻ y, leftPeriodize Gamma f (leftCosetMap Gamma y) ∂μG.restrict F =
          ∫⁻ y, f y ∂μG) :
    IsLeftWeilQuotientMeasure Gamma μG
      (Measure.map (leftCosetMap Gamma) (μG.restrict F)) := by
  have hmap_meas :
      @Measurable G (leftCosetSet Gamma) mG mX (leftCosetMap Gamma) := by
    rw [hmX]
    exact leftCosetMap_measurable_map Gamma
  exact
    IsLeftWeilQuotientMeasure.of_map_restrict_fundamentalDomain
      (Gamma := Gamma) (μG := μG) (F := F)
      hmap_meas.aemeasurable hperiodize hfund

/-- Build the strict fundamental-domain quotient-measure interface from
ambient measurability of the preperiodized functions.

For the finite-adelic compact-slice application, this is the source-facing
form of the previous constructor: once the quotient carries the standard map
measurable space, the source theorem only has to prove the periodization
integral over `F` and ambient measurability of the finite/local-finite
periodized sums before descent. -/
theorem IsLeftWeilQuotientMeasure.of_map_restrict_fundamentalDomain_map_mspace_preperiodize
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G}
    (hpreperiodize :
      ∀ f : G → ℝ≥0∞, Measurable (leftPreperiodize Gamma f))
    (hfund :
      ∀ f : G → ℝ≥0∞,
        ∫⁻ y, leftPeriodize Gamma f (leftCosetMap Gamma y) ∂μG.restrict F =
          ∫⁻ y, f y ∂μG) :
    IsLeftWeilQuotientMeasure Gamma μG
      (Measure.map (leftCosetMap Gamma) (μG.restrict F)) := by
  apply
    IsLeftWeilQuotientMeasure.of_map_restrict_fundamentalDomain_map_mspace
      (Gamma := Gamma) (μG := μG) (F := F) hmX
  · intro f
    rw [hmX]
    exact leftPeriodize_aemeasurable_map_of_leftPreperiodize Gamma (hpreperiodize f)
  · exact hfund

theorem IsLeftWeilQuotientMeasure.lintegral_leftSetPeriodize_eq
    {G : Type u} [Group G] [MeasurableSpace G] {Gamma : Subgroup G}
    [MeasurableSpace (leftCosetSet Gamma)] {μG : Measure G}
    {μX : Measure (leftCosetSet Gamma)}
    (hWeil : IsLeftWeilQuotientMeasure Gamma μG μX)
    {S : Set G} (hS : MeasurableSet S) :
    ∫⁻ X, leftSetPeriodize Gamma S X ∂μX = μG S := by
  rw [leftSetPeriodize, hWeil.lintegral_leftPeriodize_eq]
  rw [lintegral_indicator_const hS]
  simp

theorem IsLeftWeilQuotientMeasure.lintegral_indicator_leftSetPeriodize_eq
    {G : Type u} [Group G] [MeasurableSpace G] {Gamma : Subgroup G}
    [MeasurableSpace (leftCosetSet Gamma)] {μG : Measure G}
    {μX : Measure (leftCosetSet Gamma)}
    (hWeil : IsLeftWeilQuotientMeasure Gamma μG μX)
    {S : Set G} (hSmeas : MeasurableSet S)
    {Y : Set (leftCosetSet Gamma)}
    (hS_sub : ∀ ⦃y : G⦄, y ∈ S → leftCosetMap Gamma y ∈ Y) :
    ∫⁻ X, Y.indicator (leftSetPeriodize Gamma S) X ∂μX = μG S := by
  have hsupport :
      leftSetPeriodize Gamma S =ᵐ[μX]
        Y.indicator (leftSetPeriodize Gamma S) := by
    exact Filter.Eventually.of_forall (by
      intro X
      by_cases hX : X ∈ Y
      · simp [Set.indicator_of_mem hX]
      · rw [Set.indicator_of_notMem hX]
        exact leftSetPeriodize_eq_zero_of_not_mem Gamma hS_sub hX)
  calc
    ∫⁻ X, Y.indicator (leftSetPeriodize Gamma S) X ∂μX =
        ∫⁻ X, leftSetPeriodize Gamma S X ∂μX := by
          exact (lintegral_congr_ae hsupport).symm
    _ = μG S := hWeil.lintegral_leftSetPeriodize_eq hSmeas

/-- The project-local left quotient agrees with Mathlib's right-coset
quotient.  The local relation uses representatives `y = gamma * x`, which is
Mathlib's `rightRel` convention. -/
noncomputable def leftCosetSetEquivQuotientRightRel {G : Type u} [Group G]
    (Gamma : Subgroup G) :
    leftCosetSet Gamma ≃ Quotient (QuotientGroup.rightRel Gamma) where
  toFun :=
    Quot.map id (by
      intro x y hxy
      rw [QuotientGroup.rightRel_apply]
      rcases hxy with ⟨gamma, rfl⟩
      simp)
  invFun :=
    Quot.map id (by
      intro x y hxy
      apply (QuotientGroup.rightRel_apply).mp at hxy
      refine ⟨⟨y * x⁻¹, hxy⟩, ?_⟩
      simp)
  left_inv X := by
    induction X using Quot.inductionOn with
    | h x => rfl
  right_inv X := by
    induction X using Quot.inductionOn with
    | h x => rfl

/-- Finite/counting-measure form of the quotient pushforward normalization:
the cardinality of a group is the product of the stabilizer cardinality and
the cardinality of its project-local left quotient.

This is the discrete analogue of the Haar-measure identity behind the
one-piece quotient-volume source. -/
theorem subgroup_nat_card_mul_leftCosetSet_nat_card_eq {G : Type u} [Group G]
    (Gamma : Subgroup G) :
    Nat.card Gamma * Nat.card (leftCosetSet Gamma) = Nat.card G := by
  rw [Nat.mul_comm]
  rw [Nat.card_congr (leftCosetSetEquivQuotientRightRel Gamma)]
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Gamma)]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup Gamma).symm


end PositiveDefiniteIntegralLattice

end
