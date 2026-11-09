import SMSFormula.AdelicLeftCosets

/-!
# Adelic left-coset periodization

This module contains the preperiodization and periodization functions on
project-local left quotients, together with their measurability and
fundamental-domain integral identities.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

universe u
universe v
universe w

variable {n : ℕ}

open MeasureTheory
open scoped ENNReal

/-! ## Left-coset periodization -/

/-- The ambient left-periodized nonnegative function
`y ↦ ∑' gamma : Gamma, f (gamma * y)`.

This is the group-theoretic part of the compact-slice Weil input: before any
measure or local-finiteness hypotheses are imposed, the sum is invariant under
changing `y` by a left `Gamma`-factor. -/
noncomputable def leftPreperiodize {G : Type u} [Group G]
    (Gamma : Subgroup G) (f : G → ℝ≥0∞) (y : G) : ℝ≥0∞ :=
  ∑' gamma : Gamma, f ((gamma : G) * y)

theorem leftPreperiodize_gamma_mul {G : Type u} [Group G]
    (Gamma : Subgroup G) (f : G → ℝ≥0∞) (delta : Gamma) (y : G) :
    leftPreperiodize Gamma f ((delta : G) * y) = leftPreperiodize Gamma f y := by
  unfold leftPreperiodize
  calc
    (∑' gamma : Gamma, f ((gamma : G) * ((delta : G) * y))) =
        ∑' gamma : Gamma, f (((gamma * delta : Gamma) : G) * y) := by
          apply tsum_congr
          intro gamma
          simp [mul_assoc]
    _ = ∑' gamma : Gamma, f ((gamma : G) * y) := by
          exact (Equiv.mulRight delta).tsum_eq (fun gamma : Gamma =>
            f ((gamma : G) * y))

theorem leftPreperiodize_eq_of_leftCosetRelated {G : Type u} [Group G]
    (Gamma : Subgroup G) (f : G → ℝ≥0∞) {x y : G}
    (hxy : IsLeftCosetRelated Gamma x y) :
    leftPreperiodize Gamma f x = leftPreperiodize Gamma f y := by
  rcases hxy with ⟨delta, rfl⟩
  exact (leftPreperiodize_gamma_mul Gamma f delta x).symm

/-- Countable ambient preperiodizations of measurable nonnegative functions
are measurable.

For the compact-slice quotient-volume target this discharges the routine
measurability part of the periodized indicator sums once the rational group is
countable and left multiplication on the finite-adelic carrier is measurable.
The remaining source input is then the strict fundamental-domain integral
identity, not measurability of the countable ENNReal sum. -/
theorem leftPreperiodize_measurable_of_countable {G : Type u} [Group G]
    [MeasurableSpace G] [MeasurableMul G] (Gamma : Subgroup G) [Countable Gamma]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (leftPreperiodize Gamma f) := by
  unfold leftPreperiodize
  exact Measurable.ennreal_tsum fun gamma =>
    hf.comp (measurable_const_mul (gamma : G))

/-- Indicator specialization of
`leftPreperiodize_measurable_of_countable`. -/
theorem leftPreperiodize_indicator_one_measurable_of_countable {G : Type u}
    [Group G] [MeasurableSpace G] [MeasurableMul G] (Gamma : Subgroup G)
    [Countable Gamma] {S : Set G} (hS : MeasurableSet S) :
    Measurable (leftPreperiodize Gamma (S.indicator (fun _ => (1 : ℝ≥0∞)))) := by
  exact leftPreperiodize_measurable_of_countable Gamma
    ((measurable_const : Measurable fun _ : G => (1 : ℝ≥0∞)).indicator hS)

/-- The periodization descended to the non-normal left quotient
`Gamma \ G`.

The descent uses only reindexing of the `Gamma`-sum by right multiplication in
`Gamma`; normality of `Gamma` is not needed. -/
noncomputable def leftPeriodize {G : Type u} [Group G]
    (Gamma : Subgroup G) (f : G → ℝ≥0∞) :
    leftCosetSet Gamma → ℝ≥0∞ :=
  Quot.lift (leftPreperiodize Gamma f)
    (fun _ _ hxy => leftPreperiodize_eq_of_leftCosetRelated Gamma f hxy)

theorem leftPeriodize_leftCosetMap {G : Type u} [Group G]
    (Gamma : Subgroup G) (f : G → ℝ≥0∞) (y : G) :
    leftPeriodize Gamma f (leftCosetMap Gamma y) = leftPreperiodize Gamma f y :=
  rfl

/-- A descended periodization is measurable for the standard quotient
measurable space once its preperiodized representative on the ambient group is
measurable. -/
theorem leftPeriodize_measurable_map_of_leftPreperiodize {G : Type u} [Group G]
    [mG : MeasurableSpace G] (Gamma : Subgroup G) {f : G → ℝ≥0∞}
    (hf : Measurable (leftPreperiodize Gamma f)) :
    @Measurable (leftCosetSet Gamma) ℝ≥0∞
      (MeasurableSpace.map (leftCosetMap Gamma) mG) inferInstance
      (leftPeriodize Gamma f) := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  intro s hs
  rcases hs with ⟨s', hs', rfl⟩
  rcases hs' with ⟨t, ht, rfl⟩
  simpa [Set.preimage_preimage, leftPeriodize_leftCosetMap] using
    (measurable_iff_comap_le.mp hf) ((leftPreperiodize Gamma f) ⁻¹' t)
      ⟨t, ht, rfl⟩

/-- A.e. measurability form of
`leftPeriodize_measurable_map_of_leftPreperiodize`. -/
theorem leftPeriodize_aemeasurable_map_of_leftPreperiodize {G : Type u} [Group G]
    [mG : MeasurableSpace G] (Gamma : Subgroup G) {f : G → ℝ≥0∞} {μG : Measure G}
    (hf : Measurable (leftPreperiodize Gamma f)) :
    @AEMeasurable (leftCosetSet Gamma) ℝ≥0∞
      inferInstance (MeasurableSpace.map (leftCosetMap Gamma) mG)
      (leftPeriodize Gamma f)
      (@Measure.map G (leftCosetSet Gamma) mG
        (MeasurableSpace.map (leftCosetMap Gamma) mG)
        (leftCosetMap Gamma) μG) :=
  (leftPeriodize_measurable_map_of_leftPreperiodize Gamma hf).aemeasurable

theorem leftCosetMap_gamma_mul {G : Type u} [Group G]
    (Gamma : Subgroup G) (delta : Gamma) (y : G) :
    leftCosetMap Gamma ((delta : G) * y) = leftCosetMap Gamma y := by
  exact (Quot.sound ⟨delta, rfl⟩).symm

/-- Set-indicator periodization on the ambient non-normal left quotient. -/
noncomputable def leftSetPeriodize {G : Type u} [Group G]
    (Gamma : Subgroup G) (S : Set G) : leftCosetSet Gamma → ℝ≥0∞ :=
  leftPeriodize Gamma (S.indicator (fun _ => (1 : ℝ≥0∞)))

theorem leftSetPeriodize_leftCosetMap {G : Type u} [Group G]
    (Gamma : Subgroup G) (S : Set G) (y : G) :
    leftSetPeriodize Gamma S (leftCosetMap Gamma y) =
      ∑' gamma : Gamma, S.indicator (fun _ => (1 : ℝ≥0∞)) ((gamma : G) * y) :=
  rfl

theorem leftSetPeriodize_leftCosetMap_eq_nat_card_of_finite
    {G : Type u} [Group G] (Gamma : Subgroup G) (S : Set G) (y : G)
    [Finite { gamma : Gamma // (gamma : G) * y ∈ S }] :
    leftSetPeriodize Gamma S (leftCosetMap Gamma y) =
      (Nat.card { gamma : Gamma // (gamma : G) * y ∈ S } : ℝ≥0∞) := by
  rw [leftSetPeriodize_leftCosetMap]
  let T : Set Gamma := { gamma | (gamma : G) * y ∈ S }
  calc
    (∑' gamma : Gamma, S.indicator (fun _ => (1 : ℝ≥0∞)) ((gamma : G) * y)) =
        ∑' gamma : Gamma, T.indicator (fun _ => (1 : ℝ≥0∞)) gamma := by
          apply tsum_congr
          intro gamma
          by_cases hgamma : (gamma : G) * y ∈ S
          · simp [T, hgamma]
          · simp [T, hgamma]
    _ = ∑' gamma : T, (1 : ℝ≥0∞) := by
          exact (tsum_subtype T (fun _ => (1 : ℝ≥0∞))).symm
    _ = (Nat.card T : ℝ≥0∞) := by
          classical
          let e : T ≃ { gamma : Gamma // (gamma : G) * y ∈ S } :=
            { toFun := fun gamma => ⟨gamma.1, by
                exact gamma.2⟩
              invFun := fun gamma => ⟨gamma.1, by
                change (gamma.1 : G) * y ∈ S
                exact gamma.2⟩
              left_inv := by
                intro gamma
                rfl
              right_inv := by
                intro gamma
                rfl }
          haveI : Finite T :=
            Finite.of_equiv { gamma : Gamma // (gamma : G) * y ∈ S } e.symm
          letI : Fintype T := Fintype.ofFinite T
          rw [tsum_fintype]
          simp [Nat.card_eq_fintype_card]

/-- Integrated finite-cardinality form of set periodization over a strict
domain.

Only finiteness on the restricted strict domain is needed to rewrite the
periodized integrand to the finite cardinality integrand. -/
theorem lintegral_restrict_leftSetPeriodize_eq_lintegral_nat_card_of_ae_finite
    {G : Type u} [Group G] [MeasurableSpace G] (Gamma : Subgroup G)
    {μG : Measure G} {F S : Set G}
    (hfinite :
      ∀ᵐ y ∂μG.restrict F,
        Finite { gamma : Gamma // (gamma : G) * y ∈ S }) :
    ∫⁻ y, leftSetPeriodize Gamma S (leftCosetMap Gamma y) ∂μG.restrict F =
      ∫⁻ y,
        (Nat.card { gamma : Gamma // (gamma : G) * y ∈ S } : ℝ≥0∞)
          ∂μG.restrict F := by
  apply lintegral_congr_ae
  filter_upwards [hfinite] with y hy
  haveI : Finite { gamma : Gamma // (gamma : G) * y ∈ S } := hy
  exact leftSetPeriodize_leftCosetMap_eq_nat_card_of_finite Gamma S y

/-- Fundamental-domain unfolding for measurable nonnegative periodizations.

This is the Mathlib `IsFundamentalDomain` form of the ambient Weil
periodization theorem for a measurable integrand.  It is the all-measurable
function version behind the indicator specialization below. -/
theorem lintegral_restrict_leftPeriodize_eq_lintegral_of_isFundamentalDomain
    {G : Type u} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Gamma : Subgroup G)
    [Countable Gamma] [MeasurableConstSMul Gamma G]
    {μG : Measure G} [SMulInvariantMeasure Gamma G μG] {F : Set G}
    {f : G → ℝ≥0∞} (hf : Measurable f)
    (hF : IsFundamentalDomain Gamma F μG) :
    ∫⁻ y, leftPeriodize Gamma f (leftCosetMap Gamma y) ∂μG.restrict F =
      ∫⁻ y, f y ∂μG := by
  have hterm :
      ∀ gamma : Gamma,
        AEMeasurable (fun y : G => f ((gamma : G) * y)) (μG.restrict F) := by
    intro gamma
    exact (hf.comp (measurable_const_mul (gamma : G))).aemeasurable
  calc
    ∫⁻ y, leftPeriodize Gamma f (leftCosetMap Gamma y) ∂μG.restrict F =
        ∫⁻ y, ∑' gamma : Gamma, f ((gamma : G) * y) ∂μG.restrict F := by
          rfl
    _ =
        ∑' gamma : Gamma,
          ∫⁻ y, f ((gamma : G) * y) ∂μG.restrict F := by
          rw [lintegral_tsum hterm]
    _ = ∫⁻ y, f y ∂μG := by
          simpa using (hF.lintegral_eq_tsum'' f).symm

/-- Fundamental-domain unfolding for indicator periodizations.

This is the Mathlib `IsFundamentalDomain` form of the remaining
Schulze--Pillot strict-domain counting input: for a countable subgroup acting
on the ambient group by left multiplication, the integral over a fundamental
domain of the periodization of `1_S` is the ambient measure of `S`. -/
theorem lintegral_restrict_leftSetPeriodize_eq_measure_of_isFundamentalDomain
    {G : Type u} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Gamma : Subgroup G)
    [Countable Gamma] [MeasurableConstSMul Gamma G]
    {μG : Measure G} [SMulInvariantMeasure Gamma G μG] {F S : Set G}
    (hF : IsFundamentalDomain Gamma F μG) (hS : MeasurableSet S) :
    ∫⁻ y, leftSetPeriodize Gamma S (leftCosetMap Gamma y) ∂μG.restrict F =
      μG S := by
  calc
    ∫⁻ y, leftSetPeriodize Gamma S (leftCosetMap Gamma y) ∂μG.restrict F =
        ∫⁻ y, S.indicator (fun _ : G => (1 : ℝ≥0∞)) y ∂μG := by
          simpa [leftSetPeriodize] using
            (lintegral_restrict_leftPeriodize_eq_lintegral_of_isFundamentalDomain
              (Gamma := Gamma) (μG := μG) (F := F)
              ((measurable_const : Measurable fun _ : G => (1 : ℝ≥0∞)).indicator hS)
              hF)
    _ = μG S := by
          rw [lintegral_indicator_const hS]
          simp

/-- Support lemma for set periodizations.

If a set `S` maps into a quotient-side subset `Y`, then the periodization of
`1_S` vanishes outside `Y`.  This is the formal support step used when an
ambient compact-slice periodization is later restricted to the selected piece
`X_g`. -/
theorem leftSetPeriodize_eq_zero_of_not_mem {G : Type u} [Group G]
    (Gamma : Subgroup G) {S : Set G} {Y : Set (leftCosetSet Gamma)}
    (hS : ∀ ⦃y : G⦄, y ∈ S → leftCosetMap Gamma y ∈ Y)
    {X : leftCosetSet Gamma} (hX : X ∉ Y) :
    leftSetPeriodize Gamma S X = 0 := by
  induction X using Quot.inductionOn with
  | h y =>
      change leftCosetMap Gamma y ∉ Y at hX
      change leftSetPeriodize Gamma S (leftCosetMap Gamma y) = 0
      rw [leftSetPeriodize_leftCosetMap]
      rw [ENNReal.tsum_eq_zero]
      intro gamma
      by_cases hmem : (gamma : G) * y ∈ S
      · have hmap : leftCosetMap Gamma ((gamma : G) * y) ∈ Y := hS hmem
        have hmap' : leftCosetMap Gamma y ∈ Y := by
          simpa [leftCosetMap_gamma_mul Gamma gamma y] using hmap
        exact False.elim (hX hmap')
      · simp [hmem]

end PositiveDefiniteIntegralLattice

end
