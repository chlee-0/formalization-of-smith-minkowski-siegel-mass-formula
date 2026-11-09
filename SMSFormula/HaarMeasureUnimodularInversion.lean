import Mathlib.MeasureTheory.Group.ModularCharacter

/-!
# Unimodular Haar measures and inversion

Mathlib proves inversion invariance of regular Haar measures on commutative
groups.  The proof only uses commutativity to obtain right invariance.  This
module records the corresponding noncommutative statement with right
invariance as an explicit hypothesis, together with the exact bridge to the
modular character.

The implications are named theorems rather than reciprocal instances, so
typeclass search cannot loop between right invariance and inversion
invariance.
-/

noncomputable section

open scoped ENNReal
open TopologicalSpace

namespace MeasureTheory.Measure

/-- A nonzero sigma-finite right-invariant measure becomes a Haar measure
after inversion.  This is the right-Haar counterpart of Mathlib's
sigma-finite left-Haar uniqueness theorem. -/
theorem isHaarMeasure_inv_of_sigmaFinite_rightInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [SigmaFinite mu] [IsMulRightInvariant mu]
    (hmu : mu ≠ 0) : IsHaarMeasure mu.inv := by
  let K : PositiveCompacts G := Classical.arbitrary _
  have heq : mu.inv = mu.inv K • haarMeasure K :=
    haarMeasure_unique mu.inv K
  have hinv_ne : mu.inv ≠ 0 := by
    intro hinv
    apply hmu
    rw [← Measure.inv_inv mu, hinv]
    simp [Measure.inv_def]
  have hK_ne : mu.inv K ≠ 0 := by
    intro hK
    apply hinv_ne
    rw [heq, hK, zero_smul]
  have hK_top : mu.inv K ≠ ∞ := by
    by_contra hK_top
    have hexists : ∃ m : ℕ, mu.inv (spanningSets mu.inv m) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hinv_ne
      apply Measure.measure_univ_eq_zero.mp
      have hunion : ⋃ m : ℕ, spanningSets mu.inv m = Set.univ :=
        iUnion_spanningSets mu.inv
      rw [← hunion]
      exact measure_iUnion_null h
    obtain ⟨m, hm_ne⟩ := hexists
    have hm_top : mu.inv (spanningSets mu.inv m) = ∞ := by
      have hmeasure := congrArg
        (fun m' : Measure G => m' (spanningSets mu.inv m)) heq
      change mu.inv (spanningSets mu.inv m) =
        (mu.inv K • haarMeasure K) (spanningSets mu.inv m) at hmeasure
      rw [Measure.smul_apply, hK_top] at hmeasure
      have hhaar_ne : haarMeasure K (spanningSets mu.inv m) ≠ 0 := by
        intro hhaar
        apply hm_ne
        simpa [hhaar] using hmeasure
      simpa [hhaar_ne] using hmeasure
    exact (measure_spanningSets_lt_top mu.inv m).ne hm_top
  rw [heq]
  exact IsHaarMeasure.smul (haarMeasure K) hK_ne hK_top

/-- A nonzero sigma-finite right-invariant measure is the uniquely determined
positive scalar multiple of the inverse of any fixed left Haar measure.  No
unimodularity assumption is made: the comparison target is deliberately
`nu.inv`, not `nu`. -/
theorem eq_smul_inv_of_sigmaFinite_rightInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (mu nu : Measure G) [SigmaFinite mu] [IsMulRightInvariant mu]
    [IsHaarMeasure nu] (hmu : mu ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ mu = c • nu.inv := by
  letI : IsHaarMeasure mu.inv :=
    isHaarMeasure_inv_of_sigmaFinite_rightInvariant mu hmu
  let c : ℝ≥0∞ := haarScalarFactor mu.inv nu
  have hc_pos : 0 < c := by
    unfold c
    exact_mod_cast haarScalarFactor_pos_of_isHaarMeasure mu.inv nu
  have hc_top : c ≠ ∞ := by
    unfold c
    exact ENNReal.coe_ne_top
  have hinv : mu.inv = haarScalarFactor mu.inv nu • nu :=
    isMulLeftInvariant_eq_smul mu.inv nu
  refine ⟨c, hc_pos.ne', hc_top, ?_⟩
  calc
    mu = Measure.inv (Measure.inv mu) := (Measure.inv_inv mu).symm
    _ = Measure.inv (c • nu) := by
      apply congrArg Measure.inv
      simpa only [c] using hinv
    _ = c • Measure.inv nu := by
      simp only [Measure.inv_def, Measure.map_smul]

/-- A left-invariant inversion-invariant measure is right invariant. -/
theorem isMulRightInvariant_of_isInvInvariant
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [MeasurableInv G]
    (mu : Measure G) [IsMulLeftInvariant mu] [IsInvInvariant mu] :
    IsMulRightInvariant mu := by
  rw [← inv_eq_self mu]
  infer_instance

/-- For an inner-regular Haar measure, triviality of the modular character
is equivalent to right invariance. -/
theorem modularCharacterFun_eq_one_iff_isMulRightInvariant
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [IsHaarMeasure mu] [InnerRegular mu] :
    (∀ g : G, modularCharacterFun g = 1) ↔ IsMulRightInvariant mu := by
  constructor
  · intro h
    exact ⟨fun g => by
      simpa [h g] using map_right_mul_eq_modularCharacterFun_smul mu g⟩
  · intro h
    letI : IsMulRightInvariant mu := h
    intro g
    simpa only [MeasureTheory.map_mul_right_eq_self,
      haarScalarFactor_self] using
      modularCharacterFun_eq_haarScalarFactor mu g

/-- A regular Haar measure which is also right invariant is invariant under
inversion.  This is the noncommutative form of Mathlib's abelian Haar
inversion theorem. -/
theorem isInvInvariant_of_isMulRightInvariant_of_regular
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [IsHaarMeasure mu] [IsMulRightInvariant mu]
    [LocallyCompactSpace G] [Regular mu] :
    IsInvInvariant mu := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor mu.inv mu
  have hc : mu.inv = c • mu :=
    isMulLeftInvariant_eq_smul_of_regular mu.inv mu
  have hdouble : map Inv.inv (map Inv.inv mu) = c ^ 2 • mu := by
    rw [← inv_def mu, hc, Measure.map_smul, ← inv_def mu, hc,
      smul_smul, pow_two]
  have mueq : mu = c ^ 2 • mu := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at hdouble
    simpa only [inv_involutive, Function.Involutive.comp_self,
      Measure.map_id] using hdouble
  have K : PositiveCompacts G := Classical.arbitrary _
  have hc_sq : c ^ 2 = 1 ^ 2 := by
    apply (ENNReal.mul_left_inj
      (measure_pos_of_nonempty_interior mu K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1
    conv_rhs => rw [mueq]
    simp
  have hc_one : c = 1 :=
    (ENNReal.pow_right_strictMono two_ne_zero).injective hc_sq
  rw [hc, hc_one, one_smul]

/-- The same inversion theorem with inner regularity instead of full
regularity. -/
theorem isInvInvariant_of_isMulRightInvariant_of_innerRegular
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [IsHaarMeasure mu] [IsMulRightInvariant mu]
    [LocallyCompactSpace G] [InnerRegular mu] :
    IsInvInvariant mu := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor mu.inv mu
  have hc : mu.inv = c • mu :=
    isMulLeftInvariant_eq_smul_of_innerRegular mu.inv mu
  have hdouble : map Inv.inv (map Inv.inv mu) = c ^ 2 • mu := by
    rw [← inv_def mu, hc, Measure.map_smul, ← inv_def mu, hc,
      smul_smul, pow_two]
  have mueq : mu = c ^ 2 • mu := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at hdouble
    simpa only [inv_involutive, Function.Involutive.comp_self,
      Measure.map_id] using hdouble
  have K : PositiveCompacts G := Classical.arbitrary _
  have hc_sq : c ^ 2 = 1 ^ 2 := by
    apply (ENNReal.mul_left_inj
      (measure_pos_of_nonempty_interior mu K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1
    conv_rhs => rw [mueq]
    simp
  have hc_one : c = 1 :=
    (ENNReal.pow_right_strictMono two_ne_zero).injective hc_sq
  rw [hc, hc_one, one_smul]

/-- For a regular Haar measure, trivial modular character implies inversion
invariance. -/
theorem isInvInvariant_of_modularCharacterFun_eq_one
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [IsHaarMeasure mu] [Regular mu] [InnerRegular mu]
    (h : ∀ g : G, modularCharacterFun g = 1) :
    IsInvInvariant mu := by
  letI : IsMulRightInvariant mu :=
    (modularCharacterFun_eq_one_iff_isMulRightInvariant mu).1 h
  exact isInvInvariant_of_isMulRightInvariant_of_regular mu

end MeasureTheory.Measure
