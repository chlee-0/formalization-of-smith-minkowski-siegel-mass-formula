import SMSFormula.RationalAdeleFiniteLocalResidueCount
import SMSFormula.RationalAdeleFiniteLocalTruncationStandardCarried

/-!
# Residue-restricted tests and their congruence tube masses

For a supplied level `N₀ ≠ 0` and a supplied residue set `R ⊆ (ZMod N₀)^n`, the
residue-restricted indicator `1_{U_R}` is `1` exactly on the integral vectors whose
section-free residue class modulo `N₀ Zhat^n` lies in `R`.  It is standard-carried at scale one
and standard-periodic at level `N₀`, so it is in the `(c,d)` class; above rank four its
finite value density is therefore the limit of its congruence tube masses.

For every level `m` divisible by `N₀`, its level-`m` tube mass is an explicit restricted residue
count:

```text
∫ 1_{U_R}(x) 1_Zhat((Q(x) - M)/m) dx = m^{-n} #{z mod m : Q(z) = M, z mod N₀ ∈ R}.
```

This is the counting input of the finite-place replacement lemma.  `N₀`, `R` and `m` are supplied; no
representative of any quotient is chosen (integer representatives appear only inside proofs
through the residue model).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

open MeasureTheory RationalQuadraticSpaceMatrix Matrix Filter Topology
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The section-free residue of an integral vector modulo `N₀`. -/
def integralVectorResidue (n N₀ : ℕ) [NeZero N₀] (y : Fin n → IntegralFiniteAdele) :
    Fin n → ZMod N₀ :=
  (coordinateResidueEquivIntegralFiniteAdeleModDilation n N₀ (NeZero.ne N₀)).symm
    (y : (Fin n → IntegralFiniteAdele) ⧸ (integralFiniteAdeleCoordinateNatDilation n N₀).range)

theorem integralVectorResidue_intCast (n N₀ : ℕ) [NeZero N₀] (w : Fin n → ℤ) :
    integralVectorResidue n N₀ (integerToIntegralFiniteAdeleVector n w) =
      fun i ↦ ((w i : ℤ) : ZMod N₀) := by
  rw [integralVectorResidue, AddEquiv.symm_apply_eq,
    coordinateResidueEquivIntegralFiniteAdeleModDilation_apply_intCast]
  rfl

/-- The residue is unchanged by adding a vector of the `m`-dilated lattice when `N₀ ∣ m`. -/
theorem integralVectorResidue_add_dilation {N₀ m : ℕ} [NeZero N₀] (hdvd : N₀ ∣ m)
    (x z : Fin n → IntegralFiniteAdele)
    (hz : z ∈ (integralFiniteAdeleCoordinateNatDilation n m).range) :
    integralVectorResidue n N₀ (x + z) = integralVectorResidue n N₀ x := by
  obtain ⟨c, rfl⟩ := hdvd
  obtain ⟨u, rfl⟩ := hz
  have hmem : integralFiniteAdeleCoordinateNatDilation n (N₀ * c) u ∈
      (integralFiniteAdeleCoordinateNatDilation n N₀).range := by
    refine ⟨integralFiniteAdeleCoordinateNatDilation n c u, ?_⟩
    funext i
    apply Subtype.ext
    change (N₀ : ℕ) • ((c : ℕ) • ((u i : IntegralFiniteAdele) : RationalFiniteAdele)) =
      (N₀ * c : ℕ) • ((u i : IntegralFiniteAdele) : RationalFiniteAdele)
    rw [smul_smul]
  rw [integralVectorResidue, integralVectorResidue, QuotientAddGroup.mk_add,
    (QuotientAddGroup.eq_zero_iff _).mpr hmem, add_zero]

open Classical in
/-- The residue-restricted indicator `1_{U_R}` on finite-adelic vectors. -/
def residueRestrictedIndicator (n N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀))
    (x : Fin n → RationalFiniteAdele) : ℂ :=
  if h : x ∈ integralFiniteAdeleVectors n then
    (if integralVectorResidue n N₀ (fun i ↦ ⟨x i, h i⟩) ∈ R then 1 else 0)
  else 0

theorem isStandardCarried_residueRestrictedIndicator (N₀ : ℕ) [NeZero N₀]
    (R : Set (Fin n → ZMod N₀)) :
    IsStandardCarried 1 (residueRestrictedIndicator n N₀ R) := by
  intro x hx
  have hx' : x ∉ integralFiniteAdeleVectors n := by simpa [standardDividedLattice] using hx
  rw [residueRestrictedIndicator, dif_neg hx']

theorem isStandardPeriodic_residueRestrictedIndicator (N₀ : ℕ) [NeZero N₀]
    (R : Set (Fin n → ZMod N₀)) :
    IsStandardPeriodic N₀ (residueRestrictedIndicator n N₀ R) := by
  intro x u hu
  have hNu : N₀ • u ∈ integralFiniteAdeleVectors n := nsmul_mem_integralFiniteAdeleVectors hu
  by_cases hx : x ∈ integralFiniteAdeleVectors n
  · have hxu : x + N₀ • u ∈ integralFiniteAdeleVectors n := fun i ↦
      integralFiniteAdeleSubring.add_mem (hx i) (hNu i)
    rw [residueRestrictedIndicator, residueRestrictedIndicator, dif_pos hx, dif_pos hxu]
    have hsplit : (fun i ↦ (⟨(x + N₀ • u) i, hxu i⟩ : IntegralFiniteAdele)) =
        (fun i ↦ (⟨x i, hx i⟩ : IntegralFiniteAdele)) +
          integralFiniteAdeleCoordinateNatDilation n N₀ (fun i ↦ ⟨u i, hu i⟩) := by
      funext i
      apply Subtype.ext
      rfl
    rw [hsplit, integralVectorResidue_add_dilation (dvd_refl N₀) _ _ ⟨_, rfl⟩]
  · have hxu : x + N₀ • u ∉ integralFiniteAdeleVectors n := by
      intro h
      apply hx
      have := fun i ↦ integralFiniteAdeleSubring.sub_mem (h i) (hNu i)
      simpa using this
    rw [residueRestrictedIndicator, residueRestrictedIndicator, dif_neg hx, dif_neg hxu]

/-- The restricted congruence indicator on integral vectors. -/
def restrictedCongruenceIndicator (L : PositiveDefiniteIntegralLattice n) (N₀ : ℕ) [NeZero N₀]
    (R : Set (Fin n → ZMod N₀)) (m : ℕ) (M : ℤ) (x : Fin n → IntegralFiniteAdele) : ℂ :=
  open Classical in
  (if integralVectorResidue n N₀ x ∈ R then 1 else 0) * L.congruenceIndicator m M x

theorem restrictedCongruenceIndicator_add_dilation (L : PositiveDefiniteIntegralLattice n) {N₀ m : ℕ}
    [NeZero N₀] (hdvd : N₀ ∣ m) (R : Set (Fin n → ZMod N₀)) (M : ℤ)
    (x z : Fin n → IntegralFiniteAdele)
    (hz : z ∈ (integralFiniteAdeleCoordinateNatDilation n m).range) :
    L.restrictedCongruenceIndicator N₀ R m M (x + z) =
      L.restrictedCongruenceIndicator N₀ R m M x := by
  rw [restrictedCongruenceIndicator, restrictedCongruenceIndicator,
    integralVectorResidue_add_dilation hdvd x z hz, L.congruenceIndicator_add_dilation m M x z hz]

theorem integral_restrictedCongruence_eq_subtype (L : PositiveDefiniteIntegralLattice n) (N₀ : ℕ) [NeZero N₀]
    (R : Set (Fin n → ZMod N₀)) (m : ℕ) (M : ℤ) :
    (∫ x : Fin n → RationalFiniteAdele,
        residueRestrictedIndicator n N₀ R x *
          rationalFiniteAdeleIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
              (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      ∫ x : Fin n → IntegralFiniteAdele, L.restrictedCongruenceIndicator N₀ R m M x
        ∂integralFiniteAdeleCoordinateAddHaarMeasure n := by
  set f : (Fin n → RationalFiniteAdele) → ℂ := fun x =>
    rationalFiniteAdeleIntegralIndicator
      (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
        (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
          algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ))) with hf
  have hmeasf : Measurable f := by
    rw [hf]
    have hcont : Continuous fun x : Fin n → RationalFiniteAdele =>
        algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
          (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
            algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) := by
      unfold RationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
      fun_prop
    have hind : Measurable rationalFiniteAdeleIntegralIndicator := by
      have heq : rationalFiniteAdeleIntegralIndicator =
          Set.indicator (integralFiniteAdeleSubring : Set RationalFiniteAdele)
            (fun _ => (1 : ℂ)) := rfl
      rw [heq]
      exact measurable_const.indicator isOpen_integralFiniteAdeleSubring.measurableSet
    exact hind.comp hcont.measurable
  have hmeasR : Measurable (residueRestrictedIndicator n N₀ R) :=
    IntegralFiniteAdelePhase.measurable_of_standardCarried one_ne_zero (NeZero.ne N₀)
      (isStandardCarried_residueRestrictedIndicator N₀ R)
      (isStandardPeriodic_residueRestrictedIndicator N₀ R)
  have hpoint : ∀ x : Fin n → RationalFiniteAdele,
      residueRestrictedIndicator n N₀ R x * f x =
        Set.indicator (integralFiniteAdeleVectors n)
          (fun x ↦ residueRestrictedIndicator n N₀ R x * f x) x := by
    intro x
    by_cases hx : x ∈ integralFiniteAdeleVectors n
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, residueRestrictedIndicator, dif_neg hx, zero_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_indicator (measurableSet_integralFiniteAdeleVectors n),
    ← (measurePreserving_integralFiniteAdeleCoordinateCoe n).map_eq,
    integral_map (measurePreserving_integralFiniteAdeleCoordinateCoe n).aemeasurable
      (hmeasR.mul hmeasf).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  have hy : integralFiniteAdeleCoordinateCoe n y ∈ integralFiniteAdeleVectors n := fun i ↦ (y i).2
  show residueRestrictedIndicator n N₀ R (integralFiniteAdeleCoordinateCoe n y) *
      f (integralFiniteAdeleCoordinateCoe n y) = _
  rw [residueRestrictedIndicator, dif_pos hy, restrictedCongruenceIndicator]
  rfl

/-- The restricted congruence indicator on the residue cube. -/
theorem restrictedCongruenceIndicator_integerVector (L : PositiveDefiniteIntegralLattice n) {N₀ m : ℕ}
    [NeZero N₀] (hm : m ≠ 0) (R : Set (Fin n → ZMod N₀)) (M : ℤ) (w : Fin n → ℤ) :
    L.restrictedCongruenceIndicator N₀ R m M (integerToIntegralFiniteAdeleVector n w) =
      open Classical in
      (if (fun i ↦ ((w i : ℤ) : ZMod N₀)) ∈ R then 1 else 0) *
        (if ((m : ℤ)) ∣ (L.quadForm w - M) then 1 else 0) := by
  rw [restrictedCongruenceIndicator, integralVectorResidue_intCast,
    L.congruenceIndicator_integerVector hm M w]

set_option maxHeartbeats 4000000 in
/-- The level-`m` tube mass of a residue-restricted test is a restricted residue count, for every
level `m` divisible by `N₀`. -/
theorem measure_restrictedCongruenceSet_eq_residueCount (L : PositiveDefiniteIntegralLattice n) {N₀ m : ℕ}
    [NeZero N₀] (hm : m ≠ 0) (hdvd : N₀ ∣ m) (R : Set (Fin n → ZMod N₀)) (M : ℤ) :
    (∫ x : Fin n → RationalFiniteAdele,
        residueRestrictedIndicator n N₀ R x *
          rationalFiniteAdeleIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
              (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      (((m : ℝ) ^ n : ℂ))⁻¹ *
        (Nat.card {z : Fin n → ZMod m // L.zmodQuadForm m z = ((M : ℤ) : ZMod m) ∧
          (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ R} : ℂ) := by
  haveI : NeZero m := ⟨hm⟩
  classical
  rw [integral_restrictedCongruence_eq_subtype L N₀ R m M,
    integralFiniteAdeleCoordinate_integral_periodic_eq_inv_pow_sum n m
      (L.restrictedCongruenceIndicator N₀ R m M)
      (L.restrictedCongruenceIndicator_add_dilation hdvd R M)]
  congr 1
  rw [← Equiv.sum_comp
    (coordinateResidueEquivIntegralFiniteAdeleModDilation n m hm).toEquiv
    (addQuotientPeriodicLift (integralFiniteAdeleCoordinateNatDilation n m).range
      (L.restrictedCongruenceIndicator N₀ R m M)
      (L.restrictedCongruenceIndicator_add_dilation hdvd R M))]
  have hterm : ∀ z : Fin n → ZMod m,
      addQuotientPeriodicLift (integralFiniteAdeleCoordinateNatDilation n m).range
          (L.restrictedCongruenceIndicator N₀ R m M)
          (L.restrictedCongruenceIndicator_add_dilation hdvd R M)
          ((coordinateResidueEquivIntegralFiniteAdeleModDilation n m hm).toEquiv z) =
        if L.zmodQuadForm m z = ((M : ℤ) : ZMod m) ∧
            (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ R then 1 else 0 := by
    intro z
    have hrep : (fun i => (((((z i).val : ℕ) : ℤ)) : ZMod m)) = z := by
      funext i
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id]
    have hcast : (fun i ↦ ((((z i).val : ℕ) : ℤ) : ZMod N₀)) =
        (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) := by
      funext i
      rw [ZMod.castHom_apply, Int.cast_natCast, ZMod.natCast_val]
    conv_lhs => rw [← hrep]
    change addQuotientPeriodicLift (integralFiniteAdeleCoordinateNatDilation n m).range
        (L.restrictedCongruenceIndicator N₀ R m M)
        (L.restrictedCongruenceIndicator_add_dilation hdvd R M)
        (coordinateResidueEquivIntegralFiniteAdeleModDilation n m hm
          (fun i => (((((z i).val : ℕ) : ℤ)) : ZMod m))) = _
    rw [coordinateResidueEquivIntegralFiniteAdeleModDilation_apply_intCast]
    change L.restrictedCongruenceIndicator N₀ R m M
        (integerToIntegralFiniteAdeleVector n fun i ↦ (((z i).val : ℕ) : ℤ)) = _
    rw [L.restrictedCongruenceIndicator_integerVector hm R M, hcast]
    have hQ : (((m : ℤ)) ∣ (L.quadForm (fun i ↦ (((z i).val : ℕ) : ℤ)) - M)) ↔
        L.zmodQuadForm m z = ((M : ℤ) : ZMod m) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero,
        ← zmodQuadForm_intCast, hrep]
    by_cases h1 : (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ R
    · by_cases h2 : L.zmodQuadForm m z = ((M : ℤ) : ZMod m)
      · rw [if_pos h1, if_pos (hQ.2 h2), if_pos ⟨h2, h1⟩, one_mul]
      · rw [if_pos h1, if_neg (fun h ↦ h2 (hQ.1 h)), if_neg (fun h ↦ h2 h.1), mul_zero]
    · rw [if_neg h1, zero_mul, if_neg (fun h ↦ h1 h.2)]
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_boole]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- With the full residue set, the restricted indicator is the integral indicator. -/
theorem residueRestrictedIndicator_univ (N₀ : ℕ) [NeZero N₀] :
    residueRestrictedIndicator n N₀ Set.univ = rationalFiniteAdeleVectorIntegralIndicator := by
  funext x
  by_cases hx : x ∈ integralFiniteAdeleVectors n
  · rw [residueRestrictedIndicator, dif_pos hx, if_pos (Set.mem_univ _),
      rationalFiniteAdeleVectorIntegralIndicator_of_mem hx]
  · rw [residueRestrictedIndicator, dif_neg hx,
      rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx]

/-- The replacement lemma in counting form: above rank four, if the restricted residue counts at
the levels `k!` are eventually `κ` times the unrestricted ones, then
`d_fin(1_{U_R})(M) = κ · d_fin(1_Zhat)(M)`. -/
theorem finiteLocalValueDensity_residueRestricted_eq_mul_of_eventually_card_eq
    (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) (N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀))
    (M : ℤ) (κ : ℂ)
    (h : ∀ᶠ k : ℕ in atTop, ∀ hdvd : N₀ ∣ Nat.factorial k,
      (Nat.card {z : Fin n → ZMod (Nat.factorial k) //
          L.zmodQuadForm (Nat.factorial k) z = ((M : ℤ) : ZMod (Nat.factorial k)) ∧
          (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ R} : ℂ) =
        κ * (Nat.card {z : Fin n → ZMod (Nat.factorial k) //
          L.zmodQuadForm (Nat.factorial k) z = ((M : ℤ) : ZMod (Nat.factorial k)) ∧
          (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ (Set.univ : Set (Fin n → ZMod N₀))} : ℂ)) :
    L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity (residueRestrictedIndicator n N₀ R)
        (algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) =
      κ * L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity
        rationalFiniteAdeleVectorIntegralIndicator
        (algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) := by
  rw [← residueRestrictedIndicator_univ N₀]
  refine IntegralFiniteAdelePhase.finiteLocalValueDensity_eq_mul_of_eventually_tube_eq_of_standardCarried
    L hn one_ne_zero (NeZero.ne N₀) one_ne_zero (NeZero.ne N₀)
    (isStandardCarried_residueRestrictedIndicator N₀ R)
    (isStandardPeriodic_residueRestrictedIndicator N₀ R)
    (isStandardCarried_residueRestrictedIndicator N₀ Set.univ)
    (isStandardPeriodic_residueRestrictedIndicator N₀ Set.univ) ((M : ℤ) : ℚ) κ ?_
  filter_upwards [h, Filter.eventually_ge_atTop N₀] with k hk hkN
  have hdvd : N₀ ∣ Nat.factorial k := Nat.dvd_factorial (Nat.pos_of_ne_zero (NeZero.ne N₀)) hkN
  rw [L.measure_restrictedCongruenceSet_eq_residueCount (Nat.factorial_ne_zero k) hdvd R M,
    L.measure_restrictedCongruenceSet_eq_residueCount (Nat.factorial_ne_zero k) hdvd Set.univ M,
    hk hdvd]
  ring

end PositiveDefiniteIntegralLattice
