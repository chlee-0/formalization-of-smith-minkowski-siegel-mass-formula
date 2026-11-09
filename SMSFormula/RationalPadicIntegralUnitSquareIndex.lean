import SMSFormula.RationalPadicUnitSquareClass
import SMSFormula.RationalDyadicSquareClass
import SMSFormula.RationalCliffordGeneralSpinPadicIntegralCoordinates

/-!
# Exact square index in compact p-adic unit groups

The square subgroup of the compact-open integral units in `ℚ_[p]ˣ` has
index two at every odd prime and index four at the dyadic prime.  The odd
calculation is transported from the established two-class theorem.  At `2`,
reduction to `(ZMod 8)ˣ` is onto and has exactly the same kernel as the
p-adic square-class map, so its four-element range computes the index.

This is the finite Haar-normalization input for the local square branch.  It
contains no local Jacobian assertion, Euler product, or sheet factor.
-/

noncomputable section

open RationalQuadraticSpaceMatrix
open MeasureTheory
open scoped ENNReal

namespace Rat

set_option maxHeartbeats 1000000

noncomputable local instance padicIntegralSquareIndexMeasurableSpace
    (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance padicIntegralSquareIndexBorelSpace
    (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

def dyadicUnitResidueHom : ℤ_[2]ˣ →* (ZMod 8)ˣ :=
  Units.map (PadicInt.toZModPow 3).toMonoidHom

theorem dyadicUnitResidueHom_surjective :
    Function.Surjective dyadicUnitResidueHom := by
  intro u
  let x : ℤ_[2] := ((u : ZMod 8).val : ℕ)
  have huunit : IsUnit (u : ZMod 8) := Units.isUnit u
  have hcop : (u : ZMod 8).val.Coprime 8 := by
    have hxcast : ((u : ZMod 8).val : ZMod 8) = (u : ZMod 8) :=
      ZMod.natCast_zmod_val _
    rw [← ZMod.isUnit_iff_coprime]
    simpa only [hxcast] using huunit
  have huval : (u : ZMod 8).val < 8 := (u : ZMod 8).val_lt
  have hx : PadicInt.toZModPow 3 x = (u : ZMod 8) := by
    apply ZMod.val_injective
    interval_cases h : (u : ZMod 8).val
    all_goals norm_num [h] at hcop
    all_goals norm_num [x, h]
  have hxunit : IsUnit x := by
    interval_cases h : (u : ZMod 8).val
    all_goals norm_num [h] at hcop
    all_goals
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      norm_num [x, h]
  refine ⟨hxunit.unit, ?_⟩
  apply Units.ext
  simpa [dyadicUnitResidueHom, hxunit.unit_spec] using hx

private theorem isSquare_unit_iff_isSquare_val
    {K : Type*} [Field K] (x : Kˣ) :
    IsSquare x ↔ IsSquare (x : K) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(y : K), congrArg Units.val hy⟩
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro hyzero
      have hxzero := hy
      simp only [hyzero, zero_mul] at hxzero
      exact x.ne_zero hxzero
    refine ⟨Units.mk0 y hy0, ?_⟩
    apply Units.ext
    exact hy

theorem mem_ker_padicUnitSquareClassHom_two_iff
    (u : ℤ_[2]ˣ) :
    u ∈ (padicUnitSquareClassHom 2).ker ↔
      PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 := by
  change padicUnitSquareClassHom 2 u = 1 ↔ _
  change (((Units.map PadicInt.Coe.ringHom.toMonoidHom u : ℚ_[2]ˣ) :
      SquareClass ℚ_[2]) = 1) ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_square,
    isSquare_unit_iff_isSquare_val]
  change IsSquare (((u : ℤ_[2]) : ℚ_[2])) ↔ _
  exact PadicInt.isSquare_coe_iff_toZModPow_three_eq_one_of_isUnit
    (Units.isUnit u)

theorem ker_padicUnitSquareClassHom_two_eq_dyadicUnitResidueHom_ker :
    (padicUnitSquareClassHom 2).ker = dyadicUnitResidueHom.ker := by
  ext u
  rw [mem_ker_padicUnitSquareClassHom_two_iff]
  change _ ↔ dyadicUnitResidueHom u = 1
  rw [Units.ext_iff]
  rfl

theorem natCard_dyadicUnitResidueHom_range_eq_four :
    Nat.card dyadicUnitResidueHom.range = 4 := by
  have hrange : dyadicUnitResidueHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr dyadicUnitResidueHom_surjective
  rw [hrange]
  rw [Subgroup.card_top]
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rfl

theorem natCard_padicUnitSquareClassSubgroup_two_eq_four :
    Nat.card (padicUnitSquareClassSubgroup 2) = 4 := by
  change Nat.card (padicUnitSquareClassHom 2).range = 4
  rw [← Subgroup.index_ker (padicUnitSquareClassHom 2),
    ker_padicUnitSquareClassHom_two_eq_dyadicUnitResidueHom_ker,
    Subgroup.index_ker, natCard_dyadicUnitResidueHom_range_eq_four]

def padicIntUnitToIntegralUnitHom
    (p : ℕ) [Fact p.Prime] :
    ℤ_[p]ˣ →* padicIntegralUnitsSubgroup p where
  toFun u := ⟨Units.map PadicInt.Coe.ringHom.toMonoidHom u, by
    constructor
    · exact (u : ℤ_[p]).property
    · change (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) ∈ PadicInt.subring p
      exact ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]).property⟩
  map_one' := by ext; simp
  map_mul' u v := by ext; simp

def padicIntegralUnitSquareClassHom
    (p : ℕ) [Fact p.Prime] :
    padicIntegralUnitsSubgroup p →* SquareClass ℚ_[p] :=
  (QuotientGroup.mk' (Subgroup.square ℚ_[p]ˣ)).comp
    (padicIntegralUnitsSubgroup p).subtype

theorem padicIntegralUnitSquareClassHom_comp_padicIntUnitToIntegralUnitHom
    (p : ℕ) [Fact p.Prime] :
    (padicIntegralUnitSquareClassHom p).comp
        (padicIntUnitToIntegralUnitHom p) =
      padicUnitSquareClassHom p := by
  rfl

private noncomputable def integralUnitToPadicIntUnit
    (p : ℕ) [Fact p.Prime]
    (u : padicIntegralUnitsSubgroup p) : ℤ_[p]ˣ := by
  let a : ℤ_[p] := ⟨(u.1 : ℚ_[p]), u.2.1⟩
  let b : ℤ_[p] := ⟨((u.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), u.2.2⟩
  exact Units.mkOfMulEqOne a b (by
    apply Subtype.ext
    change (u.1 : ℚ_[p]) * ((u.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = 1
    simp)

private theorem padicIntUnitToIntegralUnitHom_integralUnitToPadicIntUnit
    (p : ℕ) [Fact p.Prime]
    (u : padicIntegralUnitsSubgroup p) :
    padicIntUnitToIntegralUnitHom p (integralUnitToPadicIntUnit p u) = u := by
  apply Subtype.ext
  apply Units.ext
  rfl

theorem padicIntUnitToIntegralUnitHom_surjective
    (p : ℕ) [Fact p.Prime] :
    Function.Surjective (padicIntUnitToIntegralUnitHom p) := by
  intro u
  exact ⟨integralUnitToPadicIntUnit p u,
    padicIntUnitToIntegralUnitHom_integralUnitToPadicIntUnit p u⟩

theorem padicIntegralUnitSquareClassHom_range_eq
    (p : ℕ) [Fact p.Prime] :
    (padicIntegralUnitSquareClassHom p).range =
      padicUnitSquareClassSubgroup p := by
  rw [padicUnitSquareClassSubgroup]
  apply le_antisymm
  · rintro x ⟨u, rfl⟩
    obtain ⟨z, rfl⟩ := padicIntUnitToIntegralUnitHom_surjective p u
    exact ⟨z, by
      rw [← MonoidHom.comp_apply,
        padicIntegralUnitSquareClassHom_comp_padicIntUnitToIntegralUnitHom]⟩
  · rintro x ⟨z, rfl⟩
    exact ⟨padicIntUnitToIntegralUnitHom p z, by
      rw [← MonoidHom.comp_apply,
        padicIntegralUnitSquareClassHom_comp_padicIntUnitToIntegralUnitHom]⟩

theorem natCard_padicIntegralUnitSquareClassHom_range_eq_two_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Nat.card (padicIntegralUnitSquareClassHom p).range = 2 := by
  rw [padicIntegralUnitSquareClassHom_range_eq,
    natCard_padicUnitSquareClassSubgroup_eq_two p hp]

theorem natCard_padicIntegralUnitSquareClassHom_range_two_eq_four :
    Nat.card (padicIntegralUnitSquareClassHom 2).range = 4 := by
  rw [padicIntegralUnitSquareClassHom_range_eq,
    natCard_padicUnitSquareClassSubgroup_two_eq_four]

theorem mem_padicIntegralUnitsSubgroup_of_sq_mem
    (p : ℕ) [Fact p.Prime] (z : ℚ_[p]ˣ)
    (hz : z ^ 2 ∈ padicIntegralUnitsSubgroup p) :
    z ∈ padicIntegralUnitsSubgroup p := by
  rw [mem_padicIntegralUnitsSubgroup_iff] at hz ⊢
  constructor
  · rw [PadicInt.mem_subring_iff] at hz ⊢
    have hpow : ‖((z : ℚ_[p]))‖ ^ 2 ≤ 1 := by
      simpa [norm_pow] using hz.1
    nlinarith [norm_nonneg (z : ℚ_[p])]
  · rw [PadicInt.mem_subring_iff] at hz ⊢
    have hpow : ‖(((z⁻¹ : ℚ_[p]ˣ) : ℚ_[p]))‖ ^ 2 ≤ 1 := by
      simpa [norm_pow] using hz.2
    nlinarith [norm_nonneg ((z⁻¹ : ℚ_[p]ˣ) : ℚ_[p])]

theorem ker_padicIntegralUnitSquareClassHom_eq_square
    (p : ℕ) [Fact p.Prime] :
    (padicIntegralUnitSquareClassHom p).ker =
      Subgroup.square (padicIntegralUnitsSubgroup p) := by
  ext u
  change ((u.1 : SquareClass ℚ_[p]) = 1) ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_square]
  constructor
  · rintro ⟨z, hz⟩
    have hzmem : z ∈ padicIntegralUnitsSubgroup p :=
      mem_padicIntegralUnitsSubgroup_of_sq_mem p z (by
        rw [pow_two, ← hz]
        exact u.2)
    refine ⟨⟨z, hzmem⟩, ?_⟩
    apply Subtype.ext
    simpa using hz
  · rintro ⟨z, hz⟩
    exact ⟨z.1, congrArg Subtype.val hz⟩

theorem index_square_padicIntegralUnitsSubgroup_eq_two_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Subgroup.square (padicIntegralUnitsSubgroup p)).index = 2 := by
  rw [← ker_padicIntegralUnitSquareClassHom_eq_square,
    Subgroup.index_ker,
    natCard_padicIntegralUnitSquareClassHom_range_eq_two_of_ne_two p hp]

theorem index_square_padicIntegralUnitsSubgroup_two_eq_four :
    (Subgroup.square (padicIntegralUnitsSubgroup 2)).index = 4 := by
  rw [← ker_padicIntegralUnitSquareClassHom_eq_square,
    Subgroup.index_ker,
    natCard_padicIntegralUnitSquareClassHom_range_two_eq_four]

theorem isOpen_square_padicUnitsSubgroup
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (Subgroup.square ℚ_[p]ˣ : Set ℚ_[p]ˣ) := by
  obtain ⟨U, hUopen, hUone, hU⟩ :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit
      (p := p) (c := (1 : ℚ_[p])) one_ne_zero
  apply (Subgroup.square ℚ_[p]ˣ).isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset
    (Units.continuous_val.continuousAt (by simpa using hUopen.mem_nhds hUone)) ?_
  intro x hx
  obtain ⟨s, hs0, hs⟩ := hU hx
  change x ∈ Subgroup.square ℚ_[p]ˣ
  rw [Subgroup.mem_square]
  refine ⟨Units.mk0 s hs0, ?_⟩
  apply Units.ext
  simpa [pow_two] using hs

theorem isOpen_square_padicIntegralUnitsSubgroup
    (p : ℕ) [Fact p.Prime] :
    IsOpen
      (Subgroup.square (padicIntegralUnitsSubgroup p) :
        Set (padicIntegralUnitsSubgroup p)) := by
  refine ⟨(Subgroup.square ℚ_[p]ˣ : Set ℚ_[p]ˣ),
    isOpen_square_padicUnitsSubgroup p, ?_⟩
  ext u
  constructor
  · intro hu
    change u.1 ∈ Subgroup.square ℚ_[p]ˣ at hu
    change u ∈ Subgroup.square (padicIntegralUnitsSubgroup p)
    rw [Subgroup.mem_square] at hu ⊢
    rcases hu with ⟨z, hz⟩
    have hzmem : z ∈ padicIntegralUnitsSubgroup p :=
      mem_padicIntegralUnitsSubgroup_of_sq_mem p z (by
        rw [pow_two, ← hz]
        exact u.2)
    exact ⟨⟨z, hzmem⟩, Subtype.ext hz⟩
  · intro hu
    change u ∈ Subgroup.square (padicIntegralUnitsSubgroup p) at hu
    change u.1 ∈ Subgroup.square ℚ_[p]ˣ
    rw [Subgroup.mem_square] at hu ⊢
    rcases hu with ⟨z, hz⟩
    exact ⟨z.1, congrArg Subtype.val hz⟩

/-- At an odd p-adic place, two square cosets exhaust the compact integral
unit group, so finite-index Haar algebra gives the literal factor `2`. -/
theorem two_mul_measure_square_padicIntegralUnitsSubgroup_eq_univ
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (mu : Measure (padicIntegralUnitsSubgroup p))
    [Measure.IsMulLeftInvariant mu] :
    (2 : ℝ≥0∞) * mu
        (Subgroup.square (padicIntegralUnitsSubgroup p) :
          Set (padicIntegralUnitsSubgroup p)) =
      mu Set.univ := by
  letI : (Subgroup.square (padicIntegralUnitsSubgroup p)).FiniteIndex := by
    exact Subgroup.finiteIndex_iff.mpr (by
      rw [index_square_padicIntegralUnitsSubgroup_eq_two_of_ne_two p hp]
      norm_num)
  have h := Subgroup.index_mul_measure
    (Subgroup.square (padicIntegralUnitsSubgroup p))
    (isOpen_square_padicIntegralUnitsSubgroup p).measurableSet mu
  rw [index_square_padicIntegralUnitsSubgroup_eq_two_of_ne_two p hp] at h
  exact h

/-- At the dyadic place, four square cosets exhaust the compact integral
unit group, giving the literal factor `4`. -/
theorem four_mul_measure_square_padicIntegralUnitsSubgroup_two_eq_univ
    (mu : Measure (padicIntegralUnitsSubgroup 2))
    [Measure.IsMulLeftInvariant mu] :
    (4 : ℝ≥0∞) * mu
        (Subgroup.square (padicIntegralUnitsSubgroup 2) :
          Set (padicIntegralUnitsSubgroup 2)) =
      mu Set.univ := by
  letI : (Subgroup.square (padicIntegralUnitsSubgroup 2)).FiniteIndex := by
    exact Subgroup.finiteIndex_iff.mpr (by
      rw [index_square_padicIntegralUnitsSubgroup_two_eq_four]
      norm_num)
  have h := Subgroup.index_mul_measure
    (Subgroup.square (padicIntegralUnitsSubgroup 2))
    (isOpen_square_padicIntegralUnitsSubgroup 2).measurableSet mu
  rw [index_square_padicIntegralUnitsSubgroup_two_eq_four] at h
  exact h

end Rat
