import SMSFormula.RationalPadicSquareClass
import SMSFormula.RationalSquareClassLocalGlobal
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Unit square classes over an odd rational p-adic field

This file isolates the two square classes represented by units in `ℚ_[p]`.
The subgroup is defined as the image of `ℤ_[p]ˣ` in
`Rat.SquareClass ℚ_[p]`.  For odd `p`, a chosen nonsquare residue class lifts
to a p-adic integral unit, and every unit class is either trivial or the class
of this lift.

This is only a statement about local square classes.  It does not assert that
the spinor norm of every integral special-orthogonal point belongs to this
subgroup.
-/

noncomputable section

namespace Rat

private lemma isSquare_unit_iff_isSquare_val
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

private lemma isSquare_padic_coe_iff_isSquare_padicInt_of_isUnit
    {p : ℕ} [Fact p.Prime] {u : ℤ_[p]} (hu : IsUnit u) :
    IsSquare ((u : ℤ_[p]) : ℚ_[p]) ↔ IsSquare u := by
  constructor
  · rintro ⟨x, hx⟩
    have hnormx : ‖x‖ = 1 := by
      have hsquare : ‖x‖ * ‖x‖ = 1 := by
        calc
          ‖x‖ * ‖x‖ = ‖x * x‖ := (norm_mul x x).symm
          _ = ‖(u : ℚ_[p])‖ := congrArg norm hx.symm
          _ = ‖u‖ := rfl
          _ = 1 := PadicInt.isUnit_iff.mp hu
      nlinarith [norm_nonneg x]
    refine ⟨⟨x, hnormx.le⟩, ?_⟩
    exact Subtype.ext hx
  · rintro ⟨x, hx⟩
    refine ⟨(x : ℚ_[p]), ?_⟩
    exact congrArg Subtype.val hx

private lemma padicInt_toZMod_ne_zero_of_isUnit
    {p : ℕ} [Fact p.Prime] {u : ℤ_[p]} (hu : IsUnit u) :
    PadicInt.toZMod u ≠ 0 := by
  rw [PadicInt.toZMod_eq_residueField_comp_residue]
  intro hzero
  have hreszero : IsLocalRing.residue ℤ_[p] u = 0 := by
    apply PadicInt.residueField.injective
    simpa using hzero
  exact (IsLocalRing.residue_ne_zero_iff_isUnit u).2 hu hreszero

private lemma isSquare_mul_of_not_isSquare_of_not_isSquare
    {F : Type*} [Field F] [Fintype F]
    {a b : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : ¬IsSquare a) (hb : ¬IsSquare b) :
    IsSquare (a * b) := by
  classical
  apply (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).mp
  rw [map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha,
    quadraticChar_neg_one_iff_not_isSquare.mpr hb]
  norm_num

/-- The map from units of the p-adic integers to p-adic square classes. -/
def padicUnitSquareClassHom (p : ℕ) [Fact p.Prime] :
    ℤ_[p]ˣ →* SquareClass ℚ_[p] :=
  (QuotientGroup.mk' (Subgroup.square ℚ_[p]ˣ)).comp
    (Units.map PadicInt.Coe.ringHom.toMonoidHom)

@[simp]
theorem padicUnitSquareClassHom_apply
    (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    padicUnitSquareClassHom p u =
      ((Units.map PadicInt.Coe.ringHom.toMonoidHom u : ℚ_[p]ˣ) :
        SquareClass ℚ_[p]) :=
  rfl

/-- The subgroup of p-adic square classes represented by integral units. -/
def padicUnitSquareClassSubgroup (p : ℕ) [Fact p.Prime] :
    Subgroup (SquareClass ℚ_[p]) :=
  (padicUnitSquareClassHom p).range

/-- For odd `p`, an integral unit has trivial p-adic square class exactly
when its residue is a square. -/
theorem padicUnitSquareClassHom_eq_one_iff_isSquare_toZMod
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) (u : ℤ_[p]ˣ) :
    padicUnitSquareClassHom p u = 1 ↔
      IsSquare (PadicInt.toZMod (u : ℤ_[p])) := by
  change
    (((Units.map PadicInt.Coe.ringHom.toMonoidHom u : ℚ_[p]ˣ) :
        SquareClass ℚ_[p]) = 1) ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_square,
    isSquare_unit_iff_isSquare_val]
  change IsSquare (((u : ℤ_[p]) : ℚ_[p])) ↔ _
  rw [isSquare_padic_coe_iff_isSquare_padicInt_of_isUnit (Units.isUnit u)]
  exact PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit
    hpodd (Units.isUnit u)

/-- A chosen nonsquare unit in the residue field at an odd prime. -/
noncomputable def oddPrimeNonsquareResidueUnit
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) : (ZMod p)ˣ :=
  Classical.choose
    (quadraticChar_exists_neg_one'
      (F := ZMod p) (by
        simpa [ZMod.ringChar_zmod_n] using hpodd))

theorem oddPrimeNonsquareResidueUnit_quadraticChar
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    quadraticChar (ZMod p)
        (oddPrimeNonsquareResidueUnit p hpodd : ZMod p) = -1 :=
  Classical.choose_spec
    (quadraticChar_exists_neg_one'
      (F := ZMod p) (by
        simpa [ZMod.ringChar_zmod_n] using hpodd))

theorem oddPrimeNonsquareResidueUnit_not_isSquare
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    ¬IsSquare (oddPrimeNonsquareResidueUnit p hpodd : ZMod p) :=
  quadraticChar_neg_one_iff_not_isSquare.mp
    (oddPrimeNonsquareResidueUnit_quadraticChar p hpodd)

private noncomputable def oddPrimeNonsquarePadicIntValue
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) : ℤ_[p] :=
  (((oddPrimeNonsquareResidueUnit p hpodd : ZMod p).val : ℕ) : ℤ_[p])

private theorem oddPrimeNonsquarePadicIntValue_toZMod
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    PadicInt.toZMod (oddPrimeNonsquarePadicIntValue p hpodd) =
      (oddPrimeNonsquareResidueUnit p hpodd : ZMod p) := by
  apply ZMod.val_injective
  simp [oddPrimeNonsquarePadicIntValue]

private theorem oddPrimeNonsquarePadicIntValue_isUnit
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    IsUnit (oddPrimeNonsquarePadicIntValue p hpodd) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro hzero
  have htozero :
      PadicInt.toZMod (oddPrimeNonsquarePadicIntValue p hpodd) = 0 := by
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    simp [hzero]
  rw [oddPrimeNonsquarePadicIntValue_toZMod] at htozero
  exact (Units.ne_zero (oddPrimeNonsquareResidueUnit p hpodd)) htozero

/-- A chosen p-adic integral unit lifting the chosen nonsquare residue. -/
noncomputable def oddPrimeNonsquarePadicIntUnit
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) : ℤ_[p]ˣ :=
  (oddPrimeNonsquarePadicIntValue_isUnit p hpodd).unit

@[simp]
theorem oddPrimeNonsquarePadicIntUnit_toZMod
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    PadicInt.toZMod (oddPrimeNonsquarePadicIntUnit p hpodd : ℤ_[p]) =
      (oddPrimeNonsquareResidueUnit p hpodd : ZMod p) := by
  rw [oddPrimeNonsquarePadicIntUnit,
    (oddPrimeNonsquarePadicIntValue_isUnit p hpodd).unit_spec,
    oddPrimeNonsquarePadicIntValue_toZMod]

theorem oddPrimeNonsquarePadicIntUnit_not_isSquare
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    ¬IsSquare (oddPrimeNonsquarePadicIntUnit p hpodd : ℤ_[p]) := by
  intro hsquare
  have hresidue :
      IsSquare
        (PadicInt.toZMod (oddPrimeNonsquarePadicIntUnit p hpodd : ℤ_[p])) :=
    (PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hpodd
      (Units.isUnit (oddPrimeNonsquarePadicIntUnit p hpodd))).mp hsquare
  rw [oddPrimeNonsquarePadicIntUnit_toZMod] at hresidue
  exact oddPrimeNonsquareResidueUnit_not_isSquare p hpodd hresidue

/-- The distinguished nontrivial integral-unit square class at an odd
prime. -/
noncomputable def oddPrimeNonsquareUnitSquareClass
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    padicUnitSquareClassSubgroup p :=
  ⟨padicUnitSquareClassHom p (oddPrimeNonsquarePadicIntUnit p hpodd),
    ⟨oddPrimeNonsquarePadicIntUnit p hpodd, rfl⟩⟩

theorem padicUnitSquareClassHom_oddPrimeNonsquare_ne_one
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    padicUnitSquareClassHom p (oddPrimeNonsquarePadicIntUnit p hpodd) ≠ 1 := by
  intro hone
  have hresidue :=
    (padicUnitSquareClassHom_eq_one_iff_isSquare_toZMod hpodd
      (oddPrimeNonsquarePadicIntUnit p hpodd)).mp hone
  rw [oddPrimeNonsquarePadicIntUnit_toZMod] at hresidue
  exact oddPrimeNonsquareResidueUnit_not_isSquare p hpodd hresidue

/-- Every p-adic integral-unit square class is either trivial or the chosen
nonsquare unit class. -/
theorem padicUnitSquareClassHom_eq_one_or_eq_oddPrimeNonsquare
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) (u : ℤ_[p]ˣ) :
    padicUnitSquareClassHom p u = 1 ∨
      padicUnitSquareClassHom p u =
        padicUnitSquareClassHom p
          (oddPrimeNonsquarePadicIntUnit p hpodd) := by
  let e := oddPrimeNonsquarePadicIntUnit p hpodd
  by_cases hu : IsSquare (PadicInt.toZMod (u : ℤ_[p]))
  · exact Or.inl
      ((padicUnitSquareClassHom_eq_one_iff_isSquare_toZMod hpodd u).2 hu)
  · right
    have he : ¬IsSquare (PadicInt.toZMod (e : ℤ_[p])) := by
      simpa [e] using oddPrimeNonsquareResidueUnit_not_isSquare p hpodd
    have hproductResidue :
        IsSquare (PadicInt.toZMod ((u * e : ℤ_[p]ˣ) : ℤ_[p])) := by
      rw [Units.val_mul, map_mul]
      exact isSquare_mul_of_not_isSquare_of_not_isSquare
        (padicInt_toZMod_ne_zero_of_isUnit (Units.isUnit u))
        (padicInt_toZMod_ne_zero_of_isUnit (Units.isUnit e)) hu he
    have hproduct :
        padicUnitSquareClassHom p (u * e) = 1 :=
      (padicUnitSquareClassHom_eq_one_iff_isSquare_toZMod hpodd (u * e)).2
        hproductResidue
    rw [map_mul] at hproduct
    have heSquare :
        padicUnitSquareClassHom p e * padicUnitSquareClassHom p e = 1 := by
      rw [← map_mul]
      apply
        (padicUnitSquareClassHom_eq_one_iff_isSquare_toZMod hpodd (e * e)).2
      rw [Units.val_mul, map_mul]
      exact ⟨PadicInt.toZMod (e : ℤ_[p]), rfl⟩
    calc
      padicUnitSquareClassHom p u =
          padicUnitSquareClassHom p u * 1 := (mul_one _).symm
      _ = padicUnitSquareClassHom p u *
          (padicUnitSquareClassHom p e * padicUnitSquareClassHom p e) := by
            rw [heSquare]
      _ = (padicUnitSquareClassHom p u * padicUnitSquareClassHom p e) *
          padicUnitSquareClassHom p e := by rw [mul_assoc]
      _ = padicUnitSquareClassHom p e := by rw [hproduct, one_mul]

theorem oddPrimeNonsquareUnitSquareClass_ne_one
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    oddPrimeNonsquareUnitSquareClass p hpodd ≠ 1 := by
  intro h
  apply padicUnitSquareClassHom_oddPrimeNonsquare_ne_one p hpodd
  exact congrArg Subtype.val h

/-- Two-element classification of the integral-unit square-class subgroup at
an odd prime. -/
theorem padicUnitSquareClass_eq_one_or_eq_oddPrimeNonsquare
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (x : padicUnitSquareClassSubgroup p) :
    x = 1 ∨ x = oddPrimeNonsquareUnitSquareClass p hpodd := by
  rcases x.property with ⟨u, hu⟩
  rcases padicUnitSquareClassHom_eq_one_or_eq_oddPrimeNonsquare hpodd u with
    h | h
  · left
    apply Subtype.ext
    rw [← hu]
    exact h
  · right
    apply Subtype.ext
    change x.1 =
      padicUnitSquareClassHom p (oddPrimeNonsquarePadicIntUnit p hpodd)
    rw [← hu]
    exact h

/-- At an odd prime there are exactly two p-adic square classes represented
by integral units. -/
theorem natCard_padicUnitSquareClassSubgroup_eq_two
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    Nat.card (padicUnitSquareClassSubgroup p) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, oddPrimeNonsquareUnitSquareClass p hpodd, ?_, ?_⟩
  · exact (oddPrimeNonsquareUnitSquareClass_ne_one p hpodd).symm
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ,
      iff_true]
    exact padicUnitSquareClass_eq_one_or_eq_oddPrimeNonsquare hpodd x

end Rat
