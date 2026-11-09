import SMSFormula.BinaryLocalClass
import SMSFormula.RationalDyadicSquareClass

/-!
# Finite residue models for the actual local order-unit norm quotients

Scalar squares belong to the original order-unit norm subgroup. Native
square lifting therefore puts the kernel of residue reduction inside that
subgroup: modulo p at odd primes, and modulo eight at two.
-/

noncomputable section

namespace BinaryNormIdeal

/-- The residue depth needed for scalar square lifting. -/
def normResidueModulus (p : ℕ) : ℕ := if p=2 then 8 else p

instance normResidueModulus_neZero (p : ℕ) [Fact p.Prime] :
    NeZero (normResidueModulus p) := by
  by_cases hp : p=2
  · exact ⟨by simp [normResidueModulus,hp]⟩
  · exact ⟨by simpa [normResidueModulus,hp] using (Fact.out : p.Prime).ne_zero⟩

/-- The literal scalar residue ring map. -/
def normResidueHom (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* ZMod (normResidueModulus p) :=
  if hp : p=2 then by
    subst p
    exact PadicInt.toZModPow 3
  else
    (ZMod.ringEquivCongr (show normResidueModulus p=p from if_neg hp)).symm.toRingHom.comp
      (PadicInt.toZMod (p := p))

def normResidueUnits (p : ℕ) [Fact p.Prime] :
    ℤ_[p]ˣ →* (ZMod (normResidueModulus p))ˣ :=
  Units.map (normResidueHom p).toMonoidHom

/-- Any residue-unit has an actual p-adic unit lift. -/
theorem normResidueUnits_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (normResidueUnits p) := by
  intro u
  let a := u.val.val
  have ha : (a : ZMod (normResidueModulus p))=u.val := ZMod.natCast_zmod_val _
  have hc : a.Coprime (normResidueModulus p) := by
    rw [← ZMod.isUnit_iff_coprime,ha]
    exact u.isUnit
  have hpm : p ∣ normResidueModulus p := by
    by_cases hp : p=2 <;> simp [normResidueModulus,hp]
  have hn : (a : ZMod p) ≠ 0 := by
    intro hz
    have hpa := (ZMod.natCast_eq_zero_iff a p).mp hz
    have h := Nat.dvd_gcd hpa hpm
    rw [hc.gcd_eq_one] at h
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)
  have hu : IsUnit (a : ℤ_[p]) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    intro h
    apply hn
    calc
      (a : ZMod p)=PadicInt.toZMod (a : ℤ_[p]) := (map_natCast _ a).symm
      _=0 := by
        change PadicInt.residueField (IsLocalRing.residue ℤ_[p] (a : ℤ_[p]))=0
        rw [h,map_zero]
  refine ⟨hu.unit,?_⟩
  apply Units.ext
  change normResidueHom p (hu.unit : ℤ_[p])=u.val
  rw [hu.unit_spec,map_natCast,ha]

/-- A unit with residue one is an actual integral square, including at two. -/
theorem isSquare_of_normResidueUnits_eq_one (p : ℕ) [Fact p.Prime]
    (u : ℤ_[p]ˣ) (hu : normResidueUnits p u=1) : IsSquare (u : ℤ_[p]) := by
  have h := congrArg Units.val hu
  change normResidueHom p (u : ℤ_[p])=1 at h
  by_cases hp : p=2
  · subst p
    have hr : PadicInt.toZModPow 3 (u : ℤ_[2])=1 := by
      simpa [normResidueHom] using h
    exact (PadicInt.isSquare_coe_iff_isSquare_of_isUnit u.isUnit).mp
      ((PadicInt.isSquare_coe_iff_toZModPow_three_eq_one_of_isUnit u.isUnit).mpr hr)
  · have hm : normResidueModulus p=p := if_neg hp
    have hr : PadicInt.toZMod (u : ℤ_[p])=1 := by
      apply (ZMod.ringEquivCongr hm).symm.injective
      simpa only [normResidueHom, dif_neg hp, RingHom.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_one] using h
    apply (PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hp u.isUnit).mpr
    rw [hr]
    exact ⟨1,by simp⟩

/-- Integral scalar squares are norms of actual original-order units. -/
theorem mem_orderUnitNormSubgroup_of_isSquare (R : Type*) [CommRing R]
    (D : ℤ) (u : Rˣ) (hu : IsSquare (u : R)) : u ∈ orderUnitNormSubgroup R D := by
  obtain ⟨x,hx⟩ := hu
  have hxunit : IsUnit x := by
    exact isUnit_of_mul_isUnit_left (show IsUnit (x*x) by rw [← hx]; exact u.isUnit)
  have he : u=hxunit.unit*hxunit.unit := by
    apply Units.ext
    simpa only [Units.val_mul,hxunit.unit_spec] using hx
  rw [he]
  have h := orderUnitNormQuotientMap_sq R D hxunit.unit
  exact (QuotientGroup.eq_one_iff _).mp h

/-- The residue kernel is contained in the original norm subgroup. -/
theorem normResidueUnits_ker_le (p : ℕ) [Fact p.Prime] (D : ℤ) :
    (normResidueUnits p).ker ≤ orderUnitNormSubgroup ℤ_[p] D := by
  intro u hu
  exact mem_orderUnitNormSubgroup_of_isSquare ℤ_[p] D u
    (isSquare_of_normResidueUnits_eq_one p u hu)

/-- The image of the original local order-unit norms in finite residue units. -/
def residueOrderUnitNormSubgroup (p : ℕ) [Fact p.Prime] (D : ℤ) :
    Subgroup (ZMod (normResidueModulus p))ˣ :=
  (orderUnitNormSubgroup ℤ_[p] D).map (normResidueUnits p)

/-- Exact descent of the actual norm quotient to a finite residue quotient. -/
def orderUnitNormQuotientEquivResidue (p : ℕ) [Fact p.Prime] (D : ℤ) :
    OrderUnitNormQuotient ℤ_[p] D ≃*
      ((ZMod (normResidueModulus p))ˣ ⧸ residueOrderUnitNormSubgroup p D) := by
  let f := (QuotientGroup.mk' (residueOrderUnitNormSubgroup p D)).comp (normResidueUnits p)
  apply QuotientGroup.liftEquiv (φ := f) (orderUnitNormSubgroup ℤ_[p] D)
    ((QuotientGroup.mk'_surjective _).comp (normResidueUnits_surjective p))
  dsimp only [f]
  rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
  exact (Subgroup.comap_map_eq_self (normResidueUnits_ker_le p D)).symm

/-- Finiteness is on the literal original-order local norm quotient. -/
theorem finite_orderUnitNormQuotient (p : ℕ) [Fact p.Prime] (D : ℤ) :
    Finite (OrderUnitNormQuotient ℤ_[p] D) :=
  Finite.of_equiv _ (orderUnitNormQuotientEquivResidue p D).symm.toEquiv

theorem card_orderUnitNormQuotient_pos (p : ℕ) [Fact p.Prime] (D : ℤ) :
    0<Nat.card (OrderUnitNormQuotient ℤ_[p] D) := by
  letI := finite_orderUnitNormQuotient p D
  exact Nat.card_pos

theorem card_orderUnitNormQuotient_eq_residue (p : ℕ) [Fact p.Prime] (D : ℤ) :
    Nat.card (OrderUnitNormQuotient ℤ_[p] D)=
      Nat.card ((ZMod (normResidueModulus p))ˣ ⧸ residueOrderUnitNormSubgroup p D) :=
  Nat.card_congr (orderUnitNormQuotientEquivResidue p D).toEquiv

/-- The dyadic quotient has at most four classes before any order
classification or finite norm-image evaluation. -/
theorem card_orderUnitNormQuotient_two_le_four (D : ℤ) :
    Nat.card (OrderUnitNormQuotient ℤ_[2] D) ≤ 4 := by
  rw [card_orderUnitNormQuotient_eq_residue]
  have h := Nat.card_le_card_of_surjective
    (QuotientGroup.mk' (residueOrderUnitNormSubgroup 2 D)) (QuotientGroup.mk'_surjective _)
  have hc : Nat.card (ZMod (normResidueModulus 2))ˣ=4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa only [hc] using h

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.normResidueModulus
#assert_standard_axioms BinaryNormIdeal.normResidueModulus_neZero
#assert_standard_axioms BinaryNormIdeal.normResidueHom
#assert_standard_axioms BinaryNormIdeal.normResidueUnits
#assert_standard_axioms BinaryNormIdeal.normResidueUnits_surjective
#assert_standard_axioms BinaryNormIdeal.isSquare_of_normResidueUnits_eq_one
#assert_standard_axioms BinaryNormIdeal.mem_orderUnitNormSubgroup_of_isSquare
#assert_standard_axioms BinaryNormIdeal.normResidueUnits_ker_le
#assert_standard_axioms BinaryNormIdeal.residueOrderUnitNormSubgroup
#assert_standard_axioms BinaryNormIdeal.orderUnitNormQuotientEquivResidue
#assert_standard_axioms BinaryNormIdeal.finite_orderUnitNormQuotient
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNormQuotient_pos
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNormQuotient_eq_residue
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNormQuotient_two_le_four
