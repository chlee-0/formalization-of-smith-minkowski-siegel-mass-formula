import SMSFormula.ResidueCharacterDescent

/-!
# The residue map is a ring map

The residue identification for the integral finite adeles is additive, but reducing the values
of a quadratic form needs multiplication.  This file supplies the ring structure -- the reduction
`integralFiniteAdeleSubring ->+* ZMod m` -- so the form's values reduce.

The multiplication lives in the ambient ring, so the congruence is stated there: `x` and `y` are
congruent when their difference is `m` times an integral element.  That relation is closed under
products by the usual two-term split `x y - x' y' = x (y - y') + y' (x - x')`, both differences
carrying the factor `m`, and the bracket staying integral because the ambient multiplication does.

The bridge to the residue map is that congruence is exactly equality of residues -- the additive
equivalence being injective, equal residues give equal classes and a class equality is membership of
the difference in the dilation range.  With the residue of an integer being its own residue class,
every integral element is congruent to an integer, and multiplicativity follows by reducing both
factors to integers.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open SMSFormula.QuadraticPhaseDescent

variable {m : ℕ}

/-! ## Congruence in the ambient ring -/

/-- Congruence MOD `m`, stated in the ambient ring because that is where the multiplication is. -/
def CongrMod (m : ℕ) (x y : RationalFiniteAdele) : Prop :=
  ∃ u : RationalFiniteAdele, u ∈ integralFiniteAdeleSubring ∧
    x - y = (m : RationalFiniteAdele) * u

/-- Congruence is closed under products, by the two-term split.  Integrality of one factor from each
pair is what keeps the bracket integral. -/
theorem CongrMod.mul {x x' y y' : RationalFiniteAdele}
    (hx : CongrMod m x x') (hy : CongrMod m y y')
    (hxmem : x ∈ integralFiniteAdeleSubring) (hy'mem : y' ∈ integralFiniteAdeleSubring) :
    CongrMod m (x * y) (x' * y') := by
  obtain ⟨u, hu, hxu⟩ := hx
  obtain ⟨v, hv, hyv⟩ := hy
  refine ⟨x * v + y' * u, Subring.add_mem _ (Subring.mul_mem _ hxmem hv)
    (Subring.mul_mem _ hy'mem hu), ?_⟩
  have hsplit : x * y - x' * y' = x * (y - y') + y' * (x - x') := by ring
  rw [hsplit, hxu, hyv]
  ring

/-! ## Congruence is equality of residues -/

/-- The residue of an integer is its own residue class. -/
theorem residueOf_integerToIntegralFiniteAdele (hm : m ≠ 0) (z : ℤ) :
    residueOf m hm (integerToIntegralFiniteAdele z) = (z : ZMod m) := by
  have hz : (residueEquivIntegralFiniteAdeleModDilation m hm) ((z : ZMod m)) =
      QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range
        (integerToIntegralFiniteAdele z) :=
    residueToIntegralFiniteAdeleModDilation_intCast m z
  show (residueEquivIntegralFiniteAdeleModDilation m hm).symm
    (QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range
      (integerToIntegralFiniteAdele z)) = _
  rw [← hz, AddEquiv.symm_apply_apply]

/-- Equal residues give a congruence: the additive identification is injective, so equal residues
give equal classes, and a class equality is membership of the difference in the dilation range. -/
theorem congrMod_of_residueOf_eq (hm : m ≠ 0) {r s : IntegralFiniteAdele}
    (h : residueOf m hm r = residueOf m hm s) :
    CongrMod m (r : RationalFiniteAdele) (s : RationalFiniteAdele) := by
  have hmk : (QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range r) =
      QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range s :=
    (residueEquivIntegralFiniteAdeleModDilation m hm).symm.injective h
  obtain ⟨u, hu⟩ : -s + r ∈ (integralFiniteAdeleNatDilation m).range :=
    QuotientAddGroup.eq.mp hmk.symm
  refine ⟨(u : RationalFiniteAdele), u.property, ?_⟩
  have hval := congrArg Subtype.val hu
  simp only [integralFiniteAdeleNatDilation, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddSubgroup.coe_add, AddSubgroup.coe_neg] at hval
  rw [nsmul_eq_mul] at hval
  rw [hval]
  ring

/-- And the converse, which is what multiplicativity consumes. -/
theorem residueOf_eq_of_congrMod (hm : m ≠ 0) {r s : IntegralFiniteAdele}
    (h : CongrMod m (r : RationalFiniteAdele) (s : RationalFiniteAdele)) :
    residueOf m hm r = residueOf m hm s := by
  obtain ⟨u, hu, huval⟩ := h
  have hmem : r - s ∈ (integralFiniteAdeleNatDilation m).range := by
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    show (m • u) = _
    rw [nsmul_eq_mul]
    exact huval.symm
  have hzero : residueOf m hm (r - s) = 0 := by
    show (residueEquivIntegralFiniteAdeleModDilation m hm).symm
      (QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range (r - s)) = 0
    rw [show QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range (r - s) = 0 from
      (QuotientAddGroup.eq_zero_iff _).2 hmem]
    exact map_zero _
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- And every integral element is congruent to an integer. -/
theorem exists_int_congrMod (hm : m ≠ 0) (r : IntegralFiniteAdele) :
    ∃ z : ℤ, CongrMod m (r : RationalFiniteAdele)
      ((integerToIntegralFiniteAdele z : IntegralFiniteAdele) : RationalFiniteAdele) ∧
      residueOf m hm r = (z : ZMod m) := by
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (residueOf m hm r)
  refine ⟨z, congrMod_of_residueOf_eq hm ?_, hz.symm⟩
  rw [residueOf_integerToIntegralFiniteAdele hm z]
  exact hz.symm

/-! ## The ring reduction -/

/-- The integral subring's elements as additive ones -- the same carrier, so no content. -/
def toIntegral (x : integralFiniteAdeleSubring) : IntegralFiniteAdele := ⟨x.1, x.2⟩

/-- The residue map as a ring map.  Additivity is the repository's; multiplicativity is proved by
reducing both factors to integers and using that congruence is closed under products. -/
noncomputable def ringResidueOf (m : ℕ) (hm : m ≠ 0) :
    integralFiniteAdeleSubring →+* ZMod m where
  toFun x := residueOf m hm (toIntegral x)
  map_zero' := map_zero _
  map_add' x y := map_add _ _ _
  map_one' := by
    have h1 : toIntegral (1 : integralFiniteAdeleSubring) =
        integerToIntegralFiniteAdele 1 := by
      apply Subtype.ext
      show (1 : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele (((1 : ℤ)) : ℚ)
      simp
    show residueOf m hm (toIntegral 1) = 1
    rw [h1, residueOf_integerToIntegralFiniteAdele hm]
    simp
  map_mul' x y := by
    obtain ⟨a, hax, har⟩ := exists_int_congrMod hm (toIntegral x)
    obtain ⟨b, hby, hbr⟩ := exists_int_congrMod hm (toIntegral y)
    have hmul := CongrMod.mul hax hby x.property
      (integerToIntegralFiniteAdele b).property
    have hab : ((integerToIntegralFiniteAdele a : IntegralFiniteAdele) :
          RationalFiniteAdele) *
        ((integerToIntegralFiniteAdele b : IntegralFiniteAdele) : RationalFiniteAdele) =
        ((integerToIntegralFiniteAdele (a * b) : IntegralFiniteAdele) :
          RationalFiniteAdele) := by
      show algebraMap ℚ RationalFiniteAdele ((a : ℤ) : ℚ) *
        algebraMap ℚ RationalFiniteAdele ((b : ℤ) : ℚ) =
        algebraMap ℚ RationalFiniteAdele (((a * b : ℤ)) : ℚ)
      rw [← map_mul]
      push_cast
      ring_nf
    rw [hab] at hmul
    have hres : residueOf m hm (toIntegral (x * y)) =
        residueOf m hm (integerToIntegralFiniteAdele (a * b)) :=
      residueOf_eq_of_congrMod hm hmul
    show residueOf m hm (toIntegral (x * y)) =
      residueOf m hm (toIntegral x) * residueOf m hm (toIntegral y)
    rw [hres, residueOf_integerToIntegralFiniteAdele hm, har, hbr]
    push_cast
    ring

@[simp]
theorem ringResidueOf_apply (hm : m ≠ 0) (x : integralFiniteAdeleSubring) :
    ringResidueOf m hm x = residueOf m hm (toIntegral x) := rfl

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
