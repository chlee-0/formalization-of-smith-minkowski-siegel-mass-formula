import SMSFormula.LevelQuotientResidueEquiv

/-!
# The frequency character is a character of `ZMod m`

The level quotient is the residue vectors, so what remains before
`FiniteQuadraticSumModulusBound` applies is that the summand be the affine quadratic phase in the
residues.  That splits into a character half and a matrix half; this file closes the character half.

The conductor condition is exactly what descends the character.  On the integral finite adeles the
frequency-scaled character `r |-> psi (t * r)` is an additive character, and when `t * m` is integral
it kills the `m`-dilation range -- the same computation as the level condition, in one variable
rather than through the polarization.  So it descends to the quotient, and the repository's own
`residueEquivIntegralFiniteAdeleModDilation` carries that to an additive character of `ZMod m`.

The compatibility is the usable form: the frequency phase at an integral element is that character
of `ZMod m` evaluated at the element's residue, the residue map being the repository's identification
composed with the projection -- no representative chosen.

Negative scope, and it names the remaining half.  The repository's identification is additive.  A
quadratic form needs multiplication, so writing `Q_C(x) mod m` as a `ZMod m`-quadratic form in the
residues needs the reduction to be a ring map, which is not supplied here.  Nothing reduces the
matrix and no Gauss sum is evaluated.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory SMSFormula.QuadraticPhaseDescent

/-! ## The frequency-scaled character on the integral finite adeles -/

/-- The frequency-scaled character, on the integral finite adeles. -/
noncomputable def scaledIntegralChar (t : RationalFiniteAdele) :
    AddChar IntegralFiniteAdele ℂ where
  toFun r := complexFiniteChar (t * (r : RationalFiniteAdele))
  map_zero_eq_one' := by
    show complexFiniteChar (t * ((0 : IntegralFiniteAdele) : RationalFiniteAdele)) = 1
    rw [AddSubgroup.coe_zero, mul_zero]
    exact AddChar.map_zero_eq_one _
  map_add_eq_mul' r s := by
    show complexFiniteChar (t * ((r + s : IntegralFiniteAdele) : RationalFiniteAdele)) = _
    rw [AddSubgroup.coe_add, mul_add]
    exact AddChar.map_add_eq_mul _ _ _

@[simp]
theorem scaledIntegralChar_apply (t : RationalFiniteAdele) (r : IntegralFiniteAdele) :
    scaledIntegralChar t r = complexFiniteChar (t * (r : RationalFiniteAdele)) := rfl

/-- The conductor condition kills the dilation range: at `t * m` integral, the scaled character is
one on every `m`-multiple.  This is the level condition in one variable. -/
theorem scaledIntegralChar_eq_one_of_mem_range (m : ℕ) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    {r : IntegralFiniteAdele} (hr : r ∈ (integralFiniteAdeleNatDilation m).range) :
    scaledIntegralChar t r = 1 := by
  obtain ⟨u, rfl⟩ := hr
  have hval : ((integralFiniteAdeleNatDilation m u : IntegralFiniteAdele) :
      RationalFiniteAdele) = (m : RationalFiniteAdele) * (u : RationalFiniteAdele) := by
    show (m • (u : RationalFiniteAdele)) = _
    rw [nsmul_eq_mul]
  rw [scaledIntegralChar_apply, hval, ← mul_assoc]
  exact complexFiniteChar_eq_one_of_mem_integral (Subring.mul_mem _ htm u.property)

/-! ## The descent to `ZMod m` -/

/-- The kernel condition, named so the descent and its compatibility both use the same proof. -/
theorem scaledIntegralChar_le_ker (m : ℕ) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    (integralFiniteAdeleNatDilation m).range ≤
      (AddChar.toAddMonoidHomEquiv (scaledIntegralChar t)).ker := by
  intro r hr
  exact congrArg Additive.ofMul (scaledIntegralChar_eq_one_of_mem_range m htm hr)

/-- The character on the one-coordinate quotient. -/
noncomputable def quotientScaledChar (m : ℕ) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    AddChar (IntegralFiniteAdele ⧸ (integralFiniteAdeleNatDilation m).range) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (integralFiniteAdeleNatDilation m).range
      (AddChar.toAddMonoidHomEquiv (scaledIntegralChar t))
      (scaledIntegralChar_le_ker m htm))

@[simp]
theorem quotientScaledChar_mk (m : ℕ) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) (r : IntegralFiniteAdele) :
    quotientScaledChar m htm (QuotientAddGroup.mk' _ r) =
      complexFiniteChar (t * (r : RationalFiniteAdele)) := rfl

/-- The residue map: the repository's own identification composed with the projection.  It is
additive, and no representative is chosen. -/
noncomputable def residueOf (m : ℕ) (hm : m ≠ 0) : IntegralFiniteAdele →+ ZMod m :=
  (residueEquivIntegralFiniteAdeleModDilation m hm).symm.toAddMonoidHom.comp
    (QuotientAddGroup.mk' (integralFiniteAdeleNatDilation m).range)

/-- The frequency character as a character of `ZMod m`. -/
noncomputable def residueChar (m : ℕ) (hm : m ≠ 0) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) : AddChar (ZMod m) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    ((AddChar.toAddMonoidHomEquiv (quotientScaledChar m htm)).comp
      (residueEquivIntegralFiniteAdeleModDilation m hm).toAddMonoidHom)

@[simp]
theorem residueChar_apply (m : ℕ) (hm : m ≠ 0) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) (z : ZMod m) :
    residueChar m hm htm z =
      quotientScaledChar m htm (residueEquivIntegralFiniteAdeleModDilation m hm z) := rfl

/-- The compatibility, and it is the usable form: the frequency phase at an integral element is the
`ZMod m` character at that element's residue. -/
@[simp]
theorem residueChar_residueOf (m : ℕ) (hm : m ≠ 0) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) (r : IntegralFiniteAdele) :
    residueChar m hm htm (residueOf m hm r) =
      complexFiniteChar (t * (r : RationalFiniteAdele)) := by
  rw [residueChar_apply, show (residueEquivIntegralFiniteAdeleModDilation m hm)
    (residueOf m hm r) = QuotientAddGroup.mk' _ r from
      (residueEquivIntegralFiniteAdeleModDilation m hm).apply_symm_apply _]
  exact quotientScaledChar_mk m htm r

/-- At the zero residue it is one, so the identification agrees with the character's own
normalization. -/
@[simp]
theorem residueChar_zero (m : ℕ) (hm : m ≠ 0) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    residueChar m hm htm 0 = 1 := AddChar.map_zero_eq_one _

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
