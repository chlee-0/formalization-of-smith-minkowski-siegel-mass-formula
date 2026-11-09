import SMSFormula.RationalAdeleArchimedeanAdditiveCharacter

/-!
# The rational classes inside the finite-adelic integral quotient

This file treats the algebraic strong-approximation step needed for the
finite part of the rational-adelic Fourier character.  It constructs the
canonical additive map

`ℚ / ℤ → 𝔸_ℚ,f / Ẑ`

on the restricted-product finite-adele carrier and proves
that it is injective.  Surjectivity is not asserted here: it is
exactly the finite strong-approximation theorem.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The additive subgroup of rational integers inside `ℚ`. -/
def rationalIntegerAddSubgroup : AddSubgroup ℚ :=
  (algebraMap ℤ ℚ).range.toAddSubgroup

/-- The additive quotient `ℚ / ℤ`, without topology. -/
abbrev RationalModInteger := ℚ ⧸ rationalIntegerAddSubgroup

/-- The additive subgroup of finite adeles integral at every finite place. -/
def integralFiniteAdeleAddSubgroup : AddSubgroup RationalFiniteAdele :=
  integralFiniteAdeleSubring.toAddSubgroup

/-- The additive quotient of the actual rational finite adeles by the
everywhere-integral finite adeles. -/
abbrev RationalFiniteAdeleModIntegral :=
  RationalFiniteAdele ⧸ integralFiniteAdeleAddSubgroup

/-- The rational diagonal induces an additive map from `ℚ / ℤ` to the finite
adelic quotient by the everywhere-integral subgroup. -/
noncomputable def rationalModIntegerToFiniteAdeleModIntegral :
    RationalModInteger →+ RationalFiniteAdeleModIntegral :=
  QuotientAddGroup.map rationalIntegerAddSubgroup
    integralFiniteAdeleAddSubgroup
    (algebraMap ℚ RationalFiniteAdele).toAddMonoidHom (by
      intro q hq
      exact (rational_mem_integralFiniteAdeleSubring_iff q).2 hq)

@[simp]
theorem rationalModIntegerToFiniteAdeleModIntegral_mk (q : ℚ) :
    rationalModIntegerToFiniteAdeleModIntegral
        (QuotientAddGroup.mk' rationalIntegerAddSubgroup q) =
      QuotientAddGroup.mk' integralFiniteAdeleAddSubgroup
        (algebraMap ℚ RationalFiniteAdele q) :=
  rfl

/-- The rational diagonal has no extra kernel after passage to the two
integral quotients.  This is the exact injective half of
`ℚ / ℤ ≃ 𝔸_ℚ,f / Ẑ`. -/
theorem rationalModIntegerToFiniteAdeleModIntegral_injective :
    Function.Injective rationalModIntegerToFiniteAdeleModIntegral := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h q =>
      induction y using Quotient.inductionOn with
      | h r =>
          apply QuotientAddGroup.eq.mpr
          have htarget :
              -(algebraMap ℚ RationalFiniteAdele q) +
                  algebraMap ℚ RationalFiniteAdele r ∈
                integralFiniteAdeleAddSubgroup := by
            exact QuotientAddGroup.eq.mp hxy
          have hdiag :
              algebraMap ℚ RationalFiniteAdele (-q + r) ∈
                integralFiniteAdeleSubring := by
            simpa only [map_add, map_neg] using htarget
          exact
            (rational_mem_integralFiniteAdeleSubring_iff (-q + r)).mp hdiag

/-- Surjectivity of the canonical quotient map is literally the concrete
finite strong-approximation statement: every finite adele differs from one
rational diagonal point by an everywhere-integral finite adele. -/
theorem rationalModIntegerToFiniteAdeleModIntegral_surjective_iff :
    Function.Surjective rationalModIntegerToFiniteAdeleModIntegral ↔
      ∀ a : RationalFiniteAdele, ∃ q : ℚ,
        a - algebraMap ℚ RationalFiniteAdele q ∈
          integralFiniteAdeleSubring := by
  constructor
  · intro hsurj a
    obtain ⟨x, hx⟩ := hsurj
      (QuotientAddGroup.mk' integralFiniteAdeleAddSubgroup a)
    induction x using Quotient.inductionOn with
    | h q =>
        refine ⟨q, ?_⟩
        have hmem :
            -(algebraMap ℚ RationalFiniteAdele q) + a ∈
              integralFiniteAdeleAddSubgroup := by
          exact QuotientAddGroup.eq.mp hx
        simpa only [sub_eq_add_neg, add_comm] using hmem
  · intro happ x
    induction x using Quotient.inductionOn with
    | h a =>
        obtain ⟨q, hq⟩ := happ a
        refine
          ⟨QuotientAddGroup.mk' rationalIntegerAddSubgroup q, ?_⟩
        apply QuotientAddGroup.eq.mpr
        simpa only [sub_eq_add_neg, add_comm] using hq

end PositiveDefiniteIntegralLattice
