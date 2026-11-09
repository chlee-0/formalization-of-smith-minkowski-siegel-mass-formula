import SMSFormula.RationalSquareClassLocalGlobal
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.ZMod
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# The order-two character coefficient in the relative Tamagawa formula

For the central kernel `mu_2`, Ono's character module `X*(mu_2)` is the
constant order-two Galois module. This module installs its explicit coefficient
model `ZMod 2`, proves that the fixed part and abstract degree-zero cohomology
both have cardinality two, and isolates the continuity condition in degree one.

Mathlib's low-degree `groupCohomology.H1` is abstract group cohomology. For a
trivial action it is the group of all homomorphisms from the absolute Galois
group. Ono uses continuous cohomology. We therefore define the exact
trivial-action continuous degree-one model as continuous homomorphisms into
the finite discrete coefficient and prove that forgetting continuity embeds it
in mathlib's abstract `H1`.

This file does not construct the algebraic-group character functor of `mu_2`,
the Kummer equivalence with square classes, or global-to-local absolute Galois
restriction maps. Those are handled in separate modules.
-/

noncomputable section

namespace RationalTamagawa

/-- The standard explicit model of the character module `X*(mu_2)`. -/
abbrev MuTwoCharacterModule := ZMod 2

/-- The constant order-two representation of the absolute Galois group of a
field. The type-universe restriction matches mathlib's current `Rep` API and
covers `Q`, `R`, and all `Q_p` used here. -/
abbrev muTwoCharacterRepresentation (K : Type) [Field K] :
    Rep ℤ (Field.absoluteGaloisGroup K) :=
  Rep.trivial ℤ (Field.absoluteGaloisGroup K) MuTwoCharacterModule

/-- The fixed part of the order-two character representation. -/
abbrev MuTwoCharacterFixedPart (K : Type) [Field K] :=
  (muTwoCharacterRepresentation K).ρ.invariants

/-- Abstract degree-zero group cohomology of the order-two character
representation. -/
abbrev MuTwoCharacterH0 (K : Type) [Field K] :=
  groupCohomology.H0 (muTwoCharacterRepresentation K)

@[simp]
theorem muTwoCharacterRepresentation_apply
    (K : Type) [Field K]
    (σ : Field.absoluteGaloisGroup K) (x : MuTwoCharacterModule) :
    (muTwoCharacterRepresentation K).ρ σ x = x := by
  rfl

/-- The character coefficient itself has order two. -/
theorem natCard_muTwoCharacterModule_eq_two :
    Nat.card MuTwoCharacterModule = 2 :=
  Nat.card_zmod 2

/-- The absolute Galois action fixes the entire character module. -/
theorem muTwoCharacterFixedPart_eq_top (K : Type) [Field K] :
    (muTwoCharacterRepresentation K).ρ.invariants = ⊤ :=
  Representation.invariants_eq_top _

/-- Ono's numerator `h^0(X*(mu_2))` is two in the explicit constant-module
model. -/
theorem natCard_muTwoCharacterFixedPart_eq_two
    (K : Type) [Field K] :
    Nat.card (MuTwoCharacterFixedPart K) = 2 := by
  change Nat.card ↑((muTwoCharacterRepresentation K).ρ.invariants) = 2
  rw [muTwoCharacterFixedPart_eq_top]
  simp

/-- The same cardinality calculation through mathlib's abstract `H0`. -/
theorem natCard_muTwoCharacterH0_eq_two
    (K : Type) [Field K] :
    Nat.card (MuTwoCharacterH0 K) = 2 := by
  let e := groupCohomology.H0IsoOfIsTrivial
    (muTwoCharacterRepresentation K)
  rw [Nat.card_congr (Equiv.ofBijective e.hom
    (CategoryTheory.ConcreteCategory.bijective_of_isIso e.hom))]
  exact Nat.card_zmod 2

/-- The exact continuous `H1` model for the trivial order-two action:
continuous additive homomorphisms from the additive-tagged absolute Galois
group to `ZMod 2`. -/
abbrev MuTwoContinuousH1 (K : Type) [Field K] :=
  ContinuousAddMonoidHom
    (Additive (Field.absoluteGaloisGroup K)) MuTwoCharacterModule

/-- Mathlib's abstract `H1` of the trivial order-two representation is the
group of all, not necessarily continuous, homomorphisms. -/
noncomputable def muTwoAbstractH1Equiv
    (K : Type) [Field K] :
    groupCohomology.H1 (muTwoCharacterRepresentation K) ≃+
      (Additive (Field.absoluteGaloisGroup K) →+ MuTwoCharacterModule) := by
  let e := groupCohomology.H1IsoOfIsTrivial
    (muTwoCharacterRepresentation K)
  exact (LinearEquiv.ofBijective e.hom.hom
    (CategoryTheory.ConcreteCategory.bijective_of_isIso e.hom)).toAddEquiv

/-- Forget continuity and regard a continuous order-two Galois character as
an abstract degree-one cohomology class. -/
noncomputable def muTwoContinuousH1ToAbstractH1
    (K : Type) [Field K] :
    MuTwoContinuousH1 K →+
      groupCohomology.H1 (muTwoCharacterRepresentation K) where
  toFun f := (groupCohomology.H1IsoOfIsTrivial
    (muTwoCharacterRepresentation K)).inv f.toAddMonoidHom
  map_zero' := by
    have hzero : (0 : MuTwoContinuousH1 K).toAddMonoidHom = 0 := rfl
    rw [hzero, map_zero]
  map_add' f g := by
    have hadd : (f + g).toAddMonoidHom =
        f.toAddMonoidHom + g.toAddMonoidHom := rfl
    rw [hadd, map_add]

@[simp]
theorem muTwoContinuousH1ToAbstractH1_apply
    (K : Type) [Field K] (f : MuTwoContinuousH1 K) :
    muTwoContinuousH1ToAbstractH1 K f =
      (groupCohomology.H1IsoOfIsTrivial
        (muTwoCharacterRepresentation K)).inv f.toAddMonoidHom :=
  rfl

/-- Forgetting continuity loses no continuous character. -/
theorem muTwoContinuousH1ToAbstractH1_injective
    (K : Type) [Field K] :
    Function.Injective (muTwoContinuousH1ToAbstractH1 K) := by
  intro f g hfg
  apply ContinuousAddMonoidHom.ext
  intro x
  have h : f.toAddMonoidHom = g.toAddMonoidHom := by
    simpa [muTwoContinuousH1ToAbstractH1] using congrArg
      (groupCohomology.H1IsoOfIsTrivial
        (muTwoCharacterRepresentation K)).hom hfg
  exact DFunLike.congr_fun h x

/-- The global continuous order-two character group over `Q`. -/
abbrev RationalMuTwoContinuousH1 := MuTwoContinuousH1 ℚ

/-- The archimedean local continuous order-two character group. -/
abbrev RealMuTwoContinuousH1 := MuTwoContinuousH1 ℝ

/-- The `p`-adic local continuous order-two character group. -/
abbrev PadicMuTwoContinuousH1 (p : ℕ) [Fact p.Prime] :=
  MuTwoContinuousH1 ℚ_[p]

end RationalTamagawa
