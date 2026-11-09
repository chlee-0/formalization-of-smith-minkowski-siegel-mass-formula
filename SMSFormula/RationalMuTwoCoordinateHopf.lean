import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The affine Hopf-algebra precursor for rational mu-two

The additive group algebra `ℚ[ZMod 2]` is the coordinate Hopf algebra of
`mu_2`. This file constructs its functor of points explicitly. Evaluation at
the nonzero element of `ZMod 2` gives a natural equivalence

```text
Hom_Alg(ℚ[ZMod 2], K) ~= rootsOfUnity 2 K.
```

The same equivalence is also stated for morphisms of affine schemes over
`Spec ℚ`. Finally, the group-like elements of the coordinate Hopf algebra
are computed: they are exactly the two monomials indexed by `ZMod 2`.
This is the specialized character-group calculation needed for Ono's
relative factor.

Mathlib currently has no automatic construction sending a commutative Hopf
algebra to a group object over `Spec ℚ`, and no algebraic-group character
functor. Thus this file supplies the coordinate Hopf algebra, its relative
scheme points, and its intrinsic group-like character group. The subsequent
`RationalMuTwoGroupScheme` module bundles the affine scheme indirectly via
representability of its roots-of-unity functor.
-/

noncomputable section

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

namespace RationalTamagawa

abbrev RationalMuTwoCoordinateRing := AddMonoidAlgebra ℚ (ZMod 2)

abbrev RationalMuTwoPoint (K : Type*) [CommRing K] [Algebra ℚ K] :=
  RationalMuTwoCoordinateRing →ₐ[ℚ] K

def integerZpowAddHom {K : Type*} [CommGroup K] (z : K) :
    ℤ →+ Additive K where
  toFun m := Additive.ofMul (z ^ m)
  map_zero' := by simp
  map_add' m n := by simp [zpow_add]

def muTwoCyclicUnitsHom {K : Type*} [CommMonoid K]
    (z : rootsOfUnity 2 K) : Multiplicative (ZMod 2) →* Kˣ := by
  let fz : ZMod 2 →+ Additive Kˣ :=
    ZMod.lift 2 ⟨integerZpowAddHom (z : Kˣ), by
      change Additive.ofMul ((z : Kˣ) ^ (2 : ℤ)) = 0
      rw [show (2 : ℤ) = (2 : ℕ) by norm_num, zpow_natCast]
      exact congrArg Additive.ofMul z.property⟩
  exact
    { toFun := fun a => (fz a.toAdd).toMul
      map_one' := congrArg Additive.toMul fz.map_zero
      map_mul' := fun a b => congrArg Additive.toMul (fz.map_add a.toAdd b.toAdd) }

@[simp]
theorem muTwoCyclicUnitsHom_one {K : Type*} [CommMonoid K]
    (z : rootsOfUnity 2 K) :
    muTwoCyclicUnitsHom z (Multiplicative.ofAdd (1 : ZMod 2)) = (z : Kˣ) := by
  change ((ZMod.lift 2 _ (1 : ZMod 2) : Additive Kˣ).toMul) = _
  rw [show (1 : ZMod 2) = (1 : ℤ) by norm_num, ZMod.lift_coe]
  simp [integerZpowAddHom]

def muTwoCyclicHom {K : Type*} [CommRing K]
    (z : rootsOfUnity 2 K) : Multiplicative (ZMod 2) →* K :=
  (Units.coeHom K).comp (muTwoCyclicUnitsHom z)

@[simp]
theorem muTwoCyclicHom_one {K : Type*} [CommRing K]
    (z : rootsOfUnity 2 K) :
    muTwoCyclicHom z (Multiplicative.ofAdd (1 : ZMod 2)) = ((z : Kˣ) : K) := by
  simp [muTwoCyclicHom]

def muTwoPointOfRoot {K : Type*} [CommRing K] [Algebra ℚ K]
    (z : rootsOfUnity 2 K) : RationalMuTwoPoint K :=
  AddMonoidAlgebra.lift ℚ K (ZMod 2) (muTwoCyclicHom z)

@[simp]
theorem muTwoPointOfRoot_generator {K : Type*} [CommRing K] [Algebra ℚ K]
    (z : rootsOfUnity 2 K) :
    muTwoPointOfRoot z (AddMonoidAlgebra.single (1 : ZMod 2) 1) =
      ((z : Kˣ) : K) := by
  rw [muTwoPointOfRoot, AddMonoidAlgebra.lift_single]
  simp

def muTwoRootOfPoint {K : Type*} [CommRing K] [Algebra ℚ K]
    (F : RationalMuTwoPoint K) : rootsOfUnity 2 K :=
  rootsOfUnity.mkOfPowEq
    (F (AddMonoidAlgebra.single (1 : ZMod 2) 1)) (by
      rw [← map_pow]
      rw [pow_two, AddMonoidAlgebra.single_mul_single]
      simp only [one_mul]
      rw [show (1 + 1 : ZMod 2) = 0 by decide]
      rw [← AddMonoidAlgebra.one_def]
      exact map_one F)

@[simp]
theorem muTwoRootOfPoint_coe {K : Type*} [CommRing K] [Algebra ℚ K]
    (F : RationalMuTwoPoint K) :
    (((muTwoRootOfPoint F : rootsOfUnity 2 K) : Kˣ) : K) =
      F (AddMonoidAlgebra.single (1 : ZMod 2) 1) :=
  rfl

theorem muTwoRootOfPoint_muTwoPointOfRoot {K : Type*}
    [CommRing K] [Algebra ℚ K] (z : rootsOfUnity 2 K) :
    muTwoRootOfPoint (muTwoPointOfRoot z) = z := by
  apply rootsOfUnity.coe_injective
  exact muTwoPointOfRoot_generator z

set_option backward.isDefEq.respectTransparency false in
theorem muTwoPointOfRoot_muTwoRootOfPoint {K : Type*}
    [CommRing K] [Algebra ℚ K] (F : RationalMuTwoPoint K) :
    muTwoPointOfRoot (muTwoRootOfPoint F) = F := by
  apply AddMonoidAlgebra.algHom_ext'
  ext g
  fin_cases g
  · simp [muTwoPointOfRoot, muTwoCyclicHom]
    rw [← AddMonoidAlgebra.one_def, map_one]
  · simp [muTwoPointOfRoot, muTwoCyclicHom]

def muTwoPointEquivRootsOfUnity {K : Type*} [CommRing K] [Algebra ℚ K] :
    RationalMuTwoPoint K ≃ rootsOfUnity 2 K where
  toFun := muTwoRootOfPoint
  invFun := muTwoPointOfRoot
  left_inv := muTwoPointOfRoot_muTwoRootOfPoint
  right_inv := muTwoRootOfPoint_muTwoPointOfRoot

def muTwoPointMap {K L : Type*} [CommRing K] [CommRing L]
    [Algebra ℚ K] [Algebra ℚ L] (σ : K →ₐ[ℚ] L) :
    RationalMuTwoPoint K → RationalMuTwoPoint L :=
  fun F => σ.comp F

@[simp]
theorem muTwoRootOfPoint_map {K L : Type*} [CommRing K] [CommRing L]
    [Algebra ℚ K] [Algebra ℚ L] (σ : K →ₐ[ℚ] L)
    (F : RationalMuTwoPoint K) :
    muTwoRootOfPoint (muTwoPointMap σ F) =
      restrictRootsOfUnity σ 2 (muTwoRootOfPoint F) := by
  apply rootsOfUnity.coe_injective
  rfl

@[simp]
theorem muTwoPointOfRoot_map {K L : Type*} [CommRing K] [CommRing L]
    [Algebra ℚ K] [Algebra ℚ L] (σ : K →ₐ[ℚ] L)
    (z : rootsOfUnity 2 K) :
    muTwoPointMap σ (muTwoPointOfRoot z) =
      muTwoPointOfRoot (restrictRootsOfUnity σ 2 z) := by
  calc
    muTwoPointMap σ (muTwoPointOfRoot z) =
        muTwoPointOfRoot (muTwoRootOfPoint (muTwoPointMap σ (muTwoPointOfRoot z))) :=
      (muTwoPointOfRoot_muTwoRootOfPoint _).symm
    _ = muTwoPointOfRoot (restrictRootsOfUnity σ 2 z) := by
      rw [muTwoRootOfPoint_map, muTwoRootOfPoint_muTwoPointOfRoot]

abbrev RationalMuTwoCharacterGroup :=
  GroupLike ℚ RationalMuTwoCoordinateRing

def muTwoMonomialGroupLike :
    Multiplicative (ZMod 2) →* RationalMuTwoCharacterGroup where
  toFun g :=
    { val := AddMonoidAlgebra.single g.toAdd 1
      isGroupLikeElem_val := by
        constructor <;> simp [AddMonoidAlgebra.comul_single] }
  map_one' := by
    apply GroupLike.val_injective
    simp [AddMonoidAlgebra.one_def]
  map_mul' g h := by
    apply GroupLike.val_injective
    simp [AddMonoidAlgebra.single_mul_single]

theorem muTwoMonomialGroupLike_injective :
    Function.Injective muTwoMonomialGroupLike := by
  intro g h hgh
  apply Multiplicative.toAdd.injective
  apply Finsupp.single_left_injective (one_ne_zero : (1 : ℚ) ≠ 0)
  exact congrArg GroupLike.val hgh

theorem finrank_rationalMuTwoCoordinateRing :
    Module.finrank ℚ RationalMuTwoCoordinateRing = 2 := by
  rw [Module.finrank_eq_card_basis (AddMonoidAlgebra.basis (ZMod 2) ℚ)]
  decide

noncomputable instance : Finite RationalMuTwoCharacterGroup := by
  letI : Module.Finite ℚ RationalMuTwoCoordinateRing :=
    Module.Finite.of_basis (AddMonoidAlgebra.basis (ZMod 2) ℚ)
  exact (linearIndep_groupLikeVal (R := ℚ)
    (A := RationalMuTwoCoordinateRing)).finite

theorem natCard_rationalMuTwoCharacterGroup_eq_two :
    Nat.card RationalMuTwoCharacterGroup = 2 := by
  letI : Module.Finite ℚ RationalMuTwoCoordinateRing :=
    Module.Finite.of_basis (AddMonoidAlgebra.basis (ZMod 2) ℚ)
  letI := Fintype.ofFinite RationalMuTwoCharacterGroup
  apply Nat.le_antisymm
  · rw [Nat.card_eq_fintype_card, ← finrank_rationalMuTwoCoordinateRing]
    exact (linearIndep_groupLikeVal (R := ℚ)
      (A := RationalMuTwoCoordinateRing)).fintype_card_le_finrank
  · simpa using Nat.card_le_card_of_injective muTwoMonomialGroupLike
      muTwoMonomialGroupLike_injective

def muTwoMonomialGroupLikeEquiv :
    Multiplicative (ZMod 2) ≃* RationalMuTwoCharacterGroup :=
  MulEquiv.ofBijective muTwoMonomialGroupLike
    ((Nat.bijective_iff_injective_and_card muTwoMonomialGroupLike).2
      ⟨muTwoMonomialGroupLike_injective, by
        simp [natCard_rationalMuTwoCharacterGroup_eq_two]⟩)

abbrev rationalMuTwoAffineScheme : Scheme :=
  Spec (CommRingCat.of RationalMuTwoCoordinateRing)

def rationalMuTwoStructureMap :
    rationalMuTwoAffineScheme ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ RationalMuTwoCoordinateRing))

def rationalAffineStructureMap (K : Type) [CommRing K] [Algebra ℚ K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ K))

abbrev RationalMuTwoSchemePoint (K : Type) [CommRing K] [Algebra ℚ K] :=
  { f : Spec (CommRingCat.of K) ⟶ rationalMuTwoAffineScheme //
    f ≫ rationalMuTwoStructureMap = rationalAffineStructureMap K }

def muTwoSchemePointOfPoint {K : Type} [CommRing K] [Algebra ℚ K]
    (F : RationalMuTwoPoint K) : RationalMuTwoSchemePoint K :=
  ⟨Spec.map (CommRingCat.ofHom F.toRingHom), by
    change Spec.map (CommRingCat.ofHom F.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ RationalMuTwoCoordinateRing)) =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ K))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext q
    exact F.commutes q⟩

def muTwoPointOfSchemePoint {K : Type} [CommRing K] [Algebra ℚ K]
    (f : RationalMuTwoSchemePoint K) : RationalMuTwoPoint K where
  toRingHom := (Spec.preimage f.1).hom
  commutes' q := by
    have h := congrArg Spec.preimage f.2
    rw [Spec.preimage_comp] at h
    simp only [rationalMuTwoStructureMap, rationalAffineStructureMap,
      Spec.preimage_map] at h
    exact congrArg
      (fun g : CommRingCat.of ℚ ⟶ CommRingCat.of K => g.hom q) h

def muTwoSchemePointEquivPoint {K : Type} [CommRing K] [Algebra ℚ K] :
    RationalMuTwoSchemePoint K ≃ RationalMuTwoPoint K where
  toFun := muTwoPointOfSchemePoint
  invFun := muTwoSchemePointOfPoint
  left_inv f := by
    apply Subtype.ext
    exact Spec.map_preimage f.1
  right_inv F := by
    apply AlgHom.ext
    intro x
    exact congrArg
      (fun g : CommRingCat.of RationalMuTwoCoordinateRing ⟶ CommRingCat.of K => g.hom x)
      (Spec.preimage_map (CommRingCat.ofHom F.toRingHom))

def muTwoSchemePointEquivRootsOfUnity {K : Type} [CommRing K] [Algebra ℚ K] :
    RationalMuTwoSchemePoint K ≃ rootsOfUnity 2 K :=
  muTwoSchemePointEquivPoint.trans muTwoPointEquivRootsOfUnity

end RationalTamagawa
