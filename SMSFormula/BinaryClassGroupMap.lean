import SMSFormula.BinaryIdealClassCorrespondence
import SMSFormula.BinaryUnitStabilizer
import Mathlib.RingTheory.ClassGroup

/-!
# The actual binary norm ideal in the canonical class group

The class map uses the explicit fractional-ideal unit over the common
quadratic order. Equality is detected by the proved proper polynomial
criterion. No Dedekind-domain assumption or substitute class carrier is used.
-/

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Clear the denominator of an actual invertible fractional ideal without
requiring every nonzero integral ideal to be invertible. -/
noncomputable def integralUnitRepresentative
    (u : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    (FractionalIdeal R⁰ (FractionRing R))ˣ :=
  ((isUnit_num).mpr u.isUnit).unit

lemma integralUnitRepresentative_val (u : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    (integralUnitRepresentative u : FractionalIdeal R⁰ (FractionRing R)) =
      ((u : FractionalIdeal R⁰ (FractionRing R)).num : FractionalIdeal R⁰ (FractionRing R)) :=
  ((isUnit_num).mpr u.isUnit).unit_spec

/-- Clearing the denominator preserves the canonical class for any domain. -/
theorem mk_integralUnitRepresentative (u : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    ClassGroup.mk (FractionRing R) (integralUnitRepresentative u) =
      ClassGroup.mk (FractionRing R) u := by
  symm
  apply ClassGroup.mk_eq_mk.mpr
  let I : FractionalIdeal R⁰ (FractionRing R) := u
  have hn : algebraMap R (FractionRing R) I.den ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.prop
  refine ⟨Units.mk0 (algebraMap R (FractionRing R) I.den) hn, ?_⟩
  apply Units.ext
  rw [Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, integralUnitRepresentative_val, mul_comm]
  exact den_mul_self_eq_num' R⁰ (FractionRing R) I

end FractionalIdeal

/-- Every canonical class has an invertible integral representative, including
for nonmaximal orders. This does not use the Dedekind-only mk0 map. -/
theorem ClassGroup.exists_integral_unit_representative {R : Type*} [CommRing R] [IsDomain R]
    (c : ClassGroup R) :
    ∃ (I : Ideal R) (u : (FractionalIdeal R⁰ (FractionRing R))ˣ),
      (u : FractionalIdeal R⁰ (FractionRing R)) = I ∧ ClassGroup.mk (FractionRing R) u = c := by
  refine ClassGroup.induction (FractionRing R) (fun u => ?_) c
  exact ⟨(u : FractionalIdeal R⁰ (FractionRing R)).num,
    FractionalIdeal.integralUnitRepresentative u, FractionalIdeal.integralUnitRepresentative_val u,
    FractionalIdeal.mk_integralUnitRepresentative u⟩

namespace PositiveDefiniteIntegralLattice

/-- The actual integral norm ideal transported only along discriminant equality. -/
def binaryDiscriminantNormIdealAt (L : PositiveDefiniteIntegralLattice 2) (D : ℤ)
    (hD : L.binaryPrimitiveDiscriminant = D) : Ideal (BinaryNormIdeal.DiscriminantOrder D) :=
  hD ▸ L.binaryDiscriminantNormIdeal

/-- The existing explicit unit, in the fraction field of the fixed order. -/
noncomputable def binaryFractionalNormIdealUnitAt (L : PositiveDefiniteIntegralLattice 2) (D : ℤ)
    (hD : L.binaryPrimitiveDiscriminant = D) :
    (FractionalIdeal (BinaryNormIdeal.DiscriminantOrder D)⁰
      (FractionRing (BinaryNormIdeal.DiscriminantOrder D)))ˣ :=
  hD ▸ L.binaryFractionalNormIdealUnit

lemma binaryFractionalNormIdealUnitAt_val (L : PositiveDefiniteIntegralLattice 2) (D : ℤ)
    (hD : L.binaryPrimitiveDiscriminant = D) :
    (binaryFractionalNormIdealUnitAt L D hD :
      FractionalIdeal (BinaryNormIdeal.DiscriminantOrder D)⁰
        (FractionRing (BinaryNormIdeal.DiscriminantOrder D))) =
      (binaryDiscriminantNormIdealAt L D hD :
        FractionalIdeal (BinaryNormIdeal.DiscriminantOrder D)⁰
          (FractionRing (BinaryNormIdeal.DiscriminantOrder D))) := by
  subst D
  rfl

/-- Equality transport is exactly the canonical coefficient-order embedding. -/
lemma binaryDiscriminantNormIdealAt_eq_map (L : PositiveDefiniteIntegralLattice 2) (D : ℤ)
    (hD : L.binaryPrimitiveDiscriminant = D) :
    binaryDiscriminantNormIdealAt L D hD =
      Ideal.map (BinaryNormIdeal.coefficientOrderEquivDiscriminantOrder
        (L.pairingMatrix 0 0 / (L.binaryContent : ℤ))
        (2*L.pairingMatrix 0 1 / (L.binaryContent : ℤ))
        (L.pairingMatrix 1 1 / (L.binaryContent : ℤ)) D
        (hD ▸ L.binaryPrimitiveDiscriminant_mod_four) hD).toRingHom L.binaryNormIdeal := by
  subst D
  exact (Ideal.map_comap_of_equiv L.binaryCoefficientOrderEquivDiscriminantOrder.toRingEquiv).symm

/-- The canonical ideal class of the actual explicit fractional-ideal unit. -/
noncomputable def binaryIdealClassAt (L : PositiveDefiniteIntegralLattice 2) (D : ℤ)
    (hD : L.binaryPrimitiveDiscriminant = D)
    [IsDomain (BinaryNormIdeal.DiscriminantOrder D)] :
    ClassGroup (BinaryNormIdeal.DiscriminantOrder D) :=
  ClassGroup.mk (FractionRing (BinaryNormIdeal.DiscriminantOrder D))
    (binaryFractionalNormIdealUnitAt L D hD)

/-- Equality of the actual canonical ideal classes detects the original proper
lattice relation at fixed content. No inverse or class certificate is supplied. -/
theorem binaryIdealClassAt_eq_iff_isProperGlobalIsometry
    (K L : PositiveDefiniteIntegralLattice 2) (hg : K.binaryContent = L.binaryContent)
    (D : ℤ) (hK : K.binaryPrimitiveDiscriminant = D) (hL : L.binaryPrimitiveDiscriminant = D)
    [IsDomain (BinaryNormIdeal.DiscriminantOrder D)] :
    binaryIdealClassAt L D hL = binaryIdealClassAt K D hK ↔ K.IsProperGlobalIsometry L := by
  rw [binaryIdealClassAt, binaryIdealClassAt,
    ClassGroup.mk_eq_mk_of_coe_ideal (binaryFractionalNormIdealUnitAt_val L D hL)
      (binaryFractionalNormIdealUnitAt_val K D hK),
    binaryDiscriminantNormIdealAt_eq_map, binaryDiscriminantNormIdealAt_eq_map]
  have hp := BinaryNormIdeal.proper_polynomial_matrix_iff_commonOrder_principal_scaling
    (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))
    (2*K.pairingMatrix 0 1 / (K.binaryContent : ℤ))
    (K.pairingMatrix 1 1 / (K.binaryContent : ℤ))
    (L.pairingMatrix 0 0 / (L.binaryContent : ℤ))
    (2*L.pairingMatrix 0 1 / (L.binaryContent : ℤ))
    (L.pairingMatrix 1 1 / (L.binaryContent : ℤ)) D
    K.binaryPrimitivePolynomial_leading_pos L.binaryPrimitivePolynomial_leading_pos
    (hK ▸ K.binaryPrimitiveDiscriminant_neg) (hK ▸ K.binaryPrimitiveDiscriminant_mod_four) hK hL
  constructor
  · intro h
    obtain ⟨U,hU,hd,hpoly⟩ := hp.mpr h
    refine ⟨U,hU,hd,?_⟩
    have hm := (binaryPrimitivePolynomialOver_matrix_congruence_iff K L hg U).mpr (by
      intro v
      simpa only [binaryPrimitivePolynomialOver_apply, Int.cast_id] using hpoly v)
    simpa only [Int.cast_id, Matrix.map_id] using hm
  · rintro ⟨U,hU,hd,hm⟩
    apply hp.mp
    refine ⟨U,hU,hd,?_⟩
    intro v
    have hpoly := (binaryPrimitivePolynomialIsometryEquivOfMatrix K L U hU hm).map_app v
    rw [binaryPrimitivePolynomialIsometryEquivOfMatrix_apply] at hpoly
    simpa only [binaryPrimitivePolynomial_apply] using hpoly

/-- The canonical ideal class of an original proper genus class. The chosen
representative is transported to the base lattice's actual common order. -/
noncomputable def binaryProperGenusIdealClass (K : PositiveDefiniteIntegralLattice 2) (C : K.properGenus) :
    letI := K.binaryDiscriminantOrder_isDomain
    ClassGroup (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact binaryIdealClassAt (properGenusClassRepresentative K C) K.binaryPrimitiveDiscriminant
    (properGenusClassRepresentative_isSameGenus K C).binaryPrimitiveDiscriminant_eq.symm

/-- The canonical map does not depend on the chosen representative. -/
theorem binaryProperGenusIdealClass_eq_of_representative (K : PositiveDefiniteIntegralLattice 2)
    (C : K.properGenus) (L : PositiveDefiniteIntegralLattice 2) (hgen : K.IsSameGenus L)
    (hclass : C.val = L.properGlobalIsometryClass) :
    letI := K.binaryDiscriminantOrder_isDomain
    binaryProperGenusIdealClass K C =
      binaryIdealClassAt L K.binaryPrimitiveDiscriminant hgen.binaryPrimitiveDiscriminant_eq.symm := by
  letI := K.binaryDiscriminantOrder_isDomain
  let M := properGenusClassRepresentative K C
  have hM := properGenusClassRepresentative_isSameGenus K C
  have hp : M.IsProperGlobalIsometry L :=
    isProperGlobalIsometry_of_properGlobalIsometryClass_eq
      ((properGenusClassRepresentative_spec K C).2.symm.trans hclass)
  have hh := (binaryIdealClassAt_eq_iff_isProperGlobalIsometry M L
    (hM.binaryContent_eq.symm.trans hgen.binaryContent_eq) K.binaryPrimitiveDiscriminant
    hM.binaryPrimitiveDiscriminant_eq.symm hgen.binaryPrimitiveDiscriminant_eq.symm).mpr hp
  exact hh.symm

/-- The original proper genus embeds into the canonical order class group.
This does not assert that its image is the whole group or a square coset. -/
theorem binaryProperGenusIdealClass_injective (K : PositiveDefiniteIntegralLattice 2) :
    Function.Injective (binaryProperGenusIdealClass K) := by
  letI := K.binaryDiscriminantOrder_isDomain
  intro C C' hh
  let M := properGenusClassRepresentative K C
  let M' := properGenusClassRepresentative K C'
  have hM := properGenusClassRepresentative_isSameGenus K C
  have hM' := properGenusClassRepresentative_isSameGenus K C'
  have hp : M.IsProperGlobalIsometry M' :=
    (binaryIdealClassAt_eq_iff_isProperGlobalIsometry M M'
      (hM.binaryContent_eq.symm.trans hM'.binaryContent_eq) K.binaryPrimitiveDiscriminant
      hM.binaryPrimitiveDiscriminant_eq.symm hM'.binaryPrimitiveDiscriminant_eq.symm).mp hh.symm
  apply Subtype.ext
  rw [(properGenusClassRepresentative_spec K C).2,
    (properGenusClassRepresentative_spec K C').2]
  exact properGlobalIsometryClass_eq_of_isProperGlobalIsometry hp

/-- The finite cardinality of the actual proper genus equals that of its
canonical class-group image, with no class-group finiteness assumption. -/
theorem card_binaryProperGenusIdealClass_range (K : PositiveDefiniteIntegralLattice 2) :
    Nat.card (Set.range (binaryProperGenusIdealClass K)) = Fintype.card K.properGenus := by
  rw [Nat.card_congr (Equiv.ofInjective (binaryProperGenusIdealClass K)
    (binaryProperGenusIdealClass_injective K)).symm]
  exact Nat.card_eq_fintype_card

/-- Ordinary mass now uses the cardinality of the actual canonical class-group
image. The image is not identified with the whole group or a square coset here. -/
theorem ordinaryGenusMass_eq_card_binaryIdealClassImage_div_two_normOneUnits
    (K : PositiveDefiniteIntegralLattice 2) :
    K.ordinaryGenusMass =
      (Nat.card (Set.range (binaryProperGenusIdealClass K)) : ℚ) /
        (2 * (Nat.card (BinaryNormIdeal.DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) : ℚ)) := by
  rw [card_binaryProperGenusIdealClass_range]
  exact K.ordinaryGenusMass_eq_card_properGenus_div_two_discriminantNormOneUnits

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDiscriminantNormIdealAt
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdealUnitAt
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdealUnitAt_val
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDiscriminantNormIdealAt_eq_map
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealClassAt
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealClassAt_eq_iff_isProperGlobalIsometry

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryProperGenusIdealClass
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryProperGenusIdealClass_eq_of_representative
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryProperGenusIdealClass_injective
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryProperGenusIdealClass_range

#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_card_binaryIdealClassImage_div_two_normOneUnits

#assert_standard_axioms FractionalIdeal.integralUnitRepresentative
#assert_standard_axioms FractionalIdeal.integralUnitRepresentative_val
#assert_standard_axioms FractionalIdeal.mk_integralUnitRepresentative
#assert_standard_axioms ClassGroup.exists_integral_unit_representative
