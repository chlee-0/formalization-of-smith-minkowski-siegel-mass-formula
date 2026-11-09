import SMSFormula.BinaryOrderConductor

/-!
# Original order units and the actual unit index

Positive integral norms identify the original full unit group with its
norm-one unit carrier. Its embedding in maximal-order units has an actual
finite index. These two unit groups are not identified with one another.
-/

namespace BinaryNormIdeal

/-- Every original order unit has norm one. Negative discriminant, rather
than maximality or primitivity, supplies the positive sign. -/
theorem norm_coefficientOrder_unit (a b c : ℤ) (hD : b^2-4*a*c < 0)
    (u : (CoefficientOrder a b c)ˣ) : (u : CoefficientOrder a b c).norm = 1 := by
  have hp := norm_pos_of_discriminant_neg a b c hD (u : CoefficientOrder a b c) u.ne_zero
  have hq := norm_pos_of_discriminant_neg a b c hD (↑u⁻¹ : CoefficientOrder a b c) (u⁻¹).ne_zero
  have hm : (u : CoefficientOrder a b c).norm * (↑u⁻¹ : CoefficientOrder a b c).norm = 1 := by
    rw [← map_mul]
    simp
  nlinarith

/-- The original full unit carrier is exactly its norm-one unit carrier. -/
def coefficientUnitsEquivNormOne (a b c : ℤ) (hD : b^2-4*a*c < 0) :
    (CoefficientOrder a b c)ˣ ≃ {u : (CoefficientOrder a b c)ˣ //
      (u : CoefficientOrder a b c).norm = 1} where
  toFun u := ⟨u,norm_coefficientOrder_unit a b c hD u⟩
  invFun u := u.val
  left_inv _ := rfl
  right_inv _ := rfl

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The actual unit embedding induced by the original integral order map. -/
noncomputable def coefficientUnitsToIntegerUnits :
    (CoefficientOrder a b c)ˣ →*
      (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))ˣ :=
  Units.map (orderToRingOfIntegers a b c).toMonoidHom

theorem coefficientUnitsToIntegerUnits_injective :
    Function.Injective (coefficientUnitsToIntegerUnits a b c) :=
  Units.map_injective (orderToRingOfIntegers_injective a b c)

theorem finite_coefficientOrder_units (hD : b^2-4*a*c < 0) :
    Finite (CoefficientOrder a b c)ˣ := by
  letI := fractionNumberField a b c hD
  letI := fraction_finite_integerUnits a b c hD
  exact Finite.of_injective _ (coefficientUnitsToIntegerUnits_injective a b c)

/-- The index of the actual original unit image in the same maximal-order
unit group. It is not silently replaced by one. -/
noncomputable def orderUnitIndex : ℕ := (coefficientUnitsToIntegerUnits a b c).range.index

theorem orderUnitIndex_pos (hD : b^2-4*a*c < 0) : 0 < orderUnitIndex a b c := by
  letI := fractionNumberField a b c hD
  letI := fraction_finite_integerUnits a b c hD
  exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
    (H := (coefficientUnitsToIntegerUnits a b c).range))

/-- The actual maximal-order unit count is the original unit count times
the actual unit index. No numerical root-of-unity classification is used. -/
theorem card_integerUnits_eq_orderUnits_mul_index :
    Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))ˣ =
      Nat.card (CoefficientOrder a b c)ˣ * orderUnitIndex a b c := by
  let f := coefficientUnitsToIntegerUnits a b c
  have he : (CoefficientOrder a b c)ˣ ≃ f.range :=
    Equiv.ofInjective f (coefficientUnitsToIntegerUnits_injective a b c)
  rw [show Nat.card (CoefficientOrder a b c)ˣ = Nat.card f.range from Nat.card_congr he]
  exact f.range.card_mul_index.symm

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- w_D counts all units of the original order, not the maximal order. -/
def binaryOrderUnitsEquivNormOneUnits (K : PositiveDefiniteIntegralLattice 2) :
    (DiscriminantOrder K.binaryPrimitiveDiscriminant)ˣ ≃
      DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant :=
  coefficientUnitsEquivNormOne _ _ _ K.binaryDiscriminantOrder_discriminant_neg

theorem card_binaryOrderUnits_eq_normOneUnits (K : PositiveDefiniteIntegralLattice 2) :
    Nat.card (DiscriminantOrder K.binaryPrimitiveDiscriminant)ˣ =
      Nat.card (DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) :=
  Nat.card_congr K.binaryOrderUnitsEquivNormOneUnits

theorem finite_binaryOrderUnits (K : PositiveDefiniteIntegralLattice 2) :
    Finite (DiscriminantOrder K.binaryPrimitiveDiscriminant)ˣ := by
  letI := K.finite_discriminantNormOneUnits
  exact Finite.of_equiv _ K.binaryOrderUnitsEquivNormOneUnits.symm

/-- The index of the actual original-order unit image. -/
noncomputable def binaryOrderUnitIndex (K : PositiveDefiniteIntegralLattice 2) : ℕ := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact orderUnitIndex 1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)

theorem binaryOrderUnitIndex_pos (K : PositiveDefiniteIntegralLattice 2) : 0 < K.binaryOrderUnitIndex := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact orderUnitIndex_pos _ _ _ K.binaryDiscriminantOrder_discriminant_neg

/-- The field torsion count is w_D times the actual unit index. This keeps
the original and maximal-order unit counts separate at nonmaximal orders. -/
theorem binaryFraction_torsionOrder_eq_normOneUnits_mul_orderUnitIndex (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    NumberField.Units.torsionOrder (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) =
      Nat.card (DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) * K.binaryOrderUnitIndex := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  rw [K.binaryFraction_torsionOrder_eq_card_integerUnits,
    card_integerUnits_eq_orderUnits_mul_index _ _ _,
    K.card_binaryOrderUnits_eq_normOneUnits]
  rfl

/-- The existing full-O mass formula in terms of the original full unit
count. The aggregate proper/full comparison remains unchanged. -/
theorem ordinaryGenusMass_eq_classNumber_div_two_orderUnits_twoTorsion (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    ordinaryGenusMass K =
      (Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) : ℚ) /
        (2 * (Nat.card (DiscriminantOrder K.binaryPrimitiveDiscriminant)ˣ : ℚ) *
          Nat.card ((powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
            ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [card_binaryOrderUnits_eq_normOneUnits]
  exact K.ordinaryGenusMass_eq_classNumber_div_two_normOneUnits_twoTorsion

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.norm_coefficientOrder_unit
#assert_standard_axioms BinaryNormIdeal.coefficientUnitsEquivNormOne
#assert_standard_axioms BinaryNormIdeal.coefficientUnitsToIntegerUnits
#assert_standard_axioms BinaryNormIdeal.coefficientUnitsToIntegerUnits_injective
#assert_standard_axioms BinaryNormIdeal.finite_coefficientOrder_units
#assert_standard_axioms BinaryNormIdeal.orderUnitIndex
#assert_standard_axioms BinaryNormIdeal.orderUnitIndex_pos
#assert_standard_axioms BinaryNormIdeal.card_integerUnits_eq_orderUnits_mul_index
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderUnitsEquivNormOneUnits
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryOrderUnits_eq_normOneUnits
#assert_standard_axioms PositiveDefiniteIntegralLattice.finite_binaryOrderUnits
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderUnitIndex
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderUnitIndex_pos
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFraction_torsionOrder_eq_normOneUnits_mul_orderUnitIndex
#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_classNumber_div_two_orderUnits_twoTorsion
