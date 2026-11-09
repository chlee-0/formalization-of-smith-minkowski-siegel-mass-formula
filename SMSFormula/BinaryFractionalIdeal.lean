import SMSFormula.BinaryDiscriminantOrder
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.RingTheory.FractionalIdeal.Inverse

/-!
# Invertible fractional ideals of the actual binary norm order

The integral identity I conjugate(I)=(A) supplies an explicit inverse in
Mathlib's fractional-ideal carrier. No Dedekind-domain or maximal-order
assumption is used. The common discriminant order stays fixed.
-/

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R P : Type*} [CommRing R] [IsDomain R] [Field P]
  [Algebra R P] [IsFractionRing R P]

/-- If integral ideals multiply to a principal ideal, its principal inverse
scales the second ideal to the fractional inverse of the first. -/
noncomputable def inverseOfIntegralProduct (J : Ideal R) (a : R) : FractionalIdeal R⁰ P :=
  (J : FractionalIdeal R⁰ P) * (Ideal.span {a} : FractionalIdeal R⁰ P)⁻¹

theorem mul_inverseOfIntegralProduct (I J : Ideal R) (a : R) (ha : a ≠ 0)
    (hIJ : I * J = Ideal.span {a}) :
    (I : FractionalIdeal R⁰ P) * inverseOfIntegralProduct (P := P) J a = 1 := by
  unfold inverseOfIntegralProduct
  rw [← mul_assoc, ← coeIdeal_mul, hIJ]
  exact coe_ideal_span_singleton_mul_inv P ha

/-- The constructed inverse agrees with the fractional-ideal inverse of `I`. -/
theorem inverseOfIntegralProduct_eq_inv (I J : Ideal R) (a : R) (ha : a ≠ 0)
    (hIJ : I * J = Ideal.span {a}) :
    inverseOfIntegralProduct (P := P) J a = (I : FractionalIdeal R⁰ P)⁻¹ :=
  right_inverse_eq P _ _ (mul_inverseOfIntegralProduct I J a ha hIJ)

/-- Invertible fractional-ideal data, with an explicit inverse. -/
noncomputable def unitOfIntegralProduct (I J : Ideal R) (a : R) (ha : a ≠ 0)
    (hIJ : I * J = Ideal.span {a}) : (FractionalIdeal R⁰ P)ˣ where
  val := I
  inv := inverseOfIntegralProduct J a
  val_inv := mul_inverseOfIntegralProduct I J a ha hIJ
  inv_val := by rw [mul_comm]; exact mul_inverseOfIntegralProduct I J a ha hIJ

omit [IsDomain R] in
/-- An invertible fractional ideal has no extra multipliers: a field element
stabilizes it by inclusion exactly when it belongs to the base order. -/
theorem multiplier_iff_of_isUnit (I : FractionalIdeal R⁰ P) (hI : IsUnit I) (x : P) :
    (∀ y ∈ I, x * y ∈ I) ↔ ∃ r : R, algebraMap R P r = x := by
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := hI
    have hle : spanSingleton R⁰ x * (u : FractionalIdeal R⁰ P) ≤ u :=
      spanSingleton_mul_le_iff.mpr hx
    have hspan : spanSingleton R⁰ x ≤ 1 := by
      calc
        spanSingleton R⁰ x = (spanSingleton R⁰ x * (u : FractionalIdeal R⁰ P)) * ↑(u⁻¹) := by
          simp [mul_assoc]
        _ ≤ (u : FractionalIdeal R⁰ P) * ↑(u⁻¹) := mul_le_mul_left hle _
        _ = 1 := by simp
    apply (mem_one_iff R⁰).mp
    apply hspan
    exact (mem_spanSingleton R⁰).mpr ⟨1, one_smul R x⟩
  · rintro ⟨r, rfl⟩ y hy
    simpa only [← Algebra.smul_def] using (I : Submodule R P).smul_mem r hy

end FractionalIdeal

namespace BinaryNormIdeal

/-- Negative discriminant makes the integral coefficient order a domain,
through the already verified rational-field injection. -/
theorem coefficientOrder_isDomain (a b c : ℤ) (hD : b ^ 2 - 4 * a * c < 0) :
    IsDomain (CoefficientOrder a b c) := by
  letI := rationalField a b c hD
  exact Function.Injective.isDomain (rationalMap a b c) (rationalMap_injective a b c)

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

/-- The common order is a domain for every actual positive binary lattice.
This proof is supplied explicitly when a fraction-field instance is needed. -/
theorem binaryDiscriminantOrder_isDomain (K : PositiveDefiniteIntegralLattice 2) :
    IsDomain (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant) := by
  letI := BinaryNormIdeal.coefficientOrder_isDomain
    (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))
    ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ))
    (K.pairingMatrix 1 1 / (K.binaryContent : ℤ)) K.binaryPrimitiveDiscriminant_neg
  exact Function.Injective.isDomain K.binaryCoefficientOrderEquivDiscriminantOrder.symm.toRingHom
    K.binaryCoefficientOrderEquivDiscriminantOrder.symm.injective

/-- The conjugate norm ideal transported into the same common discriminant order. -/
def binaryDiscriminantConjugateNormIdeal (K : PositiveDefiniteIntegralLattice 2) :
    Ideal (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant) :=
  (BinaryNormIdeal.conjugateNormIdeal
    (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))
    ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ))
    (K.pairingMatrix 1 1 / (K.binaryContent : ℤ))).comap
      K.binaryCoefficientOrderEquivDiscriminantOrder.symm.toRingHom

/-- The proved integral inverse identity holds in the common order itself. -/
theorem binaryDiscriminantNormIdeal_mul_conjugate (K : PositiveDefiniteIntegralLattice 2) :
    K.binaryDiscriminantNormIdeal * K.binaryDiscriminantConjugateNormIdeal =
      Ideal.span {((K.pairingMatrix 0 0 / (K.binaryContent : ℤ) : ℤ) :
        BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant)} := by
  let e := K.binaryCoefficientOrderEquivDiscriminantOrder
  have h := congrArg (Ideal.map e.toRingHom) K.binaryNormIdeal_mul_conjugate
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at h
  simp only [RingEquiv.toRingHom_eq_coe] at h
  rw [Ideal.map_comap_of_equiv e.toRingEquiv, Ideal.map_comap_of_equiv e.toRingEquiv] at h
  simpa only [map_intCast] using h

/-- Fractional ideals in the canonical fraction field of the common order. -/
abbrev BinaryDiscriminantFractionalIdeals (K : PositiveDefiniteIntegralLattice 2) :=
  FractionalIdeal (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant)⁰
    (FractionRing (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant))

/-- The actual norm ideal as an element of Mathlib's fractional-ideal carrier. -/
def binaryFractionalNormIdeal (K : PositiveDefiniteIntegralLattice 2) : K.BinaryDiscriminantFractionalIdeals :=
  K.binaryDiscriminantNormIdeal

/-- The explicit fractional inverse is conjugate(I) times the inverse of (A). -/
noncomputable def binaryFractionalNormIdealInverse (K : PositiveDefiniteIntegralLattice 2) :
    K.BinaryDiscriminantFractionalIdeals := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact FractionalIdeal.inverseOfIntegralProduct K.binaryDiscriminantConjugateNormIdeal
    ((K.pairingMatrix 0 0 / (K.binaryContent : ℤ) : ℤ) :
      BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant)

private lemma binaryLeading_coe_order_ne_zero (K : PositiveDefiniteIntegralLattice 2) :
    ((K.pairingMatrix 0 0 / (K.binaryContent : ℤ) : ℤ) :
      BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant) ≠ 0 := by
  intro h
  have hr := congrArg QuadraticAlgebra.re h
  have hz : K.pairingMatrix 0 0 / (K.binaryContent : ℤ) = 0 := by
    simpa only [QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_zero, Int.cast_id] using hr
  exact (ne_of_gt K.binaryPrimitivePolynomial_leading_pos) hz

theorem binaryFractionalNormIdeal_mul_inverse (K : PositiveDefiniteIntegralLattice 2) :
    K.binaryFractionalNormIdeal * K.binaryFractionalNormIdealInverse = 1 := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact FractionalIdeal.mul_inverseOfIntegralProduct K.binaryDiscriminantNormIdeal
    K.binaryDiscriminantConjugateNormIdeal _ (binaryLeading_coe_order_ne_zero K)
      K.binaryDiscriminantNormIdeal_mul_conjugate

/-- An actual unit of the fractional-ideal monoid; its value is the actual
norm ideal, not a principal or maximal-order substitute. -/
noncomputable def binaryFractionalNormIdealUnit (K : PositiveDefiniteIntegralLattice 2) :
    K.BinaryDiscriminantFractionalIdealsˣ where
  val := K.binaryFractionalNormIdeal
  inv := K.binaryFractionalNormIdealInverse
  val_inv := K.binaryFractionalNormIdeal_mul_inverse
  inv_val := by rw [mul_comm]; exact K.binaryFractionalNormIdeal_mul_inverse

lemma binaryFractionalNormIdealUnit_val (K : PositiveDefiniteIntegralLattice 2) :
    (K.binaryFractionalNormIdealUnit : K.BinaryDiscriminantFractionalIdeals) =
      K.binaryFractionalNormIdeal := rfl

/-- The explicit conjugate/principal inverse is the standard Mathlib inverse. -/
theorem binaryFractionalNormIdealInverse_eq_inv (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryFractionalNormIdealInverse = K.binaryFractionalNormIdeal⁻¹ := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact FractionalIdeal.right_inverse_eq _ _ _ K.binaryFractionalNormIdeal_mul_inverse

/-- The actual norm ideal is proper: its multiplier ring in the common
fraction field is exactly the original common discriminant order. -/
theorem binaryFractionalNormIdeal_multiplier_iff (K : PositiveDefiniteIntegralLattice 2)
    (x : FractionRing (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    (∀ y ∈ K.binaryFractionalNormIdeal, x * y ∈ K.binaryFractionalNormIdeal) ↔
      ∃ r : BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant,
        algebraMap _ _ r = x := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact FractionalIdeal.multiplier_iff_of_isUnit K.binaryFractionalNormIdeal
    ⟨K.binaryFractionalNormIdealUnit, rfl⟩ x

end PositiveDefiniteIntegralLattice

#assert_standard_axioms FractionalIdeal.inverseOfIntegralProduct
#assert_standard_axioms FractionalIdeal.mul_inverseOfIntegralProduct
#assert_standard_axioms FractionalIdeal.inverseOfIntegralProduct_eq_inv
#assert_standard_axioms FractionalIdeal.unitOfIntegralProduct
#assert_standard_axioms FractionalIdeal.multiplier_iff_of_isUnit
#assert_standard_axioms BinaryNormIdeal.coefficientOrder_isDomain
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDiscriminantOrder_isDomain
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDiscriminantConjugateNormIdeal
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDiscriminantNormIdeal_mul_conjugate
#assert_standard_axioms PositiveDefiniteIntegralLattice.BinaryDiscriminantFractionalIdeals
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdeal
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdealInverse
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdeal_mul_inverse
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdealUnit
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdealUnit_val
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdealInverse_eq_inv
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdeal_multiplier_iff
