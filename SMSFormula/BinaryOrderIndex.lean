import SMSFormula.BinaryImaginarySignature
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# The actual quadratic order index and field discriminant

The original order image is a full integer sublattice of the ring of
integers of the same field. Its actual quotient cardinal is the positive
order index. Discriminants differ by the square of this actual index.
No conductor or class-number correction is assumed.
-/

namespace BinaryNormIdeal

open Module
open scoped nonZeroDivisors

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The original order as an integer submodule in the same maximal order. -/
noncomputable def orderImage :
    Submodule ℤ (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) :=
  (orderToRingOfIntegers a b c).toLinearMap.range

/-- The original integer basis transported to its actual image. -/
noncomputable def orderImageBasis : Basis (Fin 2) ℤ (orderImage a b c) :=
  (QuadraticAlgebra.basis (-a*c) b).map
    (LinearEquiv.ofInjective (orderToRingOfIntegers a b c).toLinearMap
      (orderToRingOfIntegers_injective a b c))

theorem orderImageBasis_coe (i : Fin 2) :
    ((orderImageBasis a b c i : orderImage a b c) :
      NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))=
        orderToRingOfIntegers a b c (QuadraticAlgebra.basis (-a*c) b i) := rfl

/-- A two-element integer basis of the actual maximal order. -/
noncomputable def maximalOrderBasis (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    Basis (Fin 2) ℤ (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) := by
  letI := fractionNumberField a b c hD
  exact Module.finBasisOfFinrankEq ℤ _
    ((NumberField.RingOfIntegers.rank _).trans (fractionField_finrank_two a b c hD))

/-- The index is the cardinal of the actual additive quotient. -/
noncomputable def orderIndex : ℕ :=
  Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸ orderImage a b c)

theorem finite_orderIndex_quotient (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    Finite (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸ orderImage a b c) := by
  letI := fractionNumberField a b c hD
  apply Submodule.finiteQuotientOfFreeOfRankEq
  rw [Module.finrank_eq_card_basis (orderImageBasis a b c),Fintype.card_fin,
    NumberField.RingOfIntegers.rank,fractionField_finrank_two a b c hD]

theorem orderIndex_pos (hD : b^2-4*a*c<0) : 0<orderIndex a b c := by
  letI := fractionNumberField a b c hD
  letI := finite_orderIndex_quotient a b c hD
  exact Nat.card_pos

/-- The actual quotient count equals the absolute integer basis determinant. -/
theorem orderIndex_eq_natAbs_det (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    orderIndex a b c=
      ((maximalOrderBasis a b c hD).det
        (fun i => (orderImageBasis a b c i :
          NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))))).natAbs := by
  letI := fractionNumberField a b c hD
  exact (Submodule.natAbs_det_basis_change (maximalOrderBasis a b c hD)
    (orderImage a b c) (orderImageBasis a b c)).symm

/-- Integer traces in the maximal order agree with the exact original order trace. -/
theorem trace_orderToRingOfIntegers (hD : b^2-4*a*c<0) (z : CoefficientOrder a b c) :
    letI := fractionNumberField a b c hD
    Algebra.trace ℤ (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))
      (orderToRingOfIntegers a b c z)=2*z.re+b*z.im := by
  letI := fractionNumberField a b c hD
  letI : Algebra ℤ (FractionRing (CoefficientOrder a b c)) := Ring.toIntAlgebra _
  apply Int.cast_injective (α := ℚ)
  have h := Algebra.trace_localization ℤ (Rₘ := ℚ) (Sₘ := FractionRing (CoefficientOrder a b c))
    (nonZeroDivisors ℤ) (orderToRingOfIntegers a b c z)
  change Algebra.trace ℚ _ (algebraMap _ (FractionRing (CoefficientOrder a b c)) z)=_ at h
  rw [algebraTrace_order_fraction a b c hD] at h
  simpa using h.symm

/-- The original basis discriminant computed INSIDE the maximal order. -/
theorem discr_orderImageBasis (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    Algebra.discr ℤ (fun i => (orderImageBasis a b c i :
      NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))))=b^2-4*a*c := by
  letI := fractionNumberField a b c hD
  have hm : Algebra.traceMatrix ℤ (fun i => (orderImageBasis a b c i :
      NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))))=
        !![2,b;b,b^2-2*a*c] := by
    ext i j
    rw [Algebra.traceMatrix_apply,Algebra.traceForm_apply,orderImageBasis_coe,orderImageBasis_coe,
      ← map_mul,trace_orderToRingOfIntegers a b c hD]
    fin_cases i <;> fin_cases j <;>
      simp [QuadraticAlgebra.basis,QuadraticAlgebra.linearEquivTuple,QuadraticAlgebra.equivProd]
    all_goals ring
  rw [Algebra.discr_def,hm]
  simp [Matrix.det_fin_two]
  ring

/-- The exact determinant-square comparison with the same number field. -/
theorem order_discriminant_eq_det_sq_mul_fieldDiscr (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    b^2-4*a*c=
      ((maximalOrderBasis a b c hD).det (fun i => (orderImageBasis a b c i :
        NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))))^2*
          NumberField.discr (FractionRing (CoefficientOrder a b c)) := by
  letI := fractionNumberField a b c hD
  let B := maximalOrderBasis a b c hD
  let v := fun i => (orderImageBasis a b c i :
    NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))
  have h := Algebra.discr_of_matrix_vecMul B (B.toMatrix v)
  rw [B.toMatrix_map_vecMul,NumberField.discr_eq_discr] at h
  rw [discr_orderImageBasis a b c hD] at h
  exact h

/-- The original order discriminant is the actual positive index squared
times the same number-field discriminant. No caller index certificate occurs. -/
theorem order_discriminant_eq_index_sq_mul_fieldDiscr (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    b^2-4*a*c=(orderIndex a b c : ℤ)^2*
      NumberField.discr (FractionRing (CoefficientOrder a b c)) := by
  letI := fractionNumberField a b c hD
  rw [orderIndex_eq_natAbs_det a b c hD,Int.natCast_natAbs,sq_abs]
  exact order_discriminant_eq_det_sq_mul_fieldDiscr a b c hD

theorem fieldDiscr_dvd_orderDiscriminant (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    NumberField.discr (FractionRing (CoefficientOrder a b c)) ∣ b^2-4*a*c := by
  letI := fractionNumberField a b c hD
  rw [order_discriminant_eq_index_sq_mul_fieldDiscr a b c hD]
  exact dvd_mul_left _ _

/-- Negativity is for the discriminant of the same number field, not a
substitution of the original order discriminant for it. -/
theorem fieldDiscr_neg (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    NumberField.discr (FractionRing (CoefficientOrder a b c))<0 := by
  letI := fractionNumberField a b c hD
  by_contra h
  have hnonneg := mul_nonneg (sq_nonneg (orderIndex a b c : ℤ)) (le_of_not_gt h)
  rw [← order_discriminant_eq_index_sq_mul_fieldDiscr a b c hD] at hnonneg
  omega

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The actual positive integer index of the original discriminant order
inside the maximal order of the same field. This is not yet a conductor. -/
noncomputable def binaryOrderIndex (K : PositiveDefiniteIntegralLattice 2) : ℕ := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact orderIndex 1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)

theorem binaryOrderIndex_pos (K : PositiveDefiniteIntegralLattice 2) : 0<K.binaryOrderIndex := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact orderIndex_pos _ _ _ K.binaryDiscriminantOrder_discriminant_neg

/-- The index counts the literal finite quotient by the original image. -/
theorem finite_binaryOrderQuotient (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    Finite (NumberField.RingOfIntegers (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ⧸
      orderImage 1 (K.binaryPrimitiveDiscriminant%2)
        (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact finite_orderIndex_quotient _ _ _ K.binaryDiscriminantOrder_discriminant_neg

/-- The original primitive discriminant is the actual index squared times
the same field discriminant. No maximality or caller index premise occurs. -/
theorem binaryPrimitiveDiscriminant_eq_orderIndex_sq_mul_fieldDiscr (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    K.binaryPrimitiveDiscriminant=(K.binaryOrderIndex : ℤ)^2*
      NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  have h := order_discriminant_eq_index_sq_mul_fieldDiscr _ _ _
    K.binaryDiscriminantOrder_discriminant_neg
  rw [discriminantOrder_coefficients _ K.binaryPrimitiveDiscriminant_mod_four] at h
  exact h

theorem binaryFieldDiscr_dvd_primitiveDiscriminant (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∣
      K.binaryPrimitiveDiscriminant := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  refine ⟨(K.binaryOrderIndex : ℤ)^2,?_⟩
  exact K.binaryPrimitiveDiscriminant_eq_orderIndex_sq_mul_fieldDiscr.trans (mul_comm _ _)

theorem binaryFieldDiscr_neg (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))<0 := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact fieldDiscr_neg _ _ _ K.binaryDiscriminantOrder_discriminant_neg

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.orderImage
#assert_standard_axioms BinaryNormIdeal.orderImageBasis
#assert_standard_axioms BinaryNormIdeal.orderImageBasis_coe
#assert_standard_axioms BinaryNormIdeal.maximalOrderBasis
#assert_standard_axioms BinaryNormIdeal.orderIndex
#assert_standard_axioms BinaryNormIdeal.finite_orderIndex_quotient
#assert_standard_axioms BinaryNormIdeal.orderIndex_pos
#assert_standard_axioms BinaryNormIdeal.orderIndex_eq_natAbs_det
#assert_standard_axioms BinaryNormIdeal.trace_orderToRingOfIntegers
#assert_standard_axioms BinaryNormIdeal.discr_orderImageBasis
#assert_standard_axioms BinaryNormIdeal.order_discriminant_eq_det_sq_mul_fieldDiscr
#assert_standard_axioms BinaryNormIdeal.order_discriminant_eq_index_sq_mul_fieldDiscr
#assert_standard_axioms BinaryNormIdeal.fieldDiscr_dvd_orderDiscriminant
#assert_standard_axioms BinaryNormIdeal.fieldDiscr_neg
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderIndex
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderIndex_pos
#assert_standard_axioms PositiveDefiniteIntegralLattice.finite_binaryOrderQuotient
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitiveDiscriminant_eq_orderIndex_sq_mul_fieldDiscr
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFieldDiscr_dvd_primitiveDiscriminant
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFieldDiscr_neg
