import SMSFormula.BinaryClassNumber
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic

/-!
# The actual binary order inside its quadratic number field

The original FractionRing has degree two over the rationals. Its algebra
norm is the norm already used by the ideal proofs. The original order embeds
in the ring of integers; no maximality or conductor formula is assumed.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra

variable (a b c : ℤ) [hO : IsDomain (CoefficientOrder a b c)]

/-- The original rational coefficient equivalence respects rational scalars. -/
noncomputable def fractionRationalAlgEquiv (hD : b^2-4*a*c<0) :
    letI := fractionField_charZero a b c hD
    FractionRing (CoefficientOrder a b c) ≃ₐ[ℚ]
      CoefficientAlgebra (a : ℚ) (b : ℚ) (c : ℚ) := by
  letI := fractionField_charZero a b c hD
  letI := rationalField a b c hD
  refine { fractionRationalEquiv a b c hD with commutes' := ?_ }
  intro r
  change fractionRationalMap a b c hD (r : FractionRing (CoefficientOrder a b c))=_
  exact map_ratCast (fractionRationalMap a b c hD) r

/-- The original fraction field is a number field, without replacing its carrier. -/
theorem fractionNumberField (hD : b^2-4*a*c<0) :
    NumberField (FractionRing (CoefficientOrder a b c)) := by
  letI := fractionField_charZero a b c hD
  haveI : FiniteDimensional ℚ (FractionRing (CoefficientOrder a b c)) :=
    FiniteDimensional.of_injective (fractionRationalAlgEquiv a b c hD).toLinearMap
      (fractionRationalAlgEquiv a b c hD).injective
  exact ⟨⟩

/-- Its rational degree is exactly two. -/
theorem fractionField_finrank_two (hD : b^2-4*a*c<0) :
    letI := fractionField_charZero a b c hD
    Module.finrank ℚ (FractionRing (CoefficientOrder a b c))=2 := by
  letI := fractionField_charZero a b c hD
  rw [(fractionRationalAlgEquiv a b c hD).toLinearEquiv.finrank_eq]
  exact QuadraticAlgebra.finrank_eq_two _ _

/-- The explicit quadratic norm is the actual algebra norm. -/
theorem algebraNorm_eq_coefficientNorm {R : Type*} [CommRing R] (A B : R)
    (z : QuadraticAlgebra R A B) : Algebra.norm R z=z.norm := by
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

/-- The algebra trace includes the mixed coefficient, so the trace can be odd. -/
theorem algebraTrace_eq_coefficients {R : Type*} [CommRing R] (A B : R)
    (z : QuadraticAlgebra R A B) : Algebra.trace R _ z=2*z.re+B*z.im := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis A B)]
  simp [Matrix.trace,Fin.sum_univ_two,Algebra.leftMulMatrix_eq_repr_mul,
    QuadraticAlgebra.basis,QuadraticAlgebra.linearEquivTuple,QuadraticAlgebra.equivProd]
  ring

/-- The original field norm used by the genus proof is the algebra norm. -/
theorem algebraNorm_eq_fractionNorm (hD : b^2-4*a*c<0)
    (z : FractionRing (CoefficientOrder a b c)) :
    letI := fractionField_charZero a b c hD
    Algebra.norm ℚ z=fractionNorm a b c hD z := by
  letI := fractionField_charZero a b c hD
  rw [← Algebra.norm_eq_of_algEquiv (fractionRationalAlgEquiv a b c hD) z,
    algebraNorm_eq_coefficientNorm]
  rfl

/-- Exact field trace in the original rational coefficient coordinates. -/
theorem algebraTrace_eq_fractionCoefficients (hD : b^2-4*a*c<0)
    (z : FractionRing (CoefficientOrder a b c)) :
    letI := fractionField_charZero a b c hD
    Algebra.trace ℚ _ z=2*(fractionRationalMap a b c hD z).re+
      (b : ℚ)*(fractionRationalMap a b c hD z).im := by
  letI := fractionField_charZero a b c hD
  rw [← Algebra.trace_eq_of_algEquiv (fractionRationalAlgEquiv a b c hD) z,
    algebraTrace_eq_coefficients]
  rfl

omit hO in
/-- Every original order element is integral in the actual fraction field,
with the canonical integer algebra used by the ring of integers. -/
theorem isIntegral_order_fraction (z : CoefficientOrder a b c) :
    letI : Algebra ℤ (FractionRing (CoefficientOrder a b c)) := Ring.toIntAlgebra _
    IsIntegral ℤ (algebraMap (CoefficientOrder a b c)
      (FractionRing (CoefficientOrder a b c)) z) := by
  letI : Algebra ℤ (FractionRing (CoefficientOrder a b c)) := Ring.toIntAlgebra _
  exact map_isIntegral_int (algebraMap (CoefficientOrder a b c)
    (FractionRing (CoefficientOrder a b c))) (IsIntegral.of_finite ℤ z)

/-- The original order embeds into the ring of integers of the same field. -/
noncomputable def orderToRingOfIntegers :
    CoefficientOrder a b c →ₐ[ℤ]
      NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) where
  toFun z := ⟨algebraMap _ _ z,by
    exact isIntegral_order_fraction a b c z⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' z w := by apply Subtype.ext; exact map_mul _ z w
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' z w := by apply Subtype.ext; exact map_add _ z w
  commutes' r := by apply Subtype.ext; exact (map_intCast (algebraMap (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c))) r)

/-- The embedding keeps the original coordinate element in the original field. -/
theorem orderToRingOfIntegers_coe (z : CoefficientOrder a b c) :
    ((orderToRingOfIntegers a b c z : NumberField.RingOfIntegers
      (FractionRing (CoefficientOrder a b c))) : FractionRing (CoefficientOrder a b c))=
      algebraMap _ _ z := rfl

theorem orderToRingOfIntegers_injective : Function.Injective (orderToRingOfIntegers a b c) := by
  intro z w h
  apply IsFractionRing.injective (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c))
  exact congrArg (fun x : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) =>
    (x : FractionRing (CoefficientOrder a b c))) h

/-- The field norm of an original integral element is its original integer norm. -/
theorem algebraNorm_order_fraction (hD : b^2-4*a*c<0) (z : CoefficientOrder a b c) :
    letI := fractionField_charZero a b c hD
    Algebra.norm ℚ (algebraMap _ (FractionRing (CoefficientOrder a b c)) z)=(z.norm : ℚ) := by
  letI := fractionField_charZero a b c hD
  rw [algebraNorm_eq_fractionNorm a b c hD,fractionNorm_algebraMap]

/-- The field trace of an original order element is the exact integer trace. -/
theorem algebraTrace_order_fraction (hD : b^2-4*a*c<0) (z : CoefficientOrder a b c) :
    letI := fractionField_charZero a b c hD
    Algebra.trace ℚ _ (algebraMap _ (FractionRing (CoefficientOrder a b c)) z)=
      ((2*z.re+b*z.im : ℤ) : ℚ) := by
  letI := fractionField_charZero a b c hD
  rw [algebraTrace_eq_fractionCoefficients a b c hD,fractionRationalMap_algebraMap]
  simp [rationalMap]

/-- The trace-pairing matrix of the original integer basis 1,theta, in
the actual fraction field. It is not a maximal-order integral basis claim. -/
noncomputable def orderFractionTraceMatrix (hD : b^2-4*a*c<0) : Matrix (Fin 2) (Fin 2) ℚ := by
  letI := fractionField_charZero a b c hD
  exact fun i j => Algebra.trace ℚ (FractionRing (CoefficientOrder a b c))
    (algebraMap _ _ ((QuadraticAlgebra.basis (-a*c) b i)*(QuadraticAlgebra.basis (-a*c) b j)))

theorem orderFractionTraceMatrix_eq (hD : b^2-4*a*c<0) :
    orderFractionTraceMatrix a b c hD=!![2,(b : ℚ);(b : ℚ),(b : ℚ)^2-2*(a : ℚ)*(c : ℚ)] := by
  letI := fractionField_charZero a b c hD
  ext i j
  dsimp only [orderFractionTraceMatrix]
  rw [algebraTrace_order_fraction a b c hD]
  fin_cases i <;> fin_cases j <;>
    simp [QuadraticAlgebra.basis,QuadraticAlgebra.linearEquivTuple,QuadraticAlgebra.equivProd]
  all_goals ring

/-- The original order-basis trace discriminant is b squared minus 4ac. -/
theorem orderFractionTraceMatrix_det (hD : b^2-4*a*c<0) :
    (orderFractionTraceMatrix a b c hD).det=((b^2-4*a*c : ℤ) : ℚ) := by
  simp [orderFractionTraceMatrix_eq,Matrix.det_fin_two]
  ring

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The same canonical fraction field of the actual primitive discriminant
order is a number field, even when the order is nonmaximal. -/
theorem binaryFractionNumberField (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    NumberField (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact fractionNumberField _ _ _ K.binaryDiscriminantOrder_discriminant_neg

theorem binaryFractionField_finrank_two (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    Module.finrank ℚ (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))=2 := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  exact fractionField_finrank_two _ _ _ K.binaryDiscriminantOrder_discriminant_neg

/-- The actual norm used by the kernel proof is the number-field algebra norm. -/
theorem binaryFractionNorm_eq_algebraNorm (K : PositiveDefiniteIntegralLattice 2)
    (z : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    K.binaryFractionNorm z=Algebra.norm ℚ z := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  exact (algebraNorm_eq_fractionNorm _ _ _ K.binaryDiscriminantOrder_discriminant_neg z).symm

/-- The original order embeds into the ring of integers of its same field.
No surjectivity, maximality or conductor value is asserted. -/
noncomputable def binaryOrderToRingOfIntegers (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    DiscriminantOrder K.binaryPrimitiveDiscriminant →ₐ[ℤ]
      NumberField.RingOfIntegers (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact orderToRingOfIntegers _ _ _

theorem binaryOrderToRingOfIntegers_injective (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Function.Injective K.binaryOrderToRingOfIntegers := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact orderToRingOfIntegers_injective _ _ _

/-- The trace discriminant of the original order basis is the actual
primitive D. It is not identified with the number field discriminant. -/
theorem binaryOrder_traceDiscriminant (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    (orderFractionTraceMatrix 1 (K.binaryPrimitiveDiscriminant%2)
      (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
      K.binaryDiscriminantOrder_discriminant_neg).det=(K.binaryPrimitiveDiscriminant : ℚ) := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [orderFractionTraceMatrix_det,discriminantOrder_coefficients _ K.binaryPrimitiveDiscriminant_mod_four]

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.fractionRationalAlgEquiv
#assert_standard_axioms BinaryNormIdeal.fractionNumberField
#assert_standard_axioms BinaryNormIdeal.fractionField_finrank_two
#assert_standard_axioms BinaryNormIdeal.algebraNorm_eq_coefficientNorm
#assert_standard_axioms BinaryNormIdeal.algebraTrace_eq_coefficients
#assert_standard_axioms BinaryNormIdeal.algebraNorm_eq_fractionNorm
#assert_standard_axioms BinaryNormIdeal.algebraTrace_eq_fractionCoefficients
#assert_standard_axioms BinaryNormIdeal.isIntegral_order_fraction
#assert_standard_axioms BinaryNormIdeal.orderToRingOfIntegers
#assert_standard_axioms BinaryNormIdeal.orderToRingOfIntegers_coe
#assert_standard_axioms BinaryNormIdeal.orderToRingOfIntegers_injective
#assert_standard_axioms BinaryNormIdeal.algebraNorm_order_fraction
#assert_standard_axioms BinaryNormIdeal.algebraTrace_order_fraction
#assert_standard_axioms BinaryNormIdeal.orderFractionTraceMatrix
#assert_standard_axioms BinaryNormIdeal.orderFractionTraceMatrix_eq
#assert_standard_axioms BinaryNormIdeal.orderFractionTraceMatrix_det
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionNumberField
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionField_finrank_two
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionNorm_eq_algebraNorm
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderToRingOfIntegers
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderToRingOfIntegers_injective
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrder_traceDiscriminant
