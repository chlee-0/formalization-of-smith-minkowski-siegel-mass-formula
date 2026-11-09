import SMSFormula.BinaryNumberField
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Imaginary signature and regulator of the actual binary field

Negative original polynomial discriminant excludes every real embedding.
The actual degree-two field therefore has signature (0,1), unit rank zero
and regulator one. No maximal-order or arbitrary-order class number is
identified here.
-/

namespace BinaryNormIdeal

/-- A negative-discriminant coefficient order admits no real ring map.
Neither a primitive polynomial nor an invertible ideal is required. -/
theorem no_real_order_hom (a b c : ℤ) (hD : b^2-4*a*c<0)
    (f : CoefficientOrder a b c →+* ℝ) : False := by
  let t : CoefficientOrder a b c := QuadraticAlgebra.omega
  have ht : t*t=(-a*c : ℤ)+(b : CoefficientOrder a b c)*t := by
    apply QuadraticAlgebra.ext <;> simp [t]
  have hh := congrArg f ht
  simp only [map_mul,map_add,map_neg,map_intCast,Int.cast_mul,Int.cast_neg] at hh
  have hn : (b : ℝ)^2-4*(a : ℝ)*(c : ℝ)<0 := by exact_mod_cast hD
  nlinarith [sq_nonneg (2*f t-(b : ℝ))]

variable (a b c : ℤ) [hO : IsDomain (CoefficientOrder a b c)]

omit hO in
/-- The original canonical fraction field has no real embedding. -/
theorem no_real_fraction_hom (hD : b^2-4*a*c<0)
    (f : FractionRing (CoefficientOrder a b c) →+* ℝ) : False :=
  no_real_order_hom a b c hD (f.comp (algebraMap _ _))

theorem fraction_nrRealPlaces_zero (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    NumberField.InfinitePlace.nrRealPlaces (FractionRing (CoefficientOrder a b c))=0 := by
  classical
  letI := fractionNumberField a b c hD
  letI : IsEmpty {w : NumberField.InfinitePlace (FractionRing (CoefficientOrder a b c)) //
      NumberField.InfinitePlace.IsReal w} :=
    ⟨fun w => no_real_fraction_hom a b c hD
      (NumberField.InfinitePlace.embedding_of_isReal w.property)⟩
  exact Fintype.card_eq_zero

theorem fraction_nrComplexPlaces_one (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    NumberField.InfinitePlace.nrComplexPlaces (FractionRing (CoefficientOrder a b c))=1 := by
  letI := fractionNumberField a b c hD
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
    (FractionRing (CoefficientOrder a b c))
  rw [fraction_nrRealPlaces_zero a b c hD,fractionField_finrank_two a b c hD] at h
  omega

theorem fraction_infinitePlace_card_one (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    Fintype.card (NumberField.InfinitePlace (FractionRing (CoefficientOrder a b c)))=1 := by
  letI := fractionNumberField a b c hD
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    fraction_nrRealPlaces_zero a b c hD,fraction_nrComplexPlaces_one a b c hD]

/-- The same field has unit rank zero (Dirichlet unit theorem). -/
theorem fraction_unitRank_zero (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    NumberField.Units.rank (FractionRing (CoefficientOrder a b c))=0 := by
  letI := fractionNumberField a b c hD
  rw [NumberField.Units.rank,fraction_infinitePlace_card_one a b c hD]

/-- Its regulator is exactly one, by the empty determinant. -/
theorem fraction_regulator_one (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    NumberField.Units.regulator (FractionRing (CoefficientOrder a b c))=1 := by
  classical
  letI := fractionNumberField a b c hD
  let E := FractionRing (CoefficientOrder a b c)
  haveI : Subsingleton (NumberField.InfinitePlace E) :=
    ⟨Fintype.card_le_one_iff.mp (by rw [fraction_infinitePlace_card_one a b c hD])⟩
  let w : NumberField.InfinitePlace E := NumberField.Units.dirichletUnitTheorem.w₀
  letI : IsEmpty {v : NumberField.InfinitePlace E // v ≠ w} :=
    ⟨fun v => v.property (Subsingleton.elim _ _)⟩
  rw [NumberField.Units.regulator_eq_det']
  simp only [Matrix.det_isEmpty,abs_one]

/-- Rank zero forces every unit of the actual maximal ring of integers
into its torsion subgroup. This does not identify units of the original order. -/
theorem fraction_torsion_eq_top (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    NumberField.Units.torsion (FractionRing (CoefficientOrder a b c))=⊤ := by
  letI := fractionNumberField a b c hD
  let E := FractionRing (CoefficientOrder a b c)
  letI : IsEmpty (Fin (NumberField.Units.rank E)) := by
    rw [fraction_unitRank_zero a b c hD]
    infer_instance
  have h := NumberField.Units.closure_fundSystem_sup_torsion_eq_top E
  rw [Set.range_eq_empty,Subgroup.closure_empty,bot_sup_eq] at h
  exact h

/-- All units of the same field's maximal ring of integers form a finite
carrier. No numerical unit classification or original-order equality occurs. -/
theorem fraction_finite_integerUnits (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    Finite (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))ˣ := by
  letI := fractionNumberField a b c hD
  let E := FractionRing (CoefficientOrder a b c)
  let f : (NumberField.RingOfIntegers E)ˣ → NumberField.Units.torsion E :=
    fun u => ⟨u,by rw [fraction_torsion_eq_top a b c hD]; trivial⟩
  exact Finite.of_injective f (fun _ _ h => congrArg Subtype.val h)

/-- The field torsion order equals its actual maximal-order unit count.
The original nonmaximal-order norm-one-unit count remains separate. -/
theorem fraction_torsionOrder_eq_card_integerUnits (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    NumberField.Units.torsionOrder (FractionRing (CoefficientOrder a b c))=
      Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))ˣ := by
  letI := fractionNumberField a b c hD
  rw [NumberField.Units.torsionOrder,← Nat.card_eq_fintype_card,
    fraction_torsion_eq_top a b c hD]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- No real embedding of the same field is possible for any actual binary lattice. -/
theorem binaryFraction_no_real_hom (K : PositiveDefiniteIntegralLattice 2)
    (f : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant) →+* ℝ) : False := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact no_real_fraction_hom _ _ _ K.binaryDiscriminantOrder_discriminant_neg f

theorem binaryFraction_nrRealPlaces_zero (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    NumberField.InfinitePlace.nrRealPlaces
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))=0 := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact fraction_nrRealPlaces_zero _ _ _ K.binaryDiscriminantOrder_discriminant_neg

theorem binaryFraction_nrComplexPlaces_one (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    NumberField.InfinitePlace.nrComplexPlaces
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))=1 := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact fraction_nrComplexPlaces_one _ _ _ K.binaryDiscriminantOrder_discriminant_neg

theorem binaryFraction_regulator_one (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    NumberField.Units.regulator (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))=1 := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact fraction_regulator_one _ _ _ K.binaryDiscriminantOrder_discriminant_neg

/-- The actual field torsion factor is the maximal-order unit count;
no equality with the original order's w_D is inferred. -/
theorem binaryFraction_torsionOrder_eq_card_integerUnits (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    NumberField.Units.torsionOrder (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))=
      Nat.card (NumberField.RingOfIntegers
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))ˣ := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact fraction_torsionOrder_eq_card_integerUnits _ _ _ K.binaryDiscriminantOrder_discriminant_neg

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.no_real_order_hom
#assert_standard_axioms BinaryNormIdeal.no_real_fraction_hom
#assert_standard_axioms BinaryNormIdeal.fraction_nrRealPlaces_zero
#assert_standard_axioms BinaryNormIdeal.fraction_nrComplexPlaces_one
#assert_standard_axioms BinaryNormIdeal.fraction_infinitePlace_card_one
#assert_standard_axioms BinaryNormIdeal.fraction_unitRank_zero
#assert_standard_axioms BinaryNormIdeal.fraction_regulator_one
#assert_standard_axioms BinaryNormIdeal.fraction_torsion_eq_top
#assert_standard_axioms BinaryNormIdeal.fraction_finite_integerUnits
#assert_standard_axioms BinaryNormIdeal.fraction_torsionOrder_eq_card_integerUnits
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFraction_no_real_hom
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFraction_nrRealPlaces_zero
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFraction_nrComplexPlaces_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFraction_regulator_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFraction_torsionOrder_eq_card_integerUnits
