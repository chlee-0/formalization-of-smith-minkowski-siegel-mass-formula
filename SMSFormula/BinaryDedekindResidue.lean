import SMSFormula.BinaryConductorEulerFactors
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# The binary mass and the Dedekind residue of the same field

The analytic class-number formula supplies a zeta limit.
The conductor correction and genus factor keep their own carriers.
Identification with a quadratic Dirichlet L-value is a separate step.
-/

open Filter Topology

namespace BinaryNormIdeal

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The native residue formula on the same imaginary quadratic field,
with its actual maximal ClassGroup and unit carrier. -/
theorem fraction_dedekindZeta_residue_eq (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    let E := FractionRing (CoefficientOrder a b c)
    NumberField.dedekindZeta_residue E =
      (2*Real.pi*(Nat.card (ClassGroup (NumberField.RingOfIntegers E)) : ℝ)) /
        ((Nat.card (NumberField.RingOfIntegers E)ˣ : ℝ)*
          Real.sqrt |(NumberField.discr E : ℝ)|) := by
  letI := fractionNumberField a b c hD
  dsimp only
  rw [NumberField.dedekindZeta_residue_def,
    fraction_nrRealPlaces_zero a b c hD,fraction_nrComplexPlaces_one a b c hD,
    fraction_regulator_one a b c hD,fraction_torsionOrder_eq_card_integerUnits a b c hD]
  simp only [pow_zero,pow_one,one_mul,mul_one,NumberField.classNumber,Nat.card_eq_fintype_card]

/-- The same maximal class-number/unit ratio equals its genuine Dedekind
residue times the exact imaginary quadratic archimedean factor. -/
theorem classNumber_div_integerUnits_eq_dedekindZeta_residue (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    let E := FractionRing (CoefficientOrder a b c)
    (Nat.card (ClassGroup (NumberField.RingOfIntegers E)) : ℝ) /
        (Nat.card (NumberField.RingOfIntegers E)ˣ : ℝ) =
      Real.sqrt |(NumberField.discr E : ℝ)|/(2*Real.pi)*NumberField.dedekindZeta_residue E := by
  letI := fractionNumberField a b c hD
  have hd : Real.sqrt |(NumberField.discr (FractionRing (CoefficientOrder a b c)) : ℝ)| ≠ 0 :=
    ne_of_gt (Real.sqrt_pos_of_pos (abs_pos.mpr
      (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))))
  dsimp only
  rw [fraction_dedekindZeta_residue_eq a b c hD]
  field_simp

/-- The original order square root absorbs its actual positive index.
This is the same field discriminant identity, including nonmaximal orders. -/
theorem sqrt_orderDiscriminant_eq_index_mul_sqrt_fieldDiscr (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    Real.sqrt |((b^2-4*a*c : ℤ) : ℝ)| =
      (orderIndex a b c : ℝ)*
        Real.sqrt |(NumberField.discr (FractionRing (CoefficientOrder a b c)) : ℝ)| := by
  letI := fractionNumberField a b c hD
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (order_discriminant_eq_index_sq_mul_fieldDiscr a b c hD)
  dsimp only at h
  rw [h]
  push_cast
  rw [abs_mul,abs_sq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)]

/-- The unit-weighted class count in terms of an analytic residue. The
conductor product uses the prime signs of the same field. -/
theorem classNumber_div_orderUnits_eq_dedekindZeta_residue (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    let E := FractionRing (CoefficientOrder a b c)
    (Nat.card (ClassGroup (CoefficientOrder a b c)) : ℝ)/Nat.card (CoefficientOrder a b c)ˣ =
      Real.sqrt |((b^2-4*a*c : ℤ) : ℝ)|/(2*Real.pi)*NumberField.dedekindZeta_residue E *
        ∏ p ∈ (orderIndex a b c).primeFactors,
          (1-(conductorPrimeSign (NumberField.discr E) p : ℝ)/(p : ℝ)) := by
  letI := fractionNumberField a b c hD
  have h := congrArg (fun q : ℚ => (q : ℝ))
    (classNumber_div_orderUnits_eq_maximal_mul_conductor_euler_product a b c hD)
  push_cast at h
  rw [h,classNumber_div_integerUnits_eq_dedekindZeta_residue a b c hD,
    sqrt_orderDiscriminant_eq_index_mul_sqrt_fieldDiscr a b c hD]
  ring

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The original full-O mass equals the genuine same-field residue with
its conductor and actual class-group two-torsion factor. -/
theorem ordinaryGenusMass_eq_dedekindZeta_residue (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    let O := DiscriminantOrder K.binaryPrimitiveDiscriminant
    let E := FractionRing O
    ((ordinaryGenusMass K : ℚ) : ℝ) =
      Real.sqrt |(K.binaryPrimitiveDiscriminant : ℝ)| /
        (4*Real.pi*(Nat.card (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker : ℝ)) *
          NumberField.dedekindZeta_residue E *
            ∏ p ∈ K.binaryOrderIndex.primeFactors,
              (1-(conductorPrimeSign (NumberField.discr E) p : ℝ)/(p : ℝ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  dsimp only
  have h := classNumber_div_orderUnits_eq_dedekindZeta_residue _ _ _
    K.binaryDiscriminantOrder_discriminant_neg
  dsimp only at h
  rw [discriminantOrder_coefficients _ K.binaryPrimitiveDiscriminant_mod_four] at h
  have hm := congrArg (fun q : ℚ => (q : ℝ))
    K.ordinaryGenusMass_eq_classNumber_div_two_orderUnits_twoTorsion
  push_cast at hm
  rw [hm]
  calc
    _ = ((Nat.card (ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)) : ℝ) /
        (Nat.card (DiscriminantOrder K.binaryPrimitiveDiscriminant)ˣ : ℝ)) /
          (2*(Nat.card (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
            ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker : ℝ)) := by
      rw [div_div]
      congr 1
      ring
    _ = _ := by
      rw [h]
      dsimp only [binaryOrderIndex]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

/-- A genuine one-sided analytic limit for the original ordinary mass.
The variable zeta function is the same canonical field's ideal L-series.
No quadratic L-value or caller analytic certificate is assumed. -/
theorem tendsto_dedekindZeta_scaled_ordinaryGenusMass (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    let O := DiscriminantOrder K.binaryPrimitiveDiscriminant
    let E := FractionRing O
    Tendsto (fun s : ℝ => ((s-1)*NumberField.dedekindZeta E s).re *
      (Real.sqrt |(K.binaryPrimitiveDiscriminant : ℝ)| /
        (4*Real.pi*(Nat.card (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker : ℝ))) *
          ∏ p ∈ K.binaryOrderIndex.primeFactors,
            (1-(conductorPrimeSign (NumberField.discr E) p : ℝ)/(p : ℝ)))
      (𝓝[>] 1) (𝓝 ((ordinaryGenusMass K : ℚ) : ℝ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  dsimp only
  have hz := Complex.continuous_re.continuousAt.tendsto.comp
    (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))
  simp only [Complex.ofReal_re] at hz
  have h := (hz.mul_const (Real.sqrt |(K.binaryPrimitiveDiscriminant : ℝ)| /
    (4*Real.pi*(Nat.card (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker : ℝ)))).mul_const
        (∏ p ∈ K.binaryOrderIndex.primeFactors,
          (1-(conductorPrimeSign (NumberField.discr
            (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℝ)/(p : ℝ)))
  convert h using 1
  rw [K.ordinaryGenusMass_eq_dedekindZeta_residue]
  congr 1
  ring

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.fraction_dedekindZeta_residue_eq
#assert_standard_axioms BinaryNormIdeal.classNumber_div_integerUnits_eq_dedekindZeta_residue
#assert_standard_axioms BinaryNormIdeal.sqrt_orderDiscriminant_eq_index_mul_sqrt_fieldDiscr
#assert_standard_axioms BinaryNormIdeal.classNumber_div_orderUnits_eq_dedekindZeta_residue

#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_dedekindZeta_residue
#assert_standard_axioms PositiveDefiniteIntegralLattice.tendsto_dedekindZeta_scaled_ordinaryGenusMass
