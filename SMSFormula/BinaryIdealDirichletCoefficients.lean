import SMSFormula.BinaryNormIdealCounts

/-!
# Ideal coefficients as a Dirichlet convolution

The field prime signs extend completely multiplicatively. They are not
asserted to be a periodic or primitive Dirichlet character. The separate
product-side character keeps its bad-prime mask.
-/

open scoped ArithmeticFunction.zeta

namespace BinaryNormIdeal

/-- The multiplicative extension of the same field prime signs. -/
noncomputable def fieldSignExtension (d : ℤ) : ℕ →*₀ ℂ where
  toFun n := if n=0 then 0 else n.factorization.prod
    (fun p k => (conductorPrimeSign d p : ℂ)^k)
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m=0
    · simp [hm]
    by_cases hn : n=0
    · simp [hn]
    simp only [if_neg hm,if_neg hn,if_neg (mul_ne_zero hm hn),Nat.factorization_mul hm hn]
    exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

/-- Its values on all prime powers include exponent zero. -/
theorem fieldSignExtension_prime_pow (d : ℤ) (p k : ℕ) [Fact p.Prime] :
    fieldSignExtension d (p^k)=(conductorPrimeSign d p : ℂ)^k := by
  rw [map_pow]
  congr 1
  simp [fieldSignExtension,(Fact.out : p.Prime).ne_zero,(Fact.out : p.Prime).factorization]

/-- Every field prime sign has complex norm at most one. -/
theorem conductorPrimeSign_norm_le_one (d : ℤ) (p : ℕ) :
    ‖(conductorPrimeSign d p : ℂ)‖ ≤ 1 := by
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    rcases conductorPrimeSign_trichotomy d p with h | h | h <;> rw [h] <;> norm_num
  · simp [conductorPrimeSign,hp]

/-- The extension is bounded even at zero. -/
theorem fieldSignExtension_norm_le_one (d : ℤ) (n : ℕ) : ‖fieldSignExtension d n‖ ≤ 1 := by
  by_cases hn : n=0
  · simp [hn]
  change ‖if n=0 then (0 : ℂ) else _‖ ≤ 1
  rw [if_neg hn,Nat.prod_factorization_eq_prod_primeFactors,norm_prod]
  apply Finset.prod_le_one
  · intro p _
    exact norm_nonneg _
  · intro p _
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (conductorPrimeSign_norm_le_one d p)

/-- The extension on the normalized arithmetic-function carrier. -/
noncomputable def fieldSignArithmetic (d : ℤ) : ArithmeticFunction ℂ where
  toFun := fieldSignExtension d
  map_zero' := map_zero _

theorem fieldSignArithmetic_isMultiplicative (d : ℤ) :
    (fieldSignArithmetic d).IsMultiplicative :=
  ⟨map_one (fieldSignExtension d),fun _ => map_mul (fieldSignExtension d) _ _⟩

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The actual all-ideal sequence, normalized only at zero. -/
noncomputable def maximalNormArithmetic (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    ArithmeticFunction ℂ := by
  letI := fractionNumberField a b c hD
  exact toArithmeticFunction (fun n => (Nat.card {J : Ideal (NumberField.RingOfIntegers
    (FractionRing (CoefficientOrder a b c))) // Ideal.absNorm J=n} : ℂ))

theorem maximalNormArithmetic_apply (hD : b^2-4*a*c<0) (n : ℕ) (hn : n ≠ 0) :
    letI := fractionNumberField a b c hD
    maximalNormArithmetic a b c hD n =
      (Nat.card {J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
        Ideal.absNorm J=n} : ℂ) := by
  letI := fractionNumberField a b c hD
  simp [maximalNormArithmetic,toArithmeticFunction,hn]

theorem maximalNormArithmetic_isMultiplicative (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    (maximalNormArithmetic a b c hD).IsMultiplicative := by
  letI := fractionNumberField a b c hD
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · rw [maximalNormArithmetic_apply a b c hD 1 one_ne_zero,card_normIdeals_one]
    norm_num
  · intro m n hm hn hmn
    rw [maximalNormArithmetic_apply a b c hD (m*n) (mul_ne_zero hm hn),
      maximalNormArithmetic_apply a b c hD m hm,maximalNormArithmetic_apply a b c hD n hn,
      card_maximalNormIdeals_mul_of_coprime a b c hD m n hm hn hmn,Nat.cast_mul]

/-- Actual coefficient equality as arithmetic functions, with both
sides normalized at zero. No periodic-character premise is supplied. -/
theorem maximalNormArithmetic_eq_zeta_mul_fieldSign (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    maximalNormArithmetic a b c hD =
      (ζ : ArithmeticFunction ℂ) *
        fieldSignArithmetic (NumberField.discr (FractionRing (CoefficientOrder a b c))) := by
  letI := fractionNumberField a b c hD
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (maximalNormArithmetic_isMultiplicative a b c hD) _
    (ArithmeticFunction.isMultiplicative_zeta.natCast.mul (fieldSignArithmetic_isMultiplicative _))).mpr
  intro p k hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [maximalNormArithmetic_apply a b c hD (p^k) (pow_ne_zero k hp.ne_zero),
    ArithmeticFunction.coe_zeta_mul_apply,Nat.divisors_prime_pow hp,
    Finset.sum_map]
  change (Nat.card _ : ℂ) = ∑ j ∈ Finset.range (k+1),fieldSignExtension _ (p^j)
  simp only [fieldSignExtension_prime_pow]
  exact_mod_cast card_maximalNormPrimePowerIdeals a b c hD p k

/-- The literal all-ideal coefficient equals the divisor sum away from
zero. The zero ideal is not silently dropped from the literal sequence. -/
theorem card_maximalNormIdeals_eq_divisor_sum (hD : b^2-4*a*c<0)
    (n : ℕ) (hn : n ≠ 0) :
    letI := fractionNumberField a b c hD
    (Nat.card {J : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) //
      Ideal.absNorm J=n} : ℂ) =
        ∑ r ∈ n.divisors,fieldSignExtension
          (NumberField.discr (FractionRing (CoefficientOrder a b c))) r := by
  letI := fractionNumberField a b c hD
  rw [← maximalNormArithmetic_apply a b c hD n hn,
    maximalNormArithmetic_eq_zeta_mul_fieldSign a b c hD,ArithmeticFunction.coe_zeta_mul_apply]
  rfl

/-- Native convolution gives the same field's genuine zeta function
as zeta(s) times the L-series of the bounded field-sign extension. -/
theorem dedekindZeta_eq_riemannZeta_mul_fieldSignLSeries (hD : b^2-4*a*c<0)
    (s : ℂ) (hs : 1 < s.re) :
    letI := fractionNumberField a b c hD
    NumberField.dedekindZeta (FractionRing (CoefficientOrder a b c)) s =
      riemannZeta s * LSeries (fieldSignExtension
        (NumberField.discr (FractionRing (CoefficientOrder a b c)))) s := by
  letI := fractionNumberField a b c hD
  let d := NumberField.discr (FractionRing (CoefficientOrder a b c))
  have he : NumberField.dedekindZeta (FractionRing (CoefficientOrder a b c)) s =
      LSeries (maximalNormArithmetic a b c hD) s := by
    apply LSeries_congr (fun {n} hn => (maximalNormArithmetic_apply a b c hD n hn).symm) s
  have hz : LSeriesSummable (ζ : ArithmeticFunction ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hf : LSeriesSummable (fieldSignArithmetic d) s :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => fieldSignExtension_norm_le_one d n) hs
  have hconv := ArithmeticFunction.LSeries_mul' hz hf
  rw [he,maximalNormArithmetic_eq_zeta_mul_fieldSign a b c hD]
  change LSeries (⇑((ζ : ArithmeticFunction ℂ)*fieldSignArithmetic d)) s =
    riemannZeta s*LSeries (fieldSignExtension d) s
  rw [hconv]
  have hzeta : LSeries (ζ : ArithmeticFunction ℂ) s = riemannZeta s := by
    rw [← LSeries_one_eq_riemannZeta hs]
    apply LSeries_congr
    intro n hn
    simp [hn]
  rw [hzeta]
  rfl

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.fieldSignExtension
#assert_standard_axioms BinaryNormIdeal.fieldSignExtension_prime_pow
#assert_standard_axioms BinaryNormIdeal.conductorPrimeSign_norm_le_one
#assert_standard_axioms BinaryNormIdeal.fieldSignExtension_norm_le_one
#assert_standard_axioms BinaryNormIdeal.fieldSignArithmetic
#assert_standard_axioms BinaryNormIdeal.fieldSignArithmetic_isMultiplicative
#assert_standard_axioms BinaryNormIdeal.maximalNormArithmetic
#assert_standard_axioms BinaryNormIdeal.maximalNormArithmetic_apply
#assert_standard_axioms BinaryNormIdeal.maximalNormArithmetic_isMultiplicative
#assert_standard_axioms BinaryNormIdeal.maximalNormArithmetic_eq_zeta_mul_fieldSign
#assert_standard_axioms BinaryNormIdeal.card_maximalNormIdeals_eq_divisor_sum
#assert_standard_axioms BinaryNormIdeal.dedekindZeta_eq_riemannZeta_mul_fieldSignLSeries
