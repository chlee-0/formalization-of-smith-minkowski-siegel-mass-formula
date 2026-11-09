import SMSFormula.BinaryOddResidueUnits
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Actual conductor residue products

CRT acts on the literal scalar quotients. Positive index factorization and
the actual prime-power counts evaluate the original residue-unit quotient.
-/

namespace BinaryNormIdeal

/-- Actual CRT multiplicativity of scalar residue-unit counts. -/
theorem card_scalarQuotient_units_mul {B : Type*} [CommRing B]
    (m n : ℕ) (h : m.Coprime n) :
    Nat.card (B ⧸ Ideal.span {((m*n : ℕ) : B)})ˣ =
      Nat.card (B ⧸ Ideal.span {(m : B)})ˣ * Nat.card (B ⧸ Ideal.span {(n : B)})ˣ := by
  have hc : IsCoprime (Ideal.span {(m : B)}) (Ideal.span {(n : B)}) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    simpa only [map_natCast] using IsCoprime.map (Nat.Coprime.isCoprime h) (Int.castRingHom B)
  have hi : Ideal.span {((m*n : ℕ) : B)} =
      Ideal.span {(m : B)} * Ideal.span {(n : B)} := by
    rw [Ideal.span_singleton_mul_span_singleton,Nat.cast_mul]
  let e := (Ideal.quotEquivOfEq hi).trans (Ideal.quotientMulEquivQuotientProd _ _ hc)
  have he := Nat.card_congr ((Units.mapEquiv e.toMulEquiv).toEquiv.trans (MulEquiv.prodUnits).toEquiv)
  simpa only [Nat.card_prod] using he

/-- Every nonzero scalar residue-unit count is the product of its actual
prime-power residue-unit counts. The modulus-one product is empty. -/
theorem card_scalarQuotient_units_factorization {B : Type*} [CommRing B]
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (B ⧸ Ideal.span {(n : B)})ˣ =
      ∏ p ∈ n.primeFactors, Nat.card (B ⧸ Ideal.span {((p^(n.factorization p) : ℕ) : B)})ˣ := by
  have h1 : Nat.card (B ⧸ Ideal.span {((1 : ℕ) : B)})ˣ = 1 := by
    have hi : (Ideal.span {((1 : ℕ) : B)} : Ideal B)=⊤ := by simp
    rw [hi]
    exact Nat.card_unique
  have h := Nat.multiplicative_factorization
    (fun n : ℕ => Nat.card (B ⧸ Ideal.span {(n : B)})ˣ)
    (fun m n h => card_scalarQuotient_units_mul m n h) h1 hn
  exact h

/-- The standard prime residue sign as a total arithmetic function. At
primes it is chi8(d) at two and the field Legendre symbol otherwise;
its value zero at nonprimes is irrelevant to all factor products. -/
noncomputable def conductorPrimeSign (d : ℤ) (p : ℕ) : ℤ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    if p=2 then ZMod.χ₈ (d : ZMod 8) else legendreSym p d
  else 0

theorem conductorPrimeSign_eq (d : ℤ) (p : ℕ) [Fact p.Prime] :
    conductorPrimeSign d p=if p=2 then ZMod.χ₈ (d : ZMod 8) else legendreSym p d := by
  simp only [conductorPrimeSign,dif_pos (Fact.out : p.Prime)]

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- CRT evaluates the literal maximal conductor residue numerator. Each
factor uses the same field discriminant, including the actual dyadic sign. -/
theorem card_conductorResidueUnits_eq_prime_product (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    (Nat.card (ConductorResidueUnits a b c) : ℤ) =
      ∏ p ∈ (orderIndex a b c).primeFactors,
        ((p : ℤ)-1)*((p : ℤ)-conductorPrimeSign (NumberField.discr (FractionRing (CoefficientOrder a b c))) p) *
            (p : ℤ)^(2*((orderIndex a b c).factorization p-1)) := by
  letI := fractionNumberField a b c hD
  change (Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸
    orderConductor a b c)ˣ : ℤ)=_
  rw [orderConductor_eq_span_index a b c hD,
    card_scalarQuotient_units_factorization _ (ne_of_gt (orderIndex_pos a b c hD)),Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hk : (orderIndex a b c).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hpow : ((p^((orderIndex a b c).factorization p) : ℕ) :
      NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) =
        (p : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))^((orderIndex a b c).factorization p) :=
    Nat.cast_pow _ _
  rw [hpow]
  simpa only [conductorPrimeSign_eq] using
    card_maximalOrderResidueUnits_prime_power a b c hD p _ hk

/-- The quotient cardinal has the evaluated integral Euler factors, viewed in Q
to allow subtraction of the standard quadratic signs. -/
theorem card_conductorResidueQuotient_eq_euler_factors (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    (Nat.card (ConductorResidueUnitQuotient a b c) : ℚ) =
      ∏ p ∈ (orderIndex a b c).primeFactors,
        (p : ℚ)^((orderIndex a b c).factorization p-1) *
          ((p : ℚ)-(conductorPrimeSign (NumberField.discr (FractionRing (CoefficientOrder a b c))) p : ℚ)) := by
  letI := fractionNumberField a b c hD
  let I := orderIndex a b c
  have hn : I ≠ 0 := ne_of_gt (orderIndex_pos a b c hD)
  rw [card_conductorResidueQuotient_rat_eq_div_totient a b c hD]
  have hnum := congrArg (fun z : ℤ => (z : ℚ)) (card_conductorResidueUnits_eq_prime_product a b c hD)
  push_cast at hnum
  rw [hnum,Nat.totient_eq_prod_factorization hn]
  change (∏ p ∈ I.primeFactors, _) / ((I.factorization.prod fun p k => p^(k-1)*(p-1) : ℕ) : ℚ)=_
  rw [Nat.prod_factorization_eq_prod_primeFactors,Nat.cast_prod,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hp1 : (p : ℚ)-1 ≠ 0 := by
    have hgt : (1 : ℚ) < p := by exact_mod_cast hprime.one_lt
    linarith
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hprime.one_le,Nat.cast_one,
    mul_comm 2 (I.factorization p-1),pow_mul]
  change _ = (p : ℚ)^(I.factorization p-1)*_
  field_simp

/-- The integral form of the exact quotient count. -/
theorem card_conductorResidueQuotient_int_eq_euler_factors (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    (Nat.card (ConductorResidueUnitQuotient a b c) : ℤ) =
      ∏ p ∈ (orderIndex a b c).primeFactors,
        (p : ℤ)^((orderIndex a b c).factorization p-1) *
          ((p : ℤ)-conductorPrimeSign (NumberField.discr (FractionRing (CoefficientOrder a b c))) p) := by
  letI := fractionNumberField a b c hD
  exact_mod_cast card_conductorResidueQuotient_eq_euler_factors a b c hD

/-- Rational Euler display for the same actual conductor quotient. -/
theorem card_conductorResidueQuotient_eq_index_mul_euler_product (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    (Nat.card (ConductorResidueUnitQuotient a b c) : ℚ) =
      (orderIndex a b c : ℚ) * ∏ p ∈ (orderIndex a b c).primeFactors,
        (1-(conductorPrimeSign (NumberField.discr (FractionRing (CoefficientOrder a b c))) p : ℚ)/(p : ℚ)) := by
  letI := fractionNumberField a b c hD
  let I := orderIndex a b c
  have hn : I ≠ 0 := ne_of_gt (orderIndex_pos a b c hD)
  have hI : (I : ℚ)=∏ p ∈ I.primeFactors, (p : ℚ)^(I.factorization p) := by
    have h := Nat.prod_factorization_pow_eq_self hn
    rw [Nat.prod_factorization_eq_prod_primeFactors] at h
    exact_mod_cast h.symm
  rw [card_conductorResidueQuotient_eq_euler_factors a b c hD]
  change (∏ p ∈ I.primeFactors, _ ) = (I : ℚ)*(∏ p ∈ I.primeFactors, _)
  rw [hI,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hk : I.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [hk,Nat.succ_sub_one,pow_succ]
  field_simp

/-- Evaluated conductor class-number/unit correction. The maximal class
number and its unit count remain actual; no analytic formula is assumed. -/
theorem classNumber_div_orderUnits_eq_maximal_mul_conductor_euler_product (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    (Nat.card (ClassGroup (CoefficientOrder a b c)) : ℚ)/Nat.card (CoefficientOrder a b c)ˣ =
      ((Nat.card (ClassGroup (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))) : ℚ)/
        Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))ˣ) *
          ((orderIndex a b c : ℚ)*∏ p ∈ (orderIndex a b c).primeFactors,
            (1-(conductorPrimeSign (NumberField.discr (FractionRing (CoefficientOrder a b c))) p : ℚ)/(p : ℚ))) := by
  letI := fractionNumberField a b c hD
  rw [classNumber_div_orderUnits_eq_maximalClassNumber_div_units_mul_residueQuotient a b c hD,
    card_conductorResidueQuotient_eq_index_mul_euler_product a b c hD]

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.card_scalarQuotient_units_mul
#assert_standard_axioms BinaryNormIdeal.card_scalarQuotient_units_factorization
#assert_standard_axioms BinaryNormIdeal.conductorPrimeSign
#assert_standard_axioms BinaryNormIdeal.conductorPrimeSign_eq
#assert_standard_axioms BinaryNormIdeal.card_conductorResidueUnits_eq_prime_product
#assert_standard_axioms BinaryNormIdeal.card_conductorResidueQuotient_eq_euler_factors
#assert_standard_axioms BinaryNormIdeal.card_conductorResidueQuotient_int_eq_euler_factors
#assert_standard_axioms BinaryNormIdeal.card_conductorResidueQuotient_eq_index_mul_euler_product
#assert_standard_axioms BinaryNormIdeal.classNumber_div_orderUnits_eq_maximal_mul_conductor_euler_product
