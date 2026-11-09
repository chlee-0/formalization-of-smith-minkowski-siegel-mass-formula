import SMSFormula.BinaryStableNormImages
import SMSFormula.BinaryConductorEulerFactors

/-!
# Evaluated finite unit and norm-kernel counts for the original order

The rank-two scalar-power theorem applies directly to the original integral
quadratic algebra. Prime counts use its actual primitive discriminant D.
No maximal-order substitution or finite norm-one lifting is used.
-/

noncomputable section

namespace BinaryNormIdeal

/-- Exact unit lift count for any integral quadratic coefficient algebra. -/
theorem card_quadraticResidueUnits_power (A T : ℤ) (n k : ℕ)
    (hn : n≠0) (hk : k≠0) :
    Nat.card (QuadraticAlgebra (ZMod (n^k)) (A : ZMod (n^k)) (T : ZMod (n^k)))ˣ =
      Nat.card (QuadraticAlgebra (ZMod n) (A : ZMod n) (T : ZMod n))ˣ * n^(2*(k-1)) := by
  rw [← Nat.card_congr (Units.mapEquiv (quadraticResidueEquiv A T (n^k)).toMulEquiv).toEquiv,
    ← Nat.card_congr (Units.mapEquiv (quadraticResidueEquiv A T n).toMulEquiv).toEquiv]
  rw [Nat.cast_pow]
  exact card_scalarPowerQuotient_units (QuadraticAlgebra.basis A T) n k hn hk

/-- The original discriminant algebra has this exact lift factor, even
when it is nonmaximal or split. Modulus one remains included. -/
theorem card_discriminantAlgebraUnits_power (D : ℤ) (n k : ℕ)
    (hn : n≠0) (hk : k≠0) :
    Nat.card (DiscriminantAlgebra (ZMod (n^k)) D)ˣ =
      Nat.card (DiscriminantAlgebra (ZMod n) D)ˣ * n^(2*(k-1)) := by
  unfold DiscriminantAlgebra CoefficientAlgebra
  rw [Int.cast_one, neg_one_mul, ← Int.cast_neg,
    Int.cast_one, neg_one_mul, ← Int.cast_neg]
  exact card_quadraticResidueUnits_power (-(((D%2)^2-D)/4)) (D%2) n k hn hk

/-- The defining coefficients have the exact displayed discriminant. -/
theorem discriminantAlgebra_parameter_discriminant (D : ℤ) (hD : D%4=0 ∨ D%4=1) :
    (D%2)^2+4*(-(((D%2)^2-D)/4))=D := by
  linear_combination discriminantOrder_coefficients D hD

/-- Every prime residue unit count, with the original primitive discriminant. -/
theorem card_discriminantAlgebraUnits_prime (p : ℕ) [Fact p.Prime]
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) :
    (Nat.card (DiscriminantAlgebra (ZMod p) D)ˣ : ℤ)=
      ((p : ℤ)-1)*((p : ℤ)-conductorPrimeSign D p) := by
  have hd := discriminantAlgebra_parameter_discriminant D hD
  by_cases hp : p=2
  · subst p
    have h : (Nat.card (QuadraticAlgebra (ZMod 2)
        ((-(((D%2)^2-D)/4) : ℤ) : ZMod 2) ((D%2 : ℤ) : ZMod 2))ˣ : ℤ)=
        2-ZMod.χ₈ (((D%2)^2+4*(-(((D%2)^2-D)/4)) : ℤ) : ZMod 8) := by
      calc
        _=(if ((D%2 : ℤ) : ZMod 2)=0 then (2 : ℤ) else
            if ((-(((D%2)^2-D)/4) : ℤ) : ZMod 2)=0 then 1 else 3) := by
          rw [card_quadraticUnits_mod_two]
          split_ifs <;> rfl
        _=_ := dyadic_parity_count_eq_chi_eight _ _
    rw [hd] at h
    unfold DiscriminantAlgebra CoefficientAlgebra
    rw [Int.cast_one,neg_one_mul,← Int.cast_neg]
    simpa only [conductorPrimeSign_eq,if_pos rfl,Nat.cast_ofNat,Int.reduceSub,one_mul] using h
  · have h := card_quadraticUnits_odd p hp (-(((D%2)^2-D)/4)) (D%2)
    rw [hd] at h
    unfold DiscriminantAlgebra CoefficientAlgebra
    rw [Int.cast_one,neg_one_mul,← Int.cast_neg]
    simpa only [conductorPrimeSign_eq,if_neg hp] using h

/-- Evaluated finite order-unit count at every positive prime-power depth. -/
theorem card_discriminantAlgebraUnits_prime_power (p : ℕ) [Fact p.Prime]
    (k : ℕ) (hk : 0<k) (D : ℤ) (hD : D%4=0 ∨ D%4=1) :
    (Nat.card (DiscriminantAlgebra (ZMod (p^k)) D)ˣ : ℤ)=
      ((p : ℤ)-1)*((p : ℤ)-conductorPrimeSign D p)*(p : ℤ)^(2*(k-1)) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (card_discriminantAlgebraUnits_power D p k
    (Fact.out : p.Prime).ne_zero (Nat.ne_of_gt hk))
  push_cast at h
  rw [card_discriminantAlgebraUnits_prime p D hD] at h
  exact h

/-- Evaluated norm-one kernel count at every stable depth, keeping the
Actual p-adic norm index and the original finite norm kernel. -/
theorem card_orderUnitNorm_ker_prime_power (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 0<k) (hk2 : p=2 → 3≤k) (D : ℤ) (hD : D%4=0 ∨ D%4=1) :
    (Nat.card (orderUnitNorm (ZMod (p^k)) D).ker : ℤ)=
      (Nat.card (OrderUnitNormQuotient ℤ_[p] D) : ℤ)*
        ((p : ℤ)-conductorPrimeSign D p)*(p : ℤ)^(k-1) := by
  have h := congrArg (fun n : ℕ => (n : ℤ))
    (card_orderUnitNorm_ker_pow_mul_primeUnits p k hk hk2 D)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub (Fact.out : p.Prime).one_le,Nat.cast_one] at h
  rw [card_discriminantAlgebraUnits_prime_power p k hk D hD] at h
  have hpow : (p : ℤ)^(2*(k-1))=(p : ℤ)^(k-1)*(p : ℤ)^(k-1) := by
    rw [Nat.mul_comm 2,pow_mul,pow_two]
  rw [hpow] at h
  have hp : (1 : ℤ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hn : ((p : ℤ)-1)*(p : ℤ)^(k-1)≠0 :=
    mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  apply mul_right_cancel₀ hn
  linear_combination h

private theorem chi_eight_mul_square (i d : ZMod 8) :
    ZMod.χ₈ (i^2*d) =
      if (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) i = 0 then 0 else ZMod.χ₈ d := by
  decide +revert

/-- Multiplication by an integer square removes precisely its prime factors
from the numerical order-discriminant sign. This is not the product character. -/
theorem conductorPrimeSign_mul_nat_sq (d : ℤ) (I p : ℕ) [Fact p.Prime] :
    conductorPrimeSign ((I : ℤ)^2*d) p =
      if p ∣ I then 0 else conductorPrimeSign d p := by
  rw [conductorPrimeSign_eq, conductorPrimeSign_eq]
  by_cases hp : p = 2
  · subst p
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      map_natCast, ZMod.natCast_eq_zero_iff] using chi_eight_mul_square (I : ZMod 8) (d : ZMod 8)
  · simp only [if_neg hp]
    rw [legendreSym.mul]
    by_cases hI : p ∣ I
    · rw [if_pos hI]
      have hz : legendreSym p ((I : ℤ)^2) = 0 := by
        rw [legendreSym.eq_zero_iff]
        simp only [Int.cast_pow, Int.cast_natCast,
          (ZMod.natCast_eq_zero_iff I p).mpr hI]
        norm_num
      rw [hz, zero_mul]
    · have hI' : ((I : ℤ) : ZMod p) ≠ 0 := by
        rw [Int.cast_natCast]
        exact mt (ZMod.natCast_eq_zero_iff I p).mp hI
      rw [if_neg hI, legendreSym.sq_one' p hI', one_mul]

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The original order sign is the same field sign with exactly the actual
conductor primes removed. Original content does not enter this identity. -/
theorem binaryPrimitivePrimeSign_eq_masked_fieldSign (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    conductorPrimeSign K.binaryPrimitiveDiscriminant p =
      if p ∣ K.binaryOrderIndex then 0 else conductorPrimeSign
        (NumberField.discr (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  calc
    _ = conductorPrimeSign ((K.binaryOrderIndex : ℤ)^2 * NumberField.discr
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p :=
      congrArg (fun D : ℤ => conductorPrimeSign D p)
        K.binaryPrimitiveDiscriminant_eq_orderIndex_sq_mul_fieldDiscr
    _ = _ := conductorPrimeSign_mul_nat_sq _ _ _

/-- All finite original order units, evaluated with the actual conductor
and the same field. The formula holds at every positive depth. -/
theorem card_binaryOrderUnits_prime_power (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0 < k) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    (Nat.card (DiscriminantAlgebra (ZMod (p^k)) K.binaryPrimitiveDiscriminant)ˣ : ℚ) =
      (p : ℚ)^(2*k)*(1-1/(p : ℚ))*
        (if p ∣ K.binaryOrderIndex then 1 else 1-
          (conductorPrimeSign (NumberField.discr
            (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℚ)/(p : ℚ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  have h : (Nat.card (DiscriminantAlgebra (ZMod (p^k)) K.binaryPrimitiveDiscriminant)ˣ : ℚ) =
      ((p : ℚ)-1)*((p : ℚ)-(conductorPrimeSign K.binaryPrimitiveDiscriminant p : ℚ))*
        (p : ℚ)^(2*(k-1)) := by
    exact_mod_cast card_discriminantAlgebraUnits_prime_power p k hk
      K.binaryPrimitiveDiscriminant K.binaryPrimitiveDiscriminant_mod_four
  rw [K.binaryPrimitivePrimeSign_eq_masked_fieldSign p] at h
  rw [h]
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : 2*k = 2*(k-1)+2 := by omega
  have hpow : (p : ℚ)^(2*k) = (p : ℚ)^(2*(k-1))*(p : ℚ)^2 := by
    rw [he, pow_add]
  rw [hpow]
  by_cases hI : p ∣ K.binaryOrderIndex
  · simp only [if_pos hI, Int.cast_zero, sub_zero]
    field_simp [hp]
  · simp only [if_neg hI]
    field_simp [hp]

/-- The literal finite norm-one kernel at every stable depth has the
evaluated original-order count. Its local index is the actual p-adic quotient. -/
theorem card_binaryOrderNormKernel_prime_power (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0 < k) (hk2 : p=2 → 3≤k) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    (Nat.card (orderUnitNorm (ZMod (p^k)) K.binaryPrimitiveDiscriminant).ker : ℚ) =
      (Nat.card (OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant) : ℚ)*(p : ℚ)^k*
        (if p ∣ K.binaryOrderIndex then 1 else 1-
          (conductorPrimeSign (NumberField.discr
            (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℚ)/(p : ℚ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  have h : (Nat.card (orderUnitNorm (ZMod (p^k)) K.binaryPrimitiveDiscriminant).ker : ℚ) =
      (Nat.card (OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant) : ℚ)*
        ((p : ℚ)-(conductorPrimeSign K.binaryPrimitiveDiscriminant p : ℚ))*(p : ℚ)^(k-1) := by
    exact_mod_cast card_orderUnitNorm_ker_prime_power p k hk hk2
      K.binaryPrimitiveDiscriminant K.binaryPrimitiveDiscriminant_mod_four
  rw [K.binaryPrimitivePrimeSign_eq_masked_fieldSign p] at h
  rw [h]
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : k = (k-1)+1 := by omega
  conv_rhs => rw [he, pow_add, pow_one]
  by_cases hI : p ∣ K.binaryOrderIndex
  · simp only [if_pos hI, Int.cast_zero, sub_zero]
    ring
  · simp only [if_neg hI]
    field_simp [hp]

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.card_quadraticResidueUnits_power
#assert_standard_axioms BinaryNormIdeal.card_discriminantAlgebraUnits_power
#assert_standard_axioms BinaryNormIdeal.discriminantAlgebra_parameter_discriminant
#assert_standard_axioms BinaryNormIdeal.card_discriminantAlgebraUnits_prime
#assert_standard_axioms BinaryNormIdeal.card_discriminantAlgebraUnits_prime_power
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNorm_ker_prime_power
#assert_standard_axioms BinaryNormIdeal.conductorPrimeSign_mul_nat_sq
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePrimeSign_eq_masked_fieldSign
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryOrderUnits_prime_power
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryOrderNormKernel_prime_power
